{-# LANGUAGE CPP #-}

-- |
-- Module      : KZC.Driver
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Driver (
    defaultMainWith,
    defaultMain,

    parseKzcOpts,
    kzcUsage
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Lazy as B
import Data.Loc
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E
import System.CPUTime (getCPUTime)
import System.Directory (createDirectoryIfMissing)
import System.Environment
import System.Exit (exitFailure)
import System.FilePath (replaceExtension,
                        takeDirectory,
                        takeExtension)
import System.IO (IOMode(..),
                  hClose,
                  hPrint,
                  hPutStr,
                  hPutStrLn,
                  openFile,
                  stderr)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland
import Text.Printf (printf)

import Language.Ziria.Parser
import qualified Language.Ziria.Syntax as Z

import KZC.Analysis.NeedDefault
import KZC.Analysis.Occ
import KZC.Analysis.Rate
import KZC.Analysis.RefFlow
import KZC.Backend.C
import KZC.Check
import KZC.Config
import qualified KZC.Core.Label as C
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import KZC.Driver.Opts
import qualified KZC.Expr.Lint as E
import qualified KZC.Expr.Syntax as E
import qualified KZC.Expr.ToCore as E
import KZC.Label
import KZC.LambdaLift
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Optimize.Autolut
import KZC.Optimize.Coalesce
import KZC.Optimize.Eval
import KZC.Optimize.FloatViews
import KZC.Optimize.Fuse
import KZC.Optimize.HashConsConsts
import KZC.Optimize.LowerGenerators
import KZC.Optimize.LowerViews
import KZC.Optimize.LutToGen
import KZC.Optimize.Simplify
import KZC.Rename
import KZC.Util.Error
import KZC.Util.SysTools

defaultMain :: IO ()
defaultMain = do
    args          <- getArgs
    (conf, files) <- parseKzcOpts args
    if mode conf == Help
      then kzcUsage >>= hPutStrLn stderr
      else defaultMainWith conf files

defaultMainWith :: Config -> [FilePath] -> IO ()
defaultMainWith conf files =
    evalKZC conf (mapM_ runPipeline files) `catch` printFailure
  where
    printFailure :: SomeException -> IO ()
    printFailure e = hPrint stderr e >> exitFailure

runPipeline :: FilePath -> KZC ()
runPipeline filepath = do
    start <- liftIO getCPUTime
    void $ runMaybeT $ pipeline start filepath
  where
    ext :: String
    ext = drop 1 (takeExtension filepath)

    start :: Pos
    start = startPos filepath

    pipeline :: Integer -> FilePath -> MaybeT KZC ()
    pipeline start =
        inputPhase >=>
        cppPhase >=>
        parsePhase >=>
        pprPhase >=>
        stopIf (testDynFlag StopAfterParse) >=>
        tracePhase "rename" renamePhase >=>
        traceExprPhase "typecheck" checkPhase >=>
        stopIf (testDynFlag StopAfterCheck) >=>
        traceExprPhase "lambdaLift" lambdaLiftPhase >=>
        traceCorePhase "exprToCore" exprToCorePhase >=>
        -- Simplify
        runIf (testDynFlag Simplify) (iterateSimplPhase "-phase1") >=>
        -- Perform rate analysis
        traceCorePhase "rate" ratePhase >=>
        -- Perform pipeline coalescing
        runIf (testDynFlag Coalesce) (traceCorePhase "coalesce" coalescePhase) >=>
        -- Fuse pars
        runIf (testDynFlag Fuse) (traceCorePhase "fusion" fusionPhase) >=>
        -- Partially evaluate and simplify
        runIf (testDynFlag PartialEval) (traceCorePhase "eval" evalPhase) >=>
        runIf (testDynFlag Simplify) (iterateSimplPhase "-phase2") >=>
        -- Float views out for auto-LUTting
        runIf (testDynFlag FloatViews) (traceCorePhase "float-views" floatViewsPhase) >=>
        -- Auto-LUT, convert LUTs to generators
        runIf (testDynFlag AutoLUT) (traceCorePhase "autolut" autolutPhase) >=>
        runIf (testDynFlag LUT)     (traceCorePhase "lutToGen" lutToGenPhase) >=>
        -- Lower views so we don't have to deal with them anymore
        runIf (testDynFlag FloatViews) (traceCorePhase "lower-views" lowerViewsPhase) >=>
        -- Lower generators
        runIf (testDynFlag LowerGen) (traceCorePhase "lowerGen" lowerGenPhase) >=>
        -- One final round of simplification
        runIf (testDynFlag Simplify) (iterateSimplPhase "-phase3") >=>
        -- Clean up the code, do some analysis, and codegen
        traceCorePhase "hashcons" hashconsPhase >=>
        tracePhase "refFlow" refFlowPhase >=>
        tracePhase "needDefault" needDefaultPhase >=>
        dumpFinal >=>
        tracePhase "compile" compilePhase
      where
        traceExprPhase :: String
                       -> (a -> MaybeT KZC [E.Decl])
                       -> a
                       -> MaybeT KZC [E.Decl]
        traceExprPhase phase act =
            tracePhase phase act >=> tracePhase "lint" lintExpr

        traceCorePhase :: IsLabel l
                       => String
                       -> (a -> MaybeT KZC (C.Program l))
                       -> a
                       -> MaybeT KZC (C.Program l)
        traceCorePhase phase act =
            tracePhase phase act >=> tracePhase "lint" lintCore

        tracePhase :: String
                   -> (a -> MaybeT KZC b)
                   -> a
                   -> MaybeT KZC b
        tracePhase phase act x = do
            doTrace <- asksConfig (testTraceFlag TracePhase)
            if doTrace
              then do pass       <- lift getPass
                      phaseStart <- liftIO getCPUTime
                      let t1 :: Double
                          t1 = fromIntegral (phaseStart - start) / 1e12
                      return $! unsafePerformIO $ hPutStr stderr (printf "Phase: %s.%02d (%f)\n" phase pass t1)
                      y        <- act x
                      phaseEnd <- liftIO getCPUTime
                      let t2 :: Double
                          t2 = fromIntegral (phaseEnd - phaseStart) / 1e12
                      return $! unsafePerformIO $ hPutStr stderr (printf "Phase: %s.%02d (%f elapsed)\n" phase pass t2)
                      return y
              else act x

        iterateSimplPhase :: IsLabel l => String -> C.Program l -> MaybeT KZC (C.Program l)
        iterateSimplPhase desc prog0 = do
            n <- asksConfig maxSimpl
            go 0 n prog0
          where
            go :: IsLabel l => Int -> Int -> C.Program l -> MaybeT KZC (C.Program l)
            go i n prog | i >= n = do
                warndocWhen WarnSimplifierBailout $ text "Simplifier bailing out after" <+> ppr n <+> text "iterations"
                return prog

            go i n prog = do
                prog' <- tracePhase "occ" occPhase prog
                void $ dumpPass DumpOcc "core" ("occ" ++ desc) prog'
                (prog'', stats) <- tracePhase "simpl" simplPhase prog'
                if stats /= mempty
                  then do void $ dumpPass DumpSimpl "core" ("simpl" ++ desc) prog''
                          void $ lintCore prog''
                          go (i+1) n prog''
                  else return prog

    inputPhase :: FilePath -> MaybeT KZC T.Text
    inputPhase filepath = liftIO $ E.decodeUtf8 <$> B.readFile filepath

    cppPhase :: T.Text -> MaybeT KZC T.Text
    cppPhase = lift . runCpp filepath >=> dumpPass DumpCPP ext "pp"

    parsePhase :: T.Text -> MaybeT KZC [Z.CompLet]
    parsePhase text = lift $ liftIO $ parseProgram text start

    pprPhase :: [Z.CompLet] -> MaybeT KZC [Z.CompLet]
    pprPhase decls = do
        whenDynFlag PrettyPrint $
            liftIO $ putDocLn $ ppr decls
        return decls

    renamePhase :: [Z.CompLet] -> MaybeT KZC [Z.CompLet]
    renamePhase =
        lift . runRn . renameProgram >=>
        dumpPass DumpRename "zr" "rn"

    checkPhase :: [Z.CompLet] -> MaybeT KZC [E.Decl]
    checkPhase =
        lift . withTi . checkProgram >=>
        dumpPass DumpCore "expr" "tc"

    lambdaLiftPhase :: [E.Decl] -> MaybeT KZC [E.Decl]
    lambdaLiftPhase =
        lift . C.withTc . runLift . liftProgram >=>
        dumpPass DumpLift "expr" "ll"

    exprToCorePhase :: IsLabel l => [E.Decl] -> MaybeT KZC (C.Program l)
    exprToCorePhase =
        lift . C.withTc . E.runTC . E.exprToCore >=>
        dumpPass DumpLift "core" "exprToCore"

    occPhase :: C.Program l -> MaybeT KZC (C.Program l)
    occPhase =
        lift . C.withTc . occProgram

    simplPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l, SimplStats)
    simplPhase =
        lift . C.withTc . simplProgram

    hashconsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    hashconsPhase =
        lift . C.withTc . hashConsConsts >=>
        dumpPass DumpHashCons "core" "hashcons"

    ratePhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    ratePhase =
        lift . C.withTc . rateProgram >=>
        dumpPass DumpRate "core" "rate"

    coalescePhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    coalescePhase =
        lift . C.withTc . coalesceProgram >=>
        dumpPass DumpCoalesce "core" "coalesce"

    fusionPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    fusionPhase =
        lift . C.withTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "core" "fusion"

    floatViewsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    floatViewsPhase =
        lift . C.withTc . floatViews >=>
        dumpPass DumpViews "core" "float-views"

    lowerViewsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    lowerViewsPhase =
        lift . C.withTc . lowerViews >=>
        dumpPass DumpViews "core" "lower-views"

    autolutPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    autolutPhase =
        lift . C.withTc . autolutProgram >=>
        dumpPass DumpAutoLUT "core" "autolut"

    lutToGenPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    lutToGenPhase =
        lift . C.withTc . lutToGen >=>
        dumpPass DumpLUT "core" "lutToGen"

    lowerGenPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    lowerGenPhase =
        lift . C.withTc . lowerGenerators >=>
        dumpPass DumpLUT "core" "lowerGen"

    evalPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    evalPhase =
        lift . C.withTc . evalProgram >=>
        dumpPass DumpEval "core" "peval"

    refFlowPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    refFlowPhase =
        lift . C.liftTc . rfProgram >=>
        dumpPass DumpEval "core" "rflow"

    needDefaultPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    needDefaultPhase =
        lift . C.liftTc . needDefaultProgram >=>
        dumpPass DumpEval "core" "needdefault"

    compilePhase :: C.LProgram -> MaybeT KZC ()
    compilePhase =
        lift . evalCg . compileProgram >=>
        lift . writeOutput

    lintExpr :: [E.Decl] -> MaybeT KZC [E.Decl]
    lintExpr decls = lift $ do
        whenDynFlag Lint $
            E.withTc (E.checkDecls decls)
        return decls

    lintCore :: IsLabel l
             => C.Program l
             -> MaybeT KZC (C.Program l)
    lintCore p = lift $ do
        whenDynFlag Lint $
            C.withTc (C.checkProgram p)
        return p

    stopIf :: (Config -> Bool) -> a -> MaybeT KZC a
    stopIf f x = do
        stop <- asksConfig f
        if stop then MaybeT (return Nothing) else return x

    runIf :: (Config -> Bool) -> (a -> MaybeT KZC a) -> a -> MaybeT KZC a
    runIf f g x = do
        run <- asksConfig f
        if run then g x else return x

    writeOutput :: Pretty a
                => a
                -> KZC ()
    writeOutput x = do
        let defaultOutpath = replaceExtension filepath ".c"
        outpath     <- asksConfig (fromMaybe defaultOutpath . output)
        linePragmas <- asksConfig (testDynFlag LinePragmas)
        let pprint | linePragmas = prettyPragmaLazyText 80 . ppr
                   | otherwise   = prettyLazyText 80 . ppr
        h <- liftIO $ openFile outpath WriteMode
        liftIO $ B.hPut h $ E.encodeUtf8 (pprint x)
        liftIO $ hClose h

    dumpFinal :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    dumpFinal = dumpPass DumpCore "core" "final"

    dumpPass :: Pretty a
             => DumpFlag
             -> String
             -> String
             -> a
             -> MaybeT KZC a
    dumpPass f ext suffix x = lift $ do
        pass <- incPass
        dump f filepath ext (printf "%02d-%s" pass suffix) (ppr x)
        return x

    dump :: DumpFlag
         -> FilePath
         -> String
         -> String
         -> Doc
         -> KZC ()
    dump f sourcePath ext suffix doc = whenDumpFlag f $ do
        let destpath = replaceExtension sourcePath ext'
        liftIO $ createDirectoryIfMissing True (takeDirectory destpath)
        h <- liftIO $ openFile destpath WriteMode
        liftIO $ B.hPut h $ E.encodeUtf8 (prettyLazyText 80 doc)
        liftIO $ hClose h
      where
        ext' :: String
        ext' | null suffix = "dump" ++ "." ++ ext
             | otherwise   = "dump"  ++ "-" ++ suffix ++ "." ++ ext
