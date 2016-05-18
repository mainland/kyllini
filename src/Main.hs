{-# LANGUAGE CPP #-}

-- |
-- Module      :  Main
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cdrexel.edu

module Main where

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
import KZC.Analysis.RefFlow
import KZC.Analysis.StaticRef
import KZC.Cg
import KZC.Check
import qualified KZC.Core.Label as C
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import KZC.Error
import qualified KZC.Expr.Lint as E
import qualified KZC.Expr.Syntax as E
import qualified KZC.Expr.ToCore as E
import KZC.Flags
import KZC.Label
import KZC.LambdaLift
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Optimize.Autolut (runAutoM,
                             autolutProgram)
import KZC.Optimize.Eval
import KZC.Optimize.Fuse
import KZC.Optimize.HashConsConsts
import KZC.Optimize.Simplify
import KZC.Rename
import KZC.SysTools

import Opts

main :: IO ()
main = do
    args        <- getArgs
    (fs, files) <- compilerOpts args
    if mode fs == Help
      then usage >>= hPutStrLn stderr
      else evalKZC fs (mapM_ runPipeline files) `catch` printFailure
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
        -- Simplify, but don't inline functions or computations
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ onlyInliningValues $ iterateSimplPhase "-phase1") >=>
        -- AutoLUT
        runIf (testDynFlag AutoLUT) (traceCorePhase "autolut-phase1" autolutPhase) >=>
        -- Simplify again, allowing inlining. This may inline LUTted functions.
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase2") >=>
        -- Fuse pars
        runIf (testDynFlag Fuse) (traceCorePhase "fusion" fusionPhase) >=>
        -- Partially evaluate and simplify
        runIf runEval (traceCorePhase "eval-phase1" evalPhase) >=>
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase3") >=>
        -- Auto-LUT, partially evaluate, and simplify once more
        runIf (testDynFlag AutoLUT) (traceCorePhase "autolut-phase2" autolutPhase) >=>
        runIf runEval (tracePhase "eval-phase2" evalPhase >=> tracePhase "lintCore" lintCore) >=>
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase4") >=>
        -- Look for refs that are unchanged
        runIf (testDynFlag Simplify) (tracePhase "staticRef" staticRefsPhase) >=>
        -- One final round of simplification
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase5") >=>
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
            doTrace <- asksFlags (testTraceFlag TracePhase)
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

    runEval :: Flags -> Bool
    runEval flags = testDynFlag PartialEval flags || testDynFlag LUT flags

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
        lift . C.withTc . runOccM . occProgram

    simplPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l, SimplStats)
    simplPhase =
        lift . C.withTc . runSimplM . simplProgram

    iterateSimplPhase :: IsLabel l => String -> C.Program l -> MaybeT KZC (C.Program l)
    iterateSimplPhase desc prog0 = do
        n <- asksFlags maxSimpl
        go 0 n prog0
      where
        go :: IsLabel l => Int -> Int -> C.Program l -> MaybeT KZC (C.Program l)
        go i n prog | i >= n = do
            warndoc $ text "Simplifier bailing out after" <+> ppr n <+> text "iterations"
            return prog

        go i n prog = do
            prog'           <- occPhase prog >>= lintCore
            (prog'', stats) <- simplPhase prog'
            void $ lintCore prog'
            if stats /= mempty
              then do void $ dumpPass DumpOcc "core" ("occ" ++ desc) prog'
                      void $ dumpPass DumpSimpl "core" ("simpl" ++ desc) prog''
                      go (i+1) n prog''
              else return prog

    staticRefsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    staticRefsPhase =
        lift . C.withTc . runSR . staticRefsProgram >=>
        dumpPass DumpStaticRefs "core" "staticrefs"

    hashconsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    hashconsPhase =
        lift . C.withTc . runHCM . hashConsConsts >=>
        dumpPass DumpHashCons "core" "hashcons"

    fusionPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    fusionPhase =
        lift . C.withTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "core" "fusion"

    autolutPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    autolutPhase =
        lift . C.withTc . runAutoM . autolutProgram >=>
        dumpPass DumpAutoLUT "core" "autolut"

    evalPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    evalPhase =
        lift . C.withTc . evalEvalM . evalProgram >=>
        dumpPass DumpEval "core" "peval"

    refFlowPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    refFlowPhase =
        lift . C.liftTc . runRF . rfProgram >=>
        dumpPass DumpEval "core" "rflow"

    needDefaultPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    needDefaultPhase =
        lift . C.liftTc . runND . needDefaultProgram >=>
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

    onlyInliningValues :: (a -> MaybeT KZC a) -> a -> MaybeT KZC a
    onlyInliningValues k x =
        localFlags (unsetDynFlag MayInlineFun .
                    unsetDynFlag MayInlineComp .
                    unsetDynFlag AlwaysInlineComp) $
        k x

    stopIf :: (Flags -> Bool) -> a -> MaybeT KZC a
    stopIf f x = do
        stop <- asksFlags f
        if stop then MaybeT (return Nothing) else return x

    runIf :: (Flags -> Bool) -> (a -> MaybeT KZC a) -> a -> MaybeT KZC a
    runIf f g x = do
        run <- asksFlags f
        if run then g x else return x

    writeOutput :: Pretty a
                => a
                -> KZC ()
    writeOutput x = do
        let defaultOutpath = replaceExtension filepath ".c"
        outpath     <- asksFlags (fromMaybe defaultOutpath . output)
        linePragmas <- asksFlags (testDynFlag LinePragmas)
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
