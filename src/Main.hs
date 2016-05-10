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

import KZC.Analysis.Occ
import KZC.Analysis.RefFlow
import KZC.Analysis.NeedDefault
import KZC.Cg
import KZC.Check
import qualified KZC.Core.Label as C
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import KZC.Error
import qualified KZC.Expr.Lint as E
import qualified KZC.Expr.Syntax as E
import KZC.Flags
import KZC.Label
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
import KZC.Transform.Auto
import KZC.Transform.LambdaLift

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
runPipeline filepath =
    void $ runMaybeT $ pipeline filepath
  where
    ext :: String
    ext = drop 1 (takeExtension filepath)

    start :: Pos
    start = startPos filepath

    pipeline :: FilePath -> MaybeT KZC ()
    pipeline =
        inputPhase >=>
        cppPhase >=>
        parsePhase >=>
        pprPhase >=>
        stopIf (testDynFlag StopAfterParse) >=>
        tracePhase "rename" renamePhase >=>
        tracePhase "typecheck" checkPhase >=> tracePhase "lint" lintCore >=>
        stopIf (testDynFlag StopAfterCheck) >=>
        tracePhase "lambdaLift" lambdaLiftPhase >=> tracePhase "lint" lintCore >=>
        tracePhase "auto" autoPhase >=> tracePhase "lintAuto" lintAuto >=>
        -- Simplify, but don't inline functions or computations
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ onlyInliningValues $ iterateSimplPhase "-phase1") >=>
        -- AutoLUT
        runIf (testDynFlag AutoLUT) (tracePhase "autolut-phase1" autolutPhase >=> tracePhase "lintAuto" lintAuto) >=>
        -- Simplify again, allowing inlining. This may inline LUTted functions.
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase2") >=>
        -- Fuse pars
        runIf (testDynFlag Fuse) (tracePhase "fusion" fusionPhase >=> tracePhase "lintAuto" lintAuto) >=>
        -- Partially evaluate and simplify
        runIf runEval (tracePhase "eval-phase1" evalPhase >=> tracePhase "lintAuto" lintAuto) >=>
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase3") >=>
        -- Auto-LUT, partially evaluate, and simplify once more
        runIf (testDynFlag AutoLUT) (tracePhase "autolut-phase2" autolutPhase >=> tracePhase "lintAuto" lintAuto) >=>
        runIf runEval (tracePhase "eval-phase2" evalPhase >=> tracePhase "lintAuto" lintAuto) >=>
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase4") >=>
        -- Clean up the code, do some analysis, and codegen
        tracePhase "hashcons" hashconsPhase >=> tracePhase "lintAuto" lintAuto >=>
        tracePhase "refFlow" refFlowPhase >=>
        tracePhase "needDefault" needDefaultPhase >=>
        dumpFinal >=>
        tracePhase "compile" compilePhase

    runEval :: Flags -> Bool
    runEval flags = testDynFlag PartialEval flags || testDynFlag LUT flags

    tracePhase :: String
               -> (a -> MaybeT KZC b)
               -> a
               -> MaybeT KZC b
    tracePhase phase act x = do
        doTrace <- asksFlags (testTraceFlag TracePhase)
        if doTrace
          then do pass  <- lift getPass
                  return $! unsafePerformIO $ hPutStr stderr (printf "Phase: %s.%02d\n" phase pass)
                  start <- liftIO getCPUTime
                  y     <- act x
                  end   <- liftIO getCPUTime
                  let t :: Double
                      t = fromIntegral (end - start) / 1e12
                  return $! unsafePerformIO $ hPutStr stderr (printf "Phase: %s.%02d (%f)\n" phase pass t)
                  return y
          else act x

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
        dumpPass DumpCore "core" "tc"

    lambdaLiftPhase :: [E.Decl] -> MaybeT KZC [E.Decl]
    lambdaLiftPhase =
        lift . runLift . liftProgram >=>
        dumpPass DumpLift "core" "ll"

    autoPhase :: IsLabel l => [E.Decl] -> MaybeT KZC (C.Program l)
    autoPhase =
        lift . C.withTc . runAuto . autoProgram >=>
        dumpPass DumpLift "acore" "auto"

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
            prog'           <- occPhase prog >>= lintAuto
            (prog'', stats) <- simplPhase prog'
            void $ lintAuto prog'
            if stats /= mempty
              then do void $ dumpPass DumpOcc "acore" ("occ" ++ desc) prog'
                      void $ dumpPass DumpSimpl "acore" ("simpl" ++ desc) prog''
                      go (i+1) n prog''
              else return prog

    hashconsPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    hashconsPhase =
        lift . C.withTc . runHCM . hashConsConsts >=>
        dumpPass DumpHashCons "acore" "hashcons"

    fusionPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    fusionPhase =
        lift . C.withTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "acore" "fusion"

    autolutPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    autolutPhase =
        lift . C.withTc . runAutoM . autolutProgram >=>
        dumpPass DumpAutoLUT "acore" "autolut"

    evalPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    evalPhase =
        lift . C.withTc . evalEvalM . evalProgram >=>
        dumpPass DumpEval "acore" "peval"

    refFlowPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    refFlowPhase =
        lift . C.liftTc . runRF . rfProgram >=>
        dumpPass DumpEval "acore" "rflow"

    needDefaultPhase :: IsLabel l => C.Program l -> MaybeT KZC (C.Program l)
    needDefaultPhase =
        lift . C.liftTc . runND . needDefaultProgram >=>
        dumpPass DumpEval "acore" "needdefault"

    compilePhase :: C.LProgram -> MaybeT KZC ()
    compilePhase =
        lift . evalCg . compileProgram >=>
        lift . writeOutput

    lintCore :: [E.Decl] -> MaybeT KZC [E.Decl]
    lintCore decls = lift $ do
        whenDynFlag Lint $
            E.withTc (E.checkDecls decls)
        return decls

    lintAuto :: IsLabel l
             => C.Program l
             -> MaybeT KZC (C.Program l)
    lintAuto p = lift $ do
        whenDynFlag AutoLint $
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
    dumpFinal = dumpPass DumpAuto "acore" "final"

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
