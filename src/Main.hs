-- |
-- Module      :  Main
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cdrexel.edu

module Main where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Lazy as B
import Data.Loc
import Data.Monoid
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
import qualified KZC.Auto.Lint as A
import qualified KZC.Auto.Syntax as A
import KZC.Cg
import KZC.Check
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Optimize.Eval
import KZC.Optimize.Fuse
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
    let fs'     =  flagImplications fs
    if mode fs == Help
      then usage >>= hPutStrLn stderr
      else evalKZC fs' (mapM_ runPipeline files) `catch` printFailure
  where
    printFailure :: SomeException -> IO ()
    printFailure e = (hPutStrLn stderr . show) e >> exitFailure

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
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase1") >=>
        runIf (testDynFlag Fuse) (tracePhase "fusion" fusionPhase >=> tracePhase "lintAuto" lintAuto) >=>
        runIf (testDynFlag PartialEval) (tracePhase "eval" evalPhase >=> tracePhase "lintAuto" lintAuto) >=>
        runIf (testDynFlag Simplify) (tracePhase "simpl" $ iterateSimplPhase "-phase2") >=>
        dumpFinal >=>
        tracePhase "compile" compilePhase

    tracePhase :: String
               -> (a -> MaybeT KZC b)
               -> a
               -> MaybeT KZC b
    tracePhase phase act x = do
        doTrace <- asksFlags (testTraceFlag TracePhase)
        if doTrace
          then do pass  <- lift getPass
                  return $! unsafePerformIO $ hPutStr stderr (printf "Phase: %s.%02d" phase pass)
                  start <- liftIO getCPUTime
                  y     <- act x
                  end   <- liftIO getCPUTime
                  let t :: Double
                      t = fromIntegral (end - start) / 1e12
                  return $! unsafePerformIO $ hPutStr stderr (printf "(%f)\n" t)
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

    checkPhase :: [Z.CompLet] -> MaybeT KZC [C.Decl]
    checkPhase =
        lift . withTi . checkProgram >=>
        dumpPass DumpCore "core" "tc"

    lambdaLiftPhase :: [C.Decl] -> MaybeT KZC [C.Decl]
    lambdaLiftPhase =
        lift . runLift . liftProgram >=>
        dumpPass DumpLift "core" "ll"

    autoPhase :: [C.Decl] -> MaybeT KZC A.LProgram
    autoPhase =
        lift . A.withTcEnv . runAuto . autoProgram >=>
        dumpPass DumpLift "acore" "auto"

    occPhase :: A.LProgram -> MaybeT KZC A.LProgram
    occPhase =
        lift . A.withTcEnv . runOccM . occProgram

    simplPhase :: A.LProgram -> MaybeT KZC (A.LProgram, SimplStats)
    simplPhase =
        lift . A.withTcEnv . runSimplM . simplProgram

    iterateSimplPhase :: String -> A.LProgram -> MaybeT KZC A.LProgram
    iterateSimplPhase desc prog0 = do
        n <- asksFlags maxSimpl
        go 0 n prog0
      where
        go :: Int -> Int -> A.LProgram -> MaybeT KZC A.LProgram
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

    fusionPhase :: A.LProgram -> MaybeT KZC A.LProgram
    fusionPhase =
        lift . A.withTcEnv . A.runTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "acore" "fusion"

    evalPhase :: A.LProgram -> MaybeT KZC A.LProgram
    evalPhase =
        lift . A.withTcEnv . evalEvalM . evalProgram >=>
        dumpPass DumpEval "acore" "peval"

    compilePhase :: A.LProgram -> MaybeT KZC ()
    compilePhase =
        lift . evalCg . compileProgram >=>
        lift . writeOutput

    lintCore :: [C.Decl] -> MaybeT KZC [C.Decl]
    lintCore decls = lift $ do
        whenDynFlag Lint $
            C.withTcEnv (C.runTc (C.checkDecls decls))
        return decls

    lintAuto :: IsLabel l
             => A.Program l
             -> MaybeT KZC (A.Program l)
    lintAuto p = lift $ do
        whenDynFlag AutoLint $
            A.withTcEnv (A.runTc (A.checkProgram p))
        return p

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
        outpath     <- asksFlags (maybe defaultOutpath id . output)
        linePragmas <- asksFlags (testDynFlag LinePragmas)
        let pprint | linePragmas = prettyPragmaLazyText 80 . ppr
                   | otherwise   = prettyLazyText 80 . ppr
        h <- liftIO $ openFile outpath WriteMode
        liftIO $ B.hPut h $ E.encodeUtf8 (pprint x)
        liftIO $ hClose h

    dumpFinal :: A.LProgram -> MaybeT KZC A.LProgram
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
