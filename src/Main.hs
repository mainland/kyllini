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
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E
import System.Directory (createDirectoryIfMissing)
import System.Environment
import System.Exit (exitFailure)
import System.FilePath (replaceExtension,
                        takeDirectory,
                        takeExtension)
import System.IO (IOMode(..),
                  hClose,
                  hPutStrLn,
                  openFile,
                  stderr)
import Text.PrettyPrint.Mainland

import Language.Ziria.Parser
import qualified Language.Ziria.Syntax as Z

import KZC.Analysis.Occ
import qualified KZC.Auto.Lint as A
import qualified KZC.Auto.Syntax as A
import KZC.Cg
import KZC.Check
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Optimize.Flatten
import KZC.Optimize.Fuse
import KZC.Optimize.Simplify
import KZC.Rename
import KZC.SysTools
import KZC.Transform.Auto
import KZC.Transform.LambdaLift

import Opts

main :: IO ()
main = do
    args <- getArgs
    (fs, files) <- compilerOpts args
    if mode fs == Help
      then usage >>= hPutStrLn stderr
      else evalKZC fs (mapM_ runPipeline files) `catch` printFailure
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
        renamePhase >=>
        checkPhase >=> lintCore >=>
        stopIf (testDynFlag StopAfterCheck) >=>
        lambdaLiftPhase >=> lintCore >=>
        autoPhase >=> lintAuto >=>
        runIf (testDynFlag Flatten) (flattenPhase >=> lintAuto) >=>
        runIf (testDynFlag Fuse) (fusionPhase >=> lintAuto) >=>
        occPhase >=> lintAuto >=>
        runIf (testDynFlag Simplify) (simplPhase >=> lintAuto) >=>
        compilePhase

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
        lift . A.withTcEnv . runOccM . occProgram >=>
        dumpPass DumpOcc "acore" "occ"

    simplPhase :: A.LProgram -> MaybeT KZC A.LProgram
    simplPhase =
        lift . A.withTcEnv . runSimplM . simplProgram >=>
        dumpPass DumpSimpl "acore" "simpl"

    flattenPhase :: A.LProgram -> MaybeT KZC A.LProgram
    flattenPhase =
        lift . A.withTcEnv . evalFl . flattenProgram >=>
        dumpPass DumpFlatten "acore" "flatten"

    fusionPhase :: A.LProgram -> MaybeT KZC A.LProgram
    fusionPhase =
        lift . A.withTcEnv . A.runTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "acore" "fusion"

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

    dumpPass :: Pretty a
             => DumpFlag
             -> String
             -> String
             -> a
             -> MaybeT KZC a
    dumpPass f ext suffix x = lift $ do
        dump f filepath ext suffix (ppr x)
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
