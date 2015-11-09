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
import qualified Data.Text.Lazy.IO as TIO
import qualified Data.Text.Lazy.Encoding as E
import System.Directory (createDirectoryIfMissing)
import System.Environment
import System.Exit (exitFailure)
import System.FilePath (addExtension,
                        replaceExtension,
                        splitExtension,
                        takeDirectory)
import System.IO (IOMode(..),
                  hClose,
                  hPutStrLn,
                  openFile,
                  stderr)
import Text.PrettyPrint.Mainland

import Language.Ziria.Parser
import qualified Language.Ziria.Syntax as Z

import qualified KZC.Auto.Cg as A
import qualified KZC.Auto.Flatten as A
import qualified KZC.Auto.Fusion as A
import qualified KZC.Auto.Lint as A
import qualified KZC.Auto.Syntax as A
import KZC.Auto.Transform
import KZC.Cg
import KZC.Check
import qualified KZC.Core.Syntax as C
import KZC.Flags
import KZC.Label
import KZC.LambdaLift
import qualified KZC.Lint as Lint
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Rename
import KZC.SysTools

import Opts

main :: IO ()
main = do
    args <- getArgs
    (fs, files) <- compilerOpts args
    if mode fs == Help
      then do usage >>= hPutStrLn stderr
              return ()
      else evalKZC fs (mapM_ runPipeline files) `catch` printFailure
  where
    printFailure :: SomeException -> IO ()
    printFailure e = (hPutStrLn stderr . show) e >> exitFailure

runPipeline :: FilePath -> KZC ()
runPipeline filepath = do
    text  <- liftIO (E.decodeUtf8 <$> B.readFile filepath)
    text' <- runCpp filepath text
    whenDumpFlag DumpCPP $ do
        liftIO $ TIO.writeFile (addExtension root (".pp" ++ ext)) text'
    decls <- liftIO $ parseProgram text' start
    whenDynFlag PrettyPrint $
      liftIO $ putDocLn $ ppr decls
    void $ runMaybeT $ pipeline decls
  where
    (root, ext) = splitExtension filepath

    start :: Pos
    start = startPos filepath

    pipeline :: [Z.CompLet] -> MaybeT KZC ()
    pipeline =
        stopIf (testDynFlag StopAfterParse) >=>
        renamePhase >=>
        checkPhase >=>
        lintCore >=>
        lambdaLiftPhase >=>
        lintCore >=>
        iteFlag (testDynFlag Auto) autoCompilePhase compilePhase

    renamePhase :: [Z.CompLet] -> MaybeT KZC [Z.CompLet]
    renamePhase = lift . runRn . renameProgram >=> dumpPass DumpRename "zr" "rn"

    checkPhase :: [Z.CompLet] -> MaybeT KZC [C.Decl]
    checkPhase = lift . withTi . checkProgram >=> dumpPass DumpCore "core" "tc"

    lambdaLiftPhase :: [C.Decl] -> MaybeT KZC [C.Decl]
    lambdaLiftPhase = lift . runLift . liftProgram >=> dumpPass DumpLift "core" "ll"

    transformPhase :: [C.Decl] -> MaybeT KZC A.LProgram
    transformPhase = lift . runT . transformProgram >=> dumpPass DumpLift "acore" "trans"

    flattenPhase :: A.LProgram -> MaybeT KZC A.LProgram
    flattenPhase = lift . A.evalFl . A.flattenProgram >=> dumpPass DumpFlatten "acore" "flatten"

    fusionPhase :: A.LProgram -> MaybeT KZC A.LProgram
    fusionPhase = lift . A.withTc . SEFKT.runSEFKT . A.fuseProgram >=> dumpPass DumpFusion "acore" "fusion"

    compilePhase :: [C.Decl] -> MaybeT KZC ()
    compilePhase = stopIf (testDynFlag StopAfterCheck) >=>
                   lift . evalCg . compileProgram >=> lift . writeOutput

    autoCompilePhase :: [C.Decl] -> MaybeT KZC ()
    autoCompilePhase = transformPhase                           >=>
                       lintAuto                                 >=>
                       runIf (testDynFlag Flatten) flattenPhase >=>
                       lintAuto                                 >=>
                       runIf (testDynFlag Fuse) fusionPhase     >=>
                       lintAuto                                 >=>
                       stopIf (testDynFlag StopAfterCheck)      >=>
                       lift . A.evalCg . A.compileProgram       >=>
                       lift . writeOutput

    lintCore :: [C.Decl] -> MaybeT KZC [C.Decl]
    lintCore decls = lift $ do
        whenDynFlag Lint $
            Lint.withTc (Lint.checkDecls decls)
        return decls

    lintAuto :: IsLabel l
             => A.Program l
             -> MaybeT KZC (A.Program l)
    lintAuto p = lift $ do
        whenDynFlag AutoLint $
            A.withTc (A.checkProgram p)
        return p

    stopIf :: (Flags -> Bool) -> a -> MaybeT KZC a
    stopIf f x = do
        stop <- asksFlags f
        if stop then MaybeT (return Nothing) else return x

    runIf :: (Flags -> Bool) -> (a -> MaybeT KZC a) -> a -> MaybeT KZC a
    runIf f g x = do
        run <- asksFlags f
        if run then g x else return x

    iteFlag :: (Flags -> Bool) -> (a -> MaybeT KZC b) -> (a -> MaybeT KZC b) -> a -> MaybeT KZC b
    iteFlag f th el x = do
        stop <- asksFlags f
        if stop then th x else el x

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
