{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : KZC.Compiler
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Compiler (
    compileFiles
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Lazy as B
import Data.Foldable (toList)
import Data.IORef
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Symbol
import qualified Data.Text.Lazy.Encoding as E
import System.CPUTime (getCPUTime)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (replaceExtension,
                        takeDirectory)
import System.IO (IOMode(..),
                  hClose,
                  hPutStr,
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
import qualified KZC.Backend.C as CGen
import KZC.Check
import KZC.Compiler.Module
import KZC.Compiler.Types
import KZC.Config
import qualified KZC.Core.Label as C
import qualified KZC.Core.Lint as C
import qualified KZC.Core.Syntax as C
import qualified KZC.Expr.Lint as E
import qualified KZC.Expr.Syntax as E
import qualified KZC.Expr.ToCore as E
import KZC.Globals
import KZC.Label
import KZC.LambdaLift
import KZC.Monad
import KZC.Monad.SEFKT as SEFKT
import KZC.Name
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

data CEnv = CEnv
    { cStart :: Integer
    , cPass  :: !(IORef Int)
    , cDecls :: Seq E.Decl
    }
  deriving (Show)

defaultCEnv :: (MonadIO m, MonadRef IORef m) => m CEnv
defaultCEnv = do
    t <- liftIO getCPUTime
    p <- newRef 0
    return CEnv { cStart = t
                , cPass  = p
                , cDecls = mempty
                }

newtype C m a = C { unC :: ReaderT CEnv m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO,
              MonadReader CEnv,
              MonadException,
              MonadErr,
              MonadConfig)

deriving instance MonadRef IORef m => MonadRef IORef (C m)
deriving instance MonadAtomicRef IORef m => MonadAtomicRef IORef (C m)

runC :: (MonadIO m, MonadRef IORef m) => C m a -> m a
runC m = defaultCEnv >>= runReaderT (unC m)

askStartTime :: Monad m => C m Integer
askStartTime = asks cStart

getPass :: MonadRef IORef m => C m Int
getPass = asks cPass >>= readRef

incPass :: MonadAtomicRef IORef m => C m Int
incPass = do
    ref <- asks cPass
    atomicModifyRef' ref (\i -> (i + 1, i))

askDecls :: Monad m => C m [E.Decl]
askDecls = asks (toList . cDecls)

appendDecls :: Monad m => [E.Decl] -> C m a -> C m a
appendDecls decls =
    local $ \env -> env { cDecls = cDecls env <> Seq.fromList decls }

compileFiles :: [FilePath] -> KZC ()
compileFiles srcfiles = do
    summaries <- mapM summarizeSourceFile srcfiles
    sccs      <- modulesDepSCCs summaries
    runC $ compileRecursive (map Set.toList sccs)

compileRecursive :: [[ModuleInfo]] -> C KZC ()
compileRecursive [] =
    return ()

compileRecursive ([] : _) =
    fail "Empty module dependency group"

compileRecursive (mods@(_:_:_) : _) =
    faildoc $ nest 4 $
    text "Recursive module dependencies:" </>
    commasep (map (ppr . modSourcePath) mods)

compileRecursive [[modinfo]] = do
    liftIO $ putDocLn $ text "Compiling:" <+> dquotes (ppr (modSourcePath modinfo))
    loadDependencies (modSourcePath modinfo) $ do
      decls <- askDecls
      compileExprProgram (modSourcePath modinfo) (E.Program [] decls)

compileRecursive ([modinfo] : sccs) = do
    liftIO $ putDocLn $ text "Loading:" <+> dquotes (ppr (modSourcePath modinfo))
    loadDependencies (modSourcePath modinfo) $
        compileRecursive sccs

getStructIds :: C KZC [Symbol]
getStructIds = do
    decls <- askDecls
    return [nameSym n | E.LetStructD (E.Struct n) _ _ <- decls]

setFileDialect :: MonadIO m => FilePath -> m ()
setFileDialect filepath = do
    dialect <- moduleDialect filepath
    when (dialect == Z.Classic) $
        setClassicDialect True

loadDependencies :: FilePath -> C KZC a -> C KZC a
loadDependencies filepath k = do
    setFileDialect filepath
    maybe_prog <- runMaybeT $ pipeline filepath
    case maybe_prog of
      Nothing                  -> k
      Just (E.Program _ decls) -> appendDecls decls k
  where
    pipeline :: FilePath -> MaybeT (C KZC) E.Program
    pipeline =
        parsePhase >=>
        pprPhase >=>
        stopIf (testDynFlag StopAfterParse) >=>
        tracePhase "rename" renamePhase >=>
        tracePhase "typecheck" checkPhase

    parsePhase :: FilePath -> MaybeT (C KZC) Z.Program
    parsePhase filepath = do
        structIds <- lift getStructIds
        lift $ lift $ parseProgramFromFile (Set.fromList structIds) filepath

    pprPhase :: Z.Program -> MaybeT (C KZC) Z.Program
    pprPhase decls = do
        whenDynFlag PrettyPrint $
            liftIO $ putDocLn $ ppr decls
        return decls

    renamePhase :: Z.Program -> MaybeT (C KZC) Z.Program
    renamePhase =
        lift . lift . liftRn . renameProgram >=>
        dumpPass DumpRename "zr" "rn"

    checkPhase :: Z.Program -> MaybeT (C KZC) E.Program
    checkPhase =
        lift . lift . liftTi . checkProgram >=>
        dumpPass DumpCore "expr" "tc"

    dumpPass :: Pretty a
             => DumpFlag
             -> String
             -> String
             -> a
             -> MaybeT (C KZC) a
    dumpPass f ext suffix x = do
        pass <- lift incPass
        lift $ lift $ dump f filepath ext (printf "%02d-%s" pass suffix) (ppr x)
        return x

compileExprProgram :: FilePath -> E.Program -> C KZC ()
compileExprProgram filepath prog =  do
    setFileDialect filepath
    void $ runMaybeT $ pipeline prog
  where
    pipeline :: E.Program -> MaybeT (C KZC) ()
    pipeline =
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
        iterateSimplPhase :: IsLabel l => String -> C.Program l -> MaybeT (C KZC) (C.Program l)
        iterateSimplPhase desc prog0 = do
            n <- asksConfig maxSimpl
            go 0 n prog0
          where
            go :: IsLabel l => Int -> Int -> C.Program l -> MaybeT (C KZC) (C.Program l)
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

    lambdaLiftPhase :: E.Program -> MaybeT (C KZC) E.Program
    lambdaLiftPhase =
        lift . lift . C.liftTc . runLift . liftProgram >=>
        dumpPass DumpLift "expr" "ll"

    exprToCorePhase :: IsLabel l => E.Program -> MaybeT (C KZC) (C.Program l)
    exprToCorePhase =
        lift . lift . C.liftTc . E.runTC . E.exprToCore >=>
        dumpPass DumpLift "core" "exprToCore"

    occPhase :: C.Program l -> MaybeT (C KZC) (C.Program l)
    occPhase =
        lift . lift . C.liftTc . occProgram

    simplPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l, SimplStats)
    simplPhase =
        lift . lift . C.liftTc . simplProgram

    hashconsPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    hashconsPhase =
        lift . lift . C.liftTc . hashConsConsts >=>
        dumpPass DumpHashCons "core" "hashcons"

    ratePhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    ratePhase =
        lift . lift . C.liftTc . rateProgram >=>
        dumpPass DumpRate "core" "rate"

    coalescePhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    coalescePhase =
        lift . lift . C.liftTc . coalesceProgram >=>
        dumpPass DumpCoalesce "core" "coalesce"

    fusionPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    fusionPhase =
        lift . lift . C.liftTc . SEFKT.runSEFKT . fuseProgram >=>
        dumpPass DumpFusion "core" "fusion"

    floatViewsPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    floatViewsPhase =
        lift . lift . C.liftTc . floatViews >=>
        dumpPass DumpViews "core" "float-views"

    lowerViewsPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    lowerViewsPhase =
        lift . lift . C.liftTc . lowerViews >=>
        dumpPass DumpViews "core" "lower-views"

    autolutPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    autolutPhase =
        lift . lift . C.liftTc . autolutProgram >=>
        dumpPass DumpAutoLUT "core" "autolut"

    lutToGenPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    lutToGenPhase =
        lift . lift . C.liftTc . lutToGen >=>
        dumpPass DumpLUT "core" "lutToGen"

    lowerGenPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    lowerGenPhase =
        lift . lift . C.liftTc . lowerGenerators >=>
        dumpPass DumpLUT "core" "lowerGen"

    evalPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    evalPhase =
        lift . lift . C.liftTc . evalProgram >=>
        dumpPass DumpEval "core" "peval"

    refFlowPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    refFlowPhase =
        lift . lift . C.liftTc . rfProgram >=>
        dumpPass DumpEval "core" "rflow"

    needDefaultPhase :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    needDefaultPhase =
        lift . lift . C.liftTc . needDefaultProgram >=>
        dumpPass DumpEval "core" "needdefault"

    compilePhase :: C.LProgram -> MaybeT (C KZC) ()
    compilePhase =
        lift . lift . CGen.compileProgram >=>
        lift . lift . writeOutput

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

    dumpFinal :: IsLabel l => C.Program l -> MaybeT (C KZC) (C.Program l)
    dumpFinal = dumpPass DumpCore "core" "final"

    dumpPass :: Pretty a
             => DumpFlag
             -> String
             -> String
             -> a
             -> MaybeT (C KZC) a
    dumpPass f ext suffix x = do
        pass <- lift incPass
        lift $ lift $ dump f filepath ext (printf "%02d-%s" pass suffix) (ppr x)
        return x

traceExprPhase :: String
               -> (a -> MaybeT (C KZC) E.Program)
               -> a
               -> MaybeT (C KZC) E.Program
traceExprPhase phase act =
    tracePhase phase act >=> tracePhase "lint" lintExpr

traceCorePhase :: IsLabel l
               => String
               -> (a -> MaybeT (C KZC) (C.Program l))
               -> a
               -> MaybeT (C KZC) (C.Program l)
traceCorePhase phase act =
    tracePhase phase act >=> tracePhase "lint" lintCore

tracePhase :: String
           -> (a -> MaybeT (C KZC) b)
           -> a
           -> MaybeT (C KZC) b
tracePhase phase act x = do
    doTrace <- asksConfig (testTraceFlag TracePhase)
    if doTrace
      then do pass       <- lift getPass
              start      <- lift askStartTime
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

lintExpr :: E.Program -> MaybeT (C KZC) E.Program
lintExpr prog = lift $ lift $ do
    whenDynFlag Lint $
        E.liftTc (E.checkProgram prog)
    return prog

lintCore :: IsLabel l
         => C.Program l
         -> MaybeT (C KZC) (C.Program l)
lintCore prog = lift $ lift $ do
    whenDynFlag Lint $
        C.liftTc (C.checkProgram prog)
    return prog

stopIf :: (Config -> Bool) -> a -> MaybeT (C KZC) a
stopIf f x = do
    stop <- asksConfig f
    if stop then MaybeT (return Nothing) else return x

runIf :: (Config -> Bool) -> (a -> MaybeT (C KZC) a) -> a -> MaybeT (C KZC) a
runIf f g x = do
    run <- asksConfig f
    if run then g x else return x

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
