{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Config
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Config (
    ModeFlag(..),
    DynFlag(..),
    WarnFlag(..),
    DumpFlag(..),
    TraceFlag(..),
    Config(..),

    defaultConfig,

    MonadConfig(..),
    asksConfig,

    flagImplications,

    setMode,

    testDynFlag,
    setDynFlag,
    setDynFlags,
    unsetDynFlag,

    testWarnFlag,
    setWarnFlag,
    setWarnFlags,
    unsetWarnFlag,

    testWerrorFlag,
    setWerrorFlag,
    setWerrorFlags,
    unsetWerrorFlag,

    testDumpFlag,
    setDumpFlag,
    setDumpFlags,

    testTraceFlag,
    setTraceFlag,
    setTraceFlags,

    whenDynFlag,
    whenWarnFlag,
    whenWerrorFlag,
    whenDumpFlag,
    whenVerb,
    whenVerbLevel
  ) where

import Control.Monad (when)
#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Exception (ExceptionT(..), runExceptionT)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT(..))
import qualified Control.Monad.Trans.Cont as Cont
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))
import Data.Bits
import Data.List (foldl')
import Data.Monoid
import Data.Word

data ModeFlag = Help
              | Compile
  deriving (Eq, Ord, Enum, Show)

data DynFlag = Quiet
             | StopAfterParse
             | StopAfterCheck
             | PrettyPrint
             | Lint
             | PrintUniques
             | ExpertTypes
             | LinePragmas
             | Fuse
             | Simplify
             | MayInlineVal
             | MayInlineFun
             | MayInlineComp
             | AlwaysInlineComp
             | BoundsCheck
             | PartialEval
             | Timers
             | AutoLUT
             | LUT
             | NoGensym
             | Pipeline
             | PipelineAll
             | Coalesce
             | VectOnlyBytes
             | VectFilterAnn
             | CoalesceTop
             | FuseUnroll
             | LowerGen
             | ComputeLUTs
             | FloatViews
             | ShowCgStats
             | ShowFusionStats
  deriving (Eq, Ord, Enum, Bounded, Show)

data WarnFlag = WarnSimplifierBailout
              | WarnUnusedCommandBind
              | WarnUnsafeAutoCast
              | WarnUnsafeParAutoCast
              | WarnRateMismatch
              | WarnFusionFailure
              | WarnBitArrayCopy
  deriving (Eq, Ord, Enum, Bounded, Show)

data DumpFlag = DumpCPP
              | DumpRename
              | DumpLift
              | DumpFusion
              | DumpCore
              | DumpOcc
              | DumpSimpl
              | DumpEval
              | DumpAutoLUT
              | DumpLUT
              | DumpHashCons
              | DumpStaticRefs
              | DumpRate
              | DumpCoalesce
              | DumpViews
  deriving (Eq, Ord, Enum, Bounded, Show)

data TraceFlag = TracePhase
               | TraceLexer
               | TraceParser
               | TraceRn
               | TraceLift
               | TraceTc
               | TraceCg
               | TraceLint
               | TraceExprToCore
               | TraceFusion
               | TraceSimplify
               | TraceEval
               | TraceAutoLUT
               | TraceLUT
               | TraceRefFlow
               | TraceNeedDefault
               | TraceRate
               | TraceCoalesce
               | TraceViews
  deriving (Eq, Ord, Enum, Bounded, Show)

newtype FlagSet a = FlagSet Word32
  deriving (Eq, Ord)

testFlag :: Enum a => FlagSet a -> a -> Bool
testFlag (FlagSet fs) f = fs `testBit` fromEnum f

setFlag :: Enum a => FlagSet a -> a -> FlagSet a
setFlag (FlagSet fs) f = FlagSet $ fs `setBit` fromEnum f

unsetFlag :: Enum a => FlagSet a -> a -> FlagSet a
unsetFlag (FlagSet fs) f = FlagSet $ fs `clearBit` fromEnum f

instance Monoid (FlagSet a) where
    mempty = FlagSet 0

    FlagSet x `mappend` FlagSet y = FlagSet (x .|. y)

instance (Enum a, Bounded a, Show a) => Show (FlagSet a) where
    show (FlagSet n) = show [f | f <- [minBound..maxBound::a],
                                 n `testBit` fromEnum f]

data Config = Config
    { mode       :: !ModeFlag
    , verbLevel  :: !Int
    , maxErrCtx  :: !Int
    , maxSimpl   :: !Int
    , maxLUT     :: !Int
    , maxLUTLog2 :: !Int
    , minLUTOps  :: !Int

    , maxFusionBlowup :: !Double

    , minMemcpyBytes :: !Int

    , dynFlags    :: !(FlagSet DynFlag)
    , warnFlags   :: !(FlagSet WarnFlag)
    , werrorFlags :: !(FlagSet WarnFlag)
    , dumpFlags   :: !(FlagSet DumpFlag)
    , traceFlags  :: !(FlagSet TraceFlag)

    , includePaths :: ![FilePath]
    , defines      :: ![(String, String)]

    , output  :: Maybe FilePath
    , dumpDir :: Maybe FilePath

    , fuel :: !Int
    }
  deriving (Eq, Ord, Show)

instance Monoid Config where
    mempty = Config
        { mode       = Compile
        , verbLevel  = 0
        , maxErrCtx  = 1
        , maxSimpl   = 10
        , maxLUT     = 256*1024 -- Default maximum size for LUT is 256K bytes
        , maxLUTLog2 = 8 + 10  -- Default maximum size for LUT log_2 is 18
        , minLUTOps  = 5 -- Minimum number of operations necessary to consider a
                         -- LUT for an expression

        -- Maximum ratio of new code size to old code size. Why 3? Because
        -- transforming an expression to work over segments of an array requires
        -- a multiply and add for each index operation, which adds 2 operations,
        -- meaning overall we get approximately 3x the number of original
        -- operations.
        , maxFusionBlowup = 3.0

        -- Minimum number of bytes before we switch to memcpy
        , minMemcpyBytes = 0

        , dynFlags    = mempty
        , werrorFlags = mempty
        , warnFlags   = mempty
        , dumpFlags   = mempty
        , traceFlags  = mempty

        , includePaths = []
        , defines      = []

        , output  = Nothing
        , dumpDir = Nothing

        , fuel = 0
        }

    mappend f1 f2 = Config
        { mode       = mode f2
        , verbLevel  = verbLevel f1 + verbLevel f2
        , maxErrCtx  = max (maxErrCtx f1) (maxErrCtx f2)
        , maxSimpl   = max (maxSimpl f1) (maxSimpl f2)
        , maxLUT     = max (maxLUT f1) (maxLUT f2)
        , maxLUTLog2 = max (maxLUT f1) (maxLUT f2)
        , minLUTOps  = min (minLUTOps f1) (minLUTOps f2)

        , maxFusionBlowup = max (maxFusionBlowup f1) (maxFusionBlowup f2)

        , minMemcpyBytes = min (minMemcpyBytes f1) (minMemcpyBytes f2)

        , dynFlags    = dynFlags f1    <> dynFlags f2
        , warnFlags   = warnFlags f1   <> warnFlags f2
        , werrorFlags = werrorFlags f1 <> werrorFlags f2
        , dumpFlags   = dumpFlags f1   <> dumpFlags f2
        , traceFlags  = traceFlags f1  <> traceFlags f2

        , includePaths = includePaths f1 <> includePaths f2
        , defines      = defines f1 <> defines f2

        , output  = output  f1 <> output f2
        , dumpDir = dumpDir f1 <> dumpDir f2

        , fuel = fuel f1 + fuel f2
        }

defaultConfig :: Config
defaultConfig =
    setFlags setDynFlag  defaultDynFlags $
    setFlags setWarnFlag defaultWarnFlags
    mempty
  where
    setFlags :: (a -> Config -> Config)
             -> [a]
             -> Config
             -> Config
    setFlags f xs flags = foldl' (flip f) flags xs

    defaultDynFlags :: [DynFlag]
    defaultDynFlags = [ LinePragmas
                      , VectFilterAnn
                      , ComputeLUTs
                      ]

    defaultWarnFlags :: [WarnFlag]
    defaultWarnFlags = [WarnUnusedCommandBind]

class Monad m => MonadConfig m where
    askConfig   :: m Config
    localConfig :: (Config -> Config) -> m a -> m a

asksConfig :: MonadConfig m => (Config -> a) -> m a
asksConfig f = fmap f askConfig

-- | Set all flags implied by other flags
flagImplications :: Config -> Config
flagImplications = fixpoint go
  where
    fixpoint :: Eq a => (a -> a) -> a -> a
    fixpoint f x | x' == x   = x
                 | otherwise = fixpoint f x'
      where
        x' = f x

    go :: Config -> Config
    go = imp Fuse (setDynFlag AlwaysInlineComp) .
         imp Coalesce (setDynFlag AlwaysInlineComp) .
         imp MayInlineVal (setDynFlag Simplify) .
         imp MayInlineFun (setDynFlag Simplify) .
         imp MayInlineComp (setDynFlag Simplify) .
         imp AlwaysInlineComp (setDynFlag Simplify) .
         imp AutoLUT (setDynFlag FloatViews) .
         imp LUT (setDynFlag FloatViews)

    imp :: DynFlag
        -> (Config -> Config)
        -> Config -> Config
    imp f g fs =
        if testDynFlag f fs then g fs else fs

instance MonadConfig m => MonadConfig (MaybeT m) where
    askConfig       = lift askConfig
    localConfig f m = MaybeT $ localConfig f (runMaybeT m)

instance MonadConfig m => MonadConfig (ContT r m) where
    askConfig   = lift askConfig
    localConfig = Cont.liftLocal askConfig localConfig

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadConfig m) => MonadConfig (ErrorT e m) where
    askConfig       = lift askConfig
    localConfig f m = ErrorT $ localConfig f (runErrorT m)
#endif /* !MIN_VERSION_base(4,8,0) */

instance (MonadConfig m) => MonadConfig (ExceptT e m) where
    askConfig       = lift askConfig
    localConfig f m = ExceptT $ localConfig f (runExceptT m)

instance (MonadConfig m) => MonadConfig (ExceptionT m) where
    askConfig       = lift askConfig
    localConfig f m = ExceptionT $ localConfig f (runExceptionT m)

instance MonadConfig m => MonadConfig (ReaderT r m) where
    askConfig       = lift askConfig
    localConfig f m = ReaderT $ \r -> localConfig f (runReaderT m r)

instance MonadConfig m => MonadConfig (StateT s m) where
    askConfig       = lift askConfig
    localConfig f m = StateT $ \s -> localConfig f (runStateT m s)

instance MonadConfig m => MonadConfig (S.StateT s m) where
    askConfig       = lift askConfig
    localConfig f m = S.StateT $ \s -> localConfig f (S.runStateT m s)

instance (Monoid w, MonadConfig m) => MonadConfig (WriterT w m) where
    askConfig       = lift askConfig
    localConfig f m = WriterT $ localConfig f (runWriterT m)

instance (Monoid w, MonadConfig m) => MonadConfig (S.WriterT w m) where
    askConfig       = lift askConfig
    localConfig f m = S.WriterT $ localConfig f (S.runWriterT m)

setMode :: ModeFlag -> Config -> Config
setMode f flags = flags { mode = f }

testDynFlag :: DynFlag -> Config -> Bool
testDynFlag f flags = dynFlags flags `testFlag` f

setDynFlag :: DynFlag -> Config -> Config
setDynFlag f flags = flags { dynFlags = setFlag (dynFlags flags) f }

setDynFlags :: [DynFlag] -> Config -> Config
setDynFlags fs flags = foldl' (flip setDynFlag) flags fs

unsetDynFlag :: DynFlag -> Config -> Config
unsetDynFlag f flags = flags { dynFlags = unsetFlag (dynFlags flags) f }

testWarnFlag :: WarnFlag -> Config -> Bool
testWarnFlag f flags = warnFlags flags `testFlag` f

setWarnFlag :: WarnFlag -> Config -> Config
setWarnFlag f flags = flags { warnFlags = setFlag (warnFlags flags) f }

setWarnFlags :: [WarnFlag] -> Config -> Config
setWarnFlags fs flags = foldl' (flip setWarnFlag) flags fs

unsetWarnFlag :: WarnFlag -> Config -> Config
unsetWarnFlag f flags = flags { warnFlags = unsetFlag (warnFlags flags) f }

testWerrorFlag :: WarnFlag -> Config -> Bool
testWerrorFlag f flags = werrorFlags flags `testFlag` f

setWerrorFlag :: WarnFlag -> Config -> Config
setWerrorFlag f flags = flags { werrorFlags = setFlag (werrorFlags flags) f }

setWerrorFlags :: [WarnFlag] -> Config -> Config
setWerrorFlags fs flags = foldl' (flip setWerrorFlag) flags fs

unsetWerrorFlag :: WarnFlag -> Config -> Config
unsetWerrorFlag f flags = flags { werrorFlags = unsetFlag (werrorFlags flags) f }

testDumpFlag :: DumpFlag -> Config -> Bool
testDumpFlag f flags = dumpFlags flags `testFlag` f

setDumpFlag :: DumpFlag -> Config -> Config
setDumpFlag f flags = flags { dumpFlags = setFlag (dumpFlags flags) f }

setDumpFlags :: [DumpFlag] -> Config -> Config
setDumpFlags fs flags = foldl' (flip setDumpFlag) flags fs

testTraceFlag :: TraceFlag -> Config -> Bool
testTraceFlag f flags = traceFlags flags `testFlag` f

setTraceFlag :: TraceFlag -> Config -> Config
setTraceFlag f flags = flags { traceFlags = setFlag (traceFlags flags) f }

setTraceFlags :: [TraceFlag] -> Config -> Config
setTraceFlags fs flags = foldl' (flip setTraceFlag) flags fs

whenDynFlag :: MonadConfig m => DynFlag -> m () -> m ()
whenDynFlag f act = do
    doDump <- asksConfig (testDynFlag f)
    when doDump act

whenWarnFlag :: MonadConfig m => WarnFlag -> m () -> m ()
whenWarnFlag f act = do
    doDump <- asksConfig (testWarnFlag f)
    when doDump act

whenWerrorFlag :: MonadConfig m => WarnFlag -> m () -> m ()
whenWerrorFlag f act = do
    doDump <- asksConfig (testWerrorFlag f)
    when doDump act

whenDumpFlag :: MonadConfig m => DumpFlag -> m () -> m ()
whenDumpFlag f act = do
    doDump <- asksConfig (testDumpFlag f)
    when doDump act

whenVerb :: MonadConfig m => m () -> m ()
whenVerb = whenVerbLevel 1

whenVerbLevel :: MonadConfig m => Int -> m () -> m ()
whenVerbLevel lvlNeeded act = do
    lvl <- asksConfig verbLevel
    when (lvl >= lvlNeeded) act
