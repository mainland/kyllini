{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Flags
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Flags (
    ModeFlag(..),
    DynFlag(..),
    WarnFlag(..),
    DumpFlag(..),
    TraceFlag(..),
    Flags(..),

    defaultFlags,

    MonadFlags(..),
    asksFlags,

    flagImplications,

    setMode,
    testDynFlag,
    setDynFlag,
    unsetDynFlag,
    testWarnFlag,
    setWarnFlag,
    unsetWarnFlag,
    testDumpFlag,
    setDumpFlag,
    testTraceFlag,
    setTraceFlag,

    whenDynFlag,
    whenWarnFlag,
    whenDumpFlag
  ) where

import Control.Monad (when)
#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
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
             | AutoLint
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
  deriving (Eq, Ord, Enum, Bounded, Show)

data WarnFlag = WarnError
              | WarnUnusedCommandBind
              | WarnUnsafeAutoCast
              | WarnUnsafeParAutoCast
  deriving (Eq, Ord, Enum, Bounded, Show)

data DumpFlag = DumpCPP
              | DumpRename
              | DumpLift
              | DumpFusion
              | DumpCore
              | DumpAuto
              | DumpOcc
              | DumpSimpl
              | DumpEval
              | DumpAutoLUT
              | DumpLUT
              | DumpHashCons
  deriving (Eq, Ord, Enum, Bounded, Show)

data TraceFlag = TracePhase
               | TraceLexer
               | TraceParser
               | TraceRn
               | TraceLift
               | TraceTc
               | TraceCg
               | TraceLint
               | TraceAuto
               | TraceAutoLint
               | TraceFusion
               | TraceSimplify
               | TraceEval
               | TraceAutoLUT
               | TraceLUT
               | TraceRefFlow
               | TraceNeedDefault
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

data Flags = Flags
    { mode       :: !ModeFlag
    , verbLevel  :: !Int
    , maxErrCtx  :: !Int
    , maxSimpl   :: !Int
    , maxLUT     :: !Int
    , maxLUTLog2 :: !Int
    , minLUTOps  :: !Int

    , dynFlags   :: !(FlagSet DynFlag)
    , warnFlags  :: !(FlagSet WarnFlag)
    , dumpFlags  :: !(FlagSet DumpFlag)
    , traceFlags :: !(FlagSet TraceFlag)

    , includePaths :: ![FilePath]
    , defines      :: ![(String, String)]

    , output  :: Maybe FilePath
    , dumpDir :: Maybe FilePath
    }
  deriving (Eq, Ord, Show)

instance Monoid Flags where
    mempty = Flags
        { mode       = Compile
        , verbLevel  = 0
        , maxErrCtx  = 1
        , maxSimpl   = 4
        , maxLUT     = 32*1024 -- Default maximum size for LUT is 32K bytes
        , maxLUTLog2 = 5 + 10  -- Default maximum size for LUT log_2 is 15
        , minLUTOps  = 5 -- Minimum number of operations necessary to consider a
                         -- LUT for an expression

        , dynFlags   = mempty
        , warnFlags  = mempty
        , dumpFlags  = mempty
        , traceFlags = mempty

        , includePaths = []
        , defines      = []

        , output  = Nothing
        , dumpDir = Nothing
        }

    mappend f1 f2 = Flags
        { mode       = mode f2
        , verbLevel  = verbLevel f1 + verbLevel f2
        , maxErrCtx  = max (maxErrCtx f1) (maxErrCtx f2)
        , maxSimpl   = max (maxSimpl f1) (maxSimpl f2)
        , maxLUT     = max (maxLUT f1) (maxLUT f2)
        , maxLUTLog2 = max (maxLUT f1) (maxLUT f2)
        , minLUTOps  = min (minLUTOps f1) (minLUTOps f2)

        , dynFlags   = dynFlags f1   <> dynFlags f2
        , warnFlags  = warnFlags f1  <> warnFlags f2
        , dumpFlags  = dumpFlags f1  <> dumpFlags f2
        , traceFlags = traceFlags f1 <> traceFlags f2

        , includePaths = includePaths f1 <> includePaths f2
        , defines      = defines f1 <> defines f2

        , output  = output  f1 <> output f2
        , dumpDir = dumpDir f1 <> dumpDir f2
        }

defaultFlags :: Flags
defaultFlags =
    setFlags setDynFlag  defaultDynFlags $
    setFlags setWarnFlag defaultWarnFlags
    mempty
  where
    setFlags :: (a -> Flags -> Flags)
             -> [a]
             -> Flags
             -> Flags
    setFlags f xs flags = foldl' (flip f) flags xs

    defaultDynFlags :: [DynFlag]
    defaultDynFlags = [LinePragmas]

    defaultWarnFlags :: [WarnFlag]
    defaultWarnFlags = [ WarnUnusedCommandBind
                       , WarnUnsafeAutoCast
                       ]

class Monad m => MonadFlags m where
    askFlags   :: m Flags
    localFlags :: (Flags -> Flags) -> m a -> m a

asksFlags :: MonadFlags m => (Flags -> a) -> m a
asksFlags f = fmap f askFlags

-- | Set all flags implied by other flags
flagImplications :: Flags -> Flags
flagImplications = fixpoint go
  where
    fixpoint :: Eq a => (a -> a) -> a -> a
    fixpoint f x | x' == x   = x
                 | otherwise = fixpoint f x'
      where
        x' = f x

    go :: Flags -> Flags
    go = imp Fuse (setDynFlag AlwaysInlineComp) .
         imp MayInlineVal (setDynFlag Simplify) .
         imp MayInlineFun (setDynFlag Simplify) .
         imp MayInlineComp (setDynFlag Simplify) .
         imp AlwaysInlineComp (setDynFlag Simplify)

    imp :: DynFlag
        -> (Flags -> Flags)
        -> Flags -> Flags
    imp f g fs =
        if testDynFlag f fs then g fs else fs

instance MonadFlags m => MonadFlags (MaybeT m) where
    askFlags       = lift askFlags
    localFlags f m = MaybeT $ localFlags f (runMaybeT m)

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadFlags m) => MonadFlags (ErrorT e m) where
    askFlags       = lift askFlags
    localFlags f m = ErrorT $ localFlags f (runErrorT m)
#endif /* !MIN_VERSION_base(4,8,0) */

instance (MonadFlags m) => MonadFlags (ExceptT e m) where
    askFlags       = lift askFlags
    localFlags f m = ExceptT $ localFlags f (runExceptT m)

instance MonadFlags m => MonadFlags (ReaderT r m) where
    askFlags       = lift askFlags
    localFlags f m = ReaderT $ \r -> localFlags f (runReaderT m r)

instance MonadFlags m => MonadFlags (StateT s m) where
    askFlags       = lift askFlags
    localFlags f m = StateT $ \s -> localFlags f (runStateT m s)

instance (Monoid w, MonadFlags m) => MonadFlags (WriterT w m) where
    askFlags       = lift askFlags
    localFlags f m = WriterT $ localFlags f (runWriterT m)

setMode :: ModeFlag -> Flags -> Flags
setMode f flags = flags { mode = f }

testDynFlag :: DynFlag -> Flags -> Bool
testDynFlag f flags = dynFlags flags `testFlag` f

setDynFlag :: DynFlag -> Flags -> Flags
setDynFlag f flags = flags { dynFlags = setFlag (dynFlags flags) f }

unsetDynFlag :: DynFlag -> Flags -> Flags
unsetDynFlag f flags = flags { dynFlags = unsetFlag (dynFlags flags) f }

testWarnFlag :: WarnFlag -> Flags -> Bool
testWarnFlag f flags = warnFlags flags `testFlag` f

setWarnFlag :: WarnFlag -> Flags -> Flags
setWarnFlag f flags = flags { warnFlags = setFlag (warnFlags flags) f }

unsetWarnFlag :: WarnFlag -> Flags -> Flags
unsetWarnFlag f flags = flags { warnFlags = unsetFlag (warnFlags flags) f }

testDumpFlag :: DumpFlag -> Flags -> Bool
testDumpFlag f flags = dumpFlags flags `testFlag` f

setDumpFlag :: DumpFlag -> Flags -> Flags
setDumpFlag f flags = flags { dumpFlags = setFlag (dumpFlags flags) f }

testTraceFlag :: TraceFlag -> Flags -> Bool
testTraceFlag f flags = traceFlags flags `testFlag` f

setTraceFlag :: TraceFlag -> Flags -> Flags
setTraceFlag f flags = flags { traceFlags = setFlag (traceFlags flags) f }

whenDynFlag :: MonadFlags m => DynFlag -> m () -> m ()
whenDynFlag f act = do
    doDump <- asksFlags (testDynFlag f)
    when doDump act

whenWarnFlag :: MonadFlags m => WarnFlag -> m () -> m ()
whenWarnFlag f act = do
    doDump <- asksFlags (testWarnFlag f)
    when doDump act

whenDumpFlag :: MonadFlags m => DumpFlag -> m () -> m ()
whenDumpFlag f act = do
    doDump <- asksFlags (testDumpFlag f)
    when doDump act
