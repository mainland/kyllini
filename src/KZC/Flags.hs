-- |
-- Module      :  KZC.Flags
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Flags (
    ModeFlag(..),
    DynFlag(..),
    WarnFlag(..),
    DumpFlag(..),
    TraceFlag(..),
    Flags(..),

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

    MonadFlags(..),
    asksFlags,
    whenDynFlag,
    whenWarnFlag,
    whenDumpFlag
  ) where

import Control.Monad (when)
import Data.Bits
import Data.Int
import Data.Monoid

data ModeFlag = Help
              | Compile
  deriving (Eq, Ord, Enum, Show)

data DynFlag = Quiet
             | Check
             | PrettyPrint
             | Lint
             | PrintUniques
             | ExpertTypes
  deriving (Eq, Ord, Enum, Show)

data WarnFlag = WarnError
  deriving (Eq, Ord, Enum, Show)

data DumpFlag = DumpCPP
              | DumpRename
              | DumpCore
  deriving (Eq, Ord, Enum, Show)

data TraceFlag = TraceLexer
               | TraceParser
               | TraceRn
               | TraceTc
               | TraceLint
  deriving (Eq, Ord, Enum, Show)

data Flags = Flags
    { mode      :: !ModeFlag
    , verbLevel :: !Int

    , dynFlags   :: !Int32
    , warnFlags  :: !Int32
    , dumpFlags  :: !Int32
    , traceFlags :: !Int32

    , includePaths :: ![FilePath]
    , defines      :: ![(String, String)]

    , output  :: Maybe FilePath
    , dumpDir :: Maybe FilePath
    }

instance Monoid Flags where
    mempty = Flags
        { mode      = Compile
        , verbLevel = 0

        , dynFlags   = 0
        , warnFlags  = 0
        , dumpFlags  = 0
        , traceFlags = 0

        , includePaths = []
        , defines      = []

        , output  = Nothing
        , dumpDir = Nothing
        }

    mappend f1 f2 = Flags
        { mode      = mode f2
        , verbLevel = verbLevel f1 + verbLevel f2

        , dynFlags   = dynFlags f1   .|. dynFlags f2
        , warnFlags  = warnFlags f1  .|. warnFlags f2
        , dumpFlags  = dumpFlags f1  .|. dumpFlags f2
        , traceFlags = traceFlags f1 .|. traceFlags f2

        , includePaths = includePaths f1 <> includePaths f2
        , defines      = defines f1 <> defines f2

        , output  = output  f1 <> output f2
        , dumpDir = dumpDir f1 <> dumpDir f2
        }

setMode :: ModeFlag -> Flags -> Flags
setMode f flags = flags { mode = f }

testDynFlag :: DynFlag -> Flags -> Bool
testDynFlag f flags =
    dynFlags flags `testBit` fromEnum f

setDynFlag :: DynFlag -> Flags -> Flags
setDynFlag f flags =
    flags { dynFlags = dynFlags flags `setBit` fromEnum f }

unsetDynFlag :: DynFlag -> Flags -> Flags
unsetDynFlag f flags =
    flags { dynFlags = dynFlags flags `clearBit` fromEnum f }

testWarnFlag :: WarnFlag -> Flags -> Bool
testWarnFlag f flags =
    warnFlags flags `testBit` fromEnum f

setWarnFlag :: WarnFlag -> Flags -> Flags
setWarnFlag f flags =
    flags { warnFlags = warnFlags flags `setBit` fromEnum f }

unsetWarnFlag :: WarnFlag -> Flags -> Flags
unsetWarnFlag f flags =
    flags { warnFlags = warnFlags flags `clearBit` fromEnum f }

testDumpFlag :: DumpFlag -> Flags -> Bool
testDumpFlag f flags =
    dumpFlags flags `testBit` fromEnum f

setDumpFlag :: DumpFlag -> Flags -> Flags
setDumpFlag f flags =
    flags { dumpFlags = dumpFlags flags `setBit` fromEnum f }

testTraceFlag :: TraceFlag -> Flags -> Bool
testTraceFlag f flags =
    traceFlags flags `testBit` fromEnum f

setTraceFlag :: TraceFlag -> Flags -> Flags
setTraceFlag f flags =
    flags { traceFlags = traceFlags flags `setBit` fromEnum f }

class Monad m => MonadFlags m where
    askFlags    :: m Flags
    localFlags  :: Flags -> m a -> m a

asksFlags :: MonadFlags m => (Flags -> a) -> m a
asksFlags f = do
    fs <- askFlags
    return $ f fs

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
