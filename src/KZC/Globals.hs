-- |
-- Module      : KZC.Globals
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Globals (
    setMaxErrContext,
    maxErrContext,

    setPrintUniques,
    printUniques,

    setExpertTypes,
    expertTypes,

    setStrictClassic,
    strictClassic,

    setClassicDialect,
    classicDialect
  ) where

import Control.Monad.Trans (MonadIO(..))
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

gPrintUniques :: IORef Bool
{-# NOINLINE gPrintUniques #-}
gPrintUniques = unsafePerformIO $ newIORef False

setPrintUniques :: MonadIO m => Bool -> m ()
setPrintUniques flag = liftIO $ writeIORef gPrintUniques flag

printUniques :: Bool
{-# NOINLINE printUniques #-}
printUniques = unsafePerformIO $ readIORef gPrintUniques

gMaxErrContext :: IORef Int
{-# NOINLINE gMaxErrContext #-}
gMaxErrContext = unsafePerformIO $ newIORef 4

setMaxErrContext :: MonadIO m => Int -> m ()
setMaxErrContext n = liftIO $ writeIORef gMaxErrContext n

maxErrContext :: Int
{-# NOINLINE maxErrContext #-}
maxErrContext = unsafePerformIO $ readIORef gMaxErrContext

gExpertTypes :: IORef Bool
{-# NOINLINE gExpertTypes #-}
gExpertTypes = unsafePerformIO $ newIORef False

setExpertTypes :: MonadIO m => Bool -> m ()
setExpertTypes flag = liftIO $ writeIORef gExpertTypes flag

expertTypes :: Bool
{-# NOINLINE expertTypes #-}
expertTypes = unsafePerformIO $ readIORef gExpertTypes

gStrictClassic :: IORef Bool
{-# NOINLINE gStrictClassic #-}
gStrictClassic = unsafePerformIO $ newIORef False

setStrictClassic :: MonadIO m => Bool -> m ()
setStrictClassic flag = liftIO $ writeIORef gStrictClassic flag

strictClassic :: Bool
{-# NOINLINE strictClassic #-}
strictClassic = unsafePerformIO $ readIORef gStrictClassic

gClassicDialect :: IORef Bool
{-# NOINLINE gClassicDialect #-}
gClassicDialect = unsafePerformIO $ newIORef False

setClassicDialect :: MonadIO m => Bool -> m ()
setClassicDialect flag = liftIO $ writeIORef gClassicDialect flag

-- | A 'Bool' flag indicating whether we are currently using the classic Ziria
-- dialect. This should only be used for pretty-printing.
classicDialect :: Bool
{-# NOINLINE classicDialect #-}
classicDialect = unsafePerformIO $ readIORef gClassicDialect
