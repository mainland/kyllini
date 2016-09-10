-- |
-- Module      : KZC.Globals
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Globals (
    setMaxErrContext,
    maxErrContext,

    setPrintUniques,
    printUniques,

    setExpertTypes,
    expertTypes
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
