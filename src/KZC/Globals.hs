-- |
-- Module      : KZC.Globals
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Globals (
    setPrintUniques,
    printUniques,

    setExpertTypes,
    expertTypes
  ) where

import Control.Monad.Trans (MonadIO(..))
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

gPrintUniques :: IORef Bool
gPrintUniques =
    unsafePerformIO $ newIORef False

setPrintUniques :: MonadIO m => Bool -> m ()
setPrintUniques flag =
    liftIO $ writeIORef gPrintUniques flag

printUniques :: Bool
{-# NOINLINE printUniques #-}
printUniques =
    unsafePerformIO $ readIORef gPrintUniques

gExpertTypes :: IORef Bool
gExpertTypes =
    unsafePerformIO $ newIORef False

setExpertTypes :: MonadIO m => Bool -> m ()
setExpertTypes flag =
    liftIO $ writeIORef gExpertTypes flag

expertTypes :: Bool
{-# NOINLINE expertTypes #-}
expertTypes =
    unsafePerformIO $ readIORef gExpertTypes
