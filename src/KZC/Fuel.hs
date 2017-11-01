-- |
-- Module      :  KZC.Fuel
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Fuel (
    MonadFuel(..)
  ) where

import Control.Monad.Except (ExceptT(..))
import Control.Monad.Exception (ExceptionT(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))

class Monad m => MonadFuel m where
    useFuel :: m Bool

instance MonadFuel m => MonadFuel (MaybeT m) where
    useFuel = lift useFuel

instance MonadFuel m => MonadFuel (ContT r m) where
    useFuel = lift useFuel

instance (MonadFuel m) => MonadFuel (ExceptT e m) where
    useFuel = lift useFuel

instance (MonadFuel m) => MonadFuel (ExceptionT m) where
    useFuel = lift useFuel

instance MonadFuel m => MonadFuel (ReaderT r m) where
    useFuel = lift useFuel

instance MonadFuel m => MonadFuel (StateT s m) where
    useFuel = lift useFuel

instance MonadFuel m => MonadFuel (S.StateT s m) where
    useFuel = lift useFuel

instance (Monoid w, MonadFuel m) => MonadFuel (WriterT w m) where
    useFuel = lift useFuel

instance (Monoid w, MonadFuel m) => MonadFuel (S.WriterT w m) where
    useFuel = lift useFuel
