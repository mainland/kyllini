{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Platform
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Platform (
    Platform(..),

    MonadPlatform(..),
    asksPlatform
  ) where

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

data Platform = Platform { platformIntWidth :: Int }
  deriving (Eq, Ord, Read, Show)

class Monad m => MonadPlatform m where
    askPlatform   :: m Platform
    localPlatform :: (Platform -> Platform) -> m a -> m a

asksPlatform :: MonadPlatform m => (Platform -> a) -> m a
asksPlatform f = fmap f askPlatform

instance MonadPlatform ((->) Platform) where
    askPlatform       = id
    localPlatform f m = m . f

instance MonadPlatform m => MonadPlatform (MaybeT m) where
    askPlatform       = lift askPlatform
    localPlatform f m = MaybeT $ localPlatform f (runMaybeT m)

instance MonadPlatform m => MonadPlatform (ContT r m) where
    askPlatform   = lift askPlatform
    localPlatform = Cont.liftLocal askPlatform localPlatform

instance (MonadPlatform m) => MonadPlatform (ExceptT e m) where
    askPlatform       = lift askPlatform
    localPlatform f m = ExceptT $ localPlatform f (runExceptT m)

instance (MonadPlatform m) => MonadPlatform (ExceptionT m) where
    askPlatform       = lift askPlatform
    localPlatform f m = ExceptionT $ localPlatform f (runExceptionT m)

instance MonadPlatform m => MonadPlatform (ReaderT r m) where
    askPlatform       = lift askPlatform
    localPlatform f m = ReaderT $ \r -> localPlatform f (runReaderT m r)

instance MonadPlatform m => MonadPlatform (StateT s m) where
    askPlatform       = lift askPlatform
    localPlatform f m = StateT $ \s -> localPlatform f (runStateT m s)

instance MonadPlatform m => MonadPlatform (S.StateT s m) where
    askPlatform       = lift askPlatform
    localPlatform f m = S.StateT $ \s -> localPlatform f (S.runStateT m s)

instance (Monoid w, MonadPlatform m) => MonadPlatform (WriterT w m) where
    askPlatform       = lift askPlatform
    localPlatform f m = WriterT $ localPlatform f (runWriterT m)

instance (Monoid w, MonadPlatform m) => MonadPlatform (S.WriterT w m) where
    askPlatform       = lift askPlatform
    localPlatform f m = S.WriterT $ localPlatform f (S.runWriterT m)
