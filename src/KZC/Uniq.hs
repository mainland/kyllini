{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Uniq
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Uniq (
    Uniq(..),
    MonadUnique(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

newtype Uniq = Uniq Int
  deriving (Eq, Ord, Read, Show)

instance Pretty Uniq where
    ppr (Uniq u) = ppr u

class Monad m => MonadUnique m where
    newUnique :: m Uniq

instance MonadUnique m => MonadUnique (MaybeT m) where
    newUnique = lift newUnique

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadUnique m) => MonadUnique (ErrorT e m) where
    newUnique = lift newUnique
#endif /* !MIN_VERSION_base(4,8,0) */

instance MonadUnique m => MonadUnique (ExceptT e m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ReaderT r m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    newUnique = lift newUnique
