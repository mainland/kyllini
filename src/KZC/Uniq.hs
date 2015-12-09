{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Uniq
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Uniq (
    Uniq(..),
    MonadUnique(..)
  ) where

import Control.Monad.Error (Error, ErrorT(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import Data.Monoid (Monoid)
import Text.PrettyPrint.Mainland

newtype Uniq = Uniq Int
  deriving (Eq, Ord, Read, Show)

instance Pretty Uniq where
    ppr (Uniq u) = ppr u

class Monad m => MonadUnique m where
    newUnique :: m Uniq

instance MonadUnique m => MonadUnique (MaybeT m) where
    newUnique = lift newUnique

instance (Error e, MonadUnique m) => MonadUnique (ErrorT e m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ReaderT r m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    newUnique = lift newUnique
