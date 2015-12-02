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

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Text.PrettyPrint.Mainland

newtype Uniq = Uniq Int
  deriving (Eq, Ord, Read, Show)

instance Pretty Uniq where
    ppr (Uniq u) = ppr u

class Monad m => MonadUnique m where
    newUnique :: m Uniq

instance (Error e, MonadUnique m) => MonadUnique (ErrorT e m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ReaderT r m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    newUnique = lift newUnique
