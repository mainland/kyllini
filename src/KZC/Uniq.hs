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

import Control.Monad.Reader
import Text.PrettyPrint.Mainland

newtype Uniq = Uniq Int
  deriving (Eq, Ord, Read, Show)

instance Pretty Uniq where
    ppr (Uniq u) = ppr u

class Monad m => MonadUnique m where
    newUnique :: m Uniq

instance MonadUnique m => MonadUnique (ReaderT r m) where
    newUnique = lift newUnique
