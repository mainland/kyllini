{-# LANGUAGE BangPatterns #-}

-- |
-- Module      :  KZC.Util.Logic
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Util.Logic (
    prune
  ) where

import Control.Monad (mplus,
                      mzero)
import Control.Monad.Logic (MonadLogic,
                            msplit)

-- | Prune after @n@ attempts.
prune :: MonadLogic m => Int -> m a -> m a
prune 0  _ = mzero
prune !n m = do (a, m') <- maybe mzero return =<< msplit m
                return a `mplus` prune (n-1) m'
