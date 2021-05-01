{-# LANGUAGE BangPatterns #-}

-- |
-- Module      :  KZC.Util.Logic
-- Copyright   :  (c) 2016-2021 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Util.Logic (
    prune
  ) where

import Control.Applicative ((<|>), empty)
import Control.Monad.Logic (MonadLogic,
                            msplit)

-- | Prune after @n@ attempts.
prune :: MonadLogic m => Int -> m a -> m a
prune 0  _ = empty
prune !n m = do (a, m') <- maybe empty return =<< msplit m
                return a <|> prune (n-1) m'
