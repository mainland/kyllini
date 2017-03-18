{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Util.Memoize
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Util.Memoize (
    memoize
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Ref

-- | Memoize a monadic function.
memoize :: forall a b r m . (Ord a, MonadRef r m)
        => (a -> m b)
        -> m (a -> m b)
memoize f = do
    ref <- newRef Map.empty
    return $ f' ref
  where
    f' :: r (Map a b) -> a -> m b
    f' ref x = do
        m <- readRef ref
        case Map.lookup x m of
          Just v  -> return v
          Nothing -> do v <- f x
                        writeRef ref (Map.insert x v m)
                        return v
