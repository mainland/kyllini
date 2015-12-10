{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Util.Env
-- Copyright   :  (c) Drexel University 2015
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Util.Env (
    extendEnv,
    lookupEnv
  ) where

import Control.Monad.Reader
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map

extendEnv :: forall m r k v a . (Ord k, MonadReader r m)
          => (r -> Map k v)
          -> (r -> Map k v -> r)
          -> [(k, v)]
          -> m a
          -> m a
extendEnv _ _ [] m = m

extendEnv proj upd kvs m =
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupEnv :: (Ord k, MonadReader r m)
          => (r -> Map k v)
          -> m v
          -> k
          -> m v
lookupEnv proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v
