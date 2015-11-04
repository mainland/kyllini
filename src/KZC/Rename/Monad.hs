{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Rename.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Rename.Monad (
    RnEnv(..),

    Rn(..),
    runRn,

    extend,
    lookupBy,

    inCompScope,
    inPureScope
  ) where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map

import Language.Ziria.Syntax

import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Trace
import KZC.Uniq

data RnEnv = RnEnv
    { vars      :: Map Var Var
    , compVars  :: Map Var Var
    , compScope :: Bool
    }

defaultRnEnv :: RnEnv
defaultRnEnv = RnEnv
    { vars       = Map.empty
    , compVars   = Map.empty
    , compScope  = False
    }

newtype Rn a = Rn { unRn :: ReaderT RnEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader RnEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runRn :: Rn a -> KZC a
runRn m = runReaderT (unRn m) defaultRnEnv

extend :: forall k v a . Ord k
       => (RnEnv -> Map k v)
       -> (RnEnv -> Map k v -> RnEnv)
       -> [(k, v)]
       -> Rn a
       -> Rn a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (RnEnv -> Map k v)
         -> Rn v
         -> k
         -> Rn v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

inCompScope :: Rn a -> Rn a
inCompScope m = local (\env -> env { compScope = True }) m

inPureScope :: Rn a -> Rn a
inPureScope m = local (\env -> env { compScope = False }) m
