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
import Text.PrettyPrint.Mainland

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
    { vars      = Map.empty
    , compVars  = Map.empty
    , compScope = False
    }

newtype Rn a = Rn { unRn :: RnEnv -> KZC a }

runRn :: Rn a -> KZC a
runRn m = unRn m defaultRnEnv

instance Functor Rn where
    fmap f x = x >>= return . f

instance Applicative Rn where
    pure  = return
    (<*>) = ap

instance Monad Rn where
    {-# INLINE return #-}
    return a = Rn $ \_ -> return a

    {-# INLINE (>>=) #-}
    m >>= f  = Rn $ \r -> do
               x <- unRn m r
               unRn (f x) r

    {-# INLINE (>>) #-}
    m1 >> m2 = Rn $ \r -> do
               _ <- unRn m1 r
               unRn m2 r

    fail msg = throw (FailException (string msg))

instance MonadReader RnEnv Rn where
    ask = Rn $ \r -> return r

    local f m = Rn $ \r -> unRn m (f r)

instance MonadRef IORef Rn where
    newRef x     = liftIO $ newRef x
    readRef r    = liftIO $ readRef r
    writeRef r x = liftIO $ writeRef r x

instance MonadIO Rn where
    liftIO = liftKZC . liftIO

instance MonadUnique Rn where
    newUnique = liftKZC newUnique

instance MonadKZC Rn where
    liftKZC m = Rn $ \_ -> m

instance MonadException Rn where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Rn $ \r ->
      unRn m r `catchContextException` \e -> unRn (h e) r

instance MonadErr Rn where
    {-# INLINE askErrCtx #-}
    askErrCtx = liftKZC askErrCtx

    {-# INLINE localErrCtx #-}
    localErrCtx ctx m = Rn $ \r -> localErrCtx ctx (unRn m r)

    {-# INLINE warnIsError #-}
    warnIsError = asksFlags (testWarnFlag WarnError)

instance MonadFlags Rn where
    askFlags = liftKZC askFlags
    localFlags fs m = Rn $ \r -> unRn (localFlags fs m) r

instance MonadTrace Rn where
    asksTraceDepth = liftKZC asksTraceDepth
    localTraceDepth d m = Rn $ \r -> unRn (localTraceDepth d m) r

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
