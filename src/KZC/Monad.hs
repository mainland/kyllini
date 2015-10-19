{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Monad (
    KZCEnv(..),
    defaultKZCEnv,

    KZC(..),
    MonadKZC(..),
    evalKZC,
    mapKZC,
    kzcToIO,
    ioToKZC
  ) where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef
import Text.PrettyPrint.Mainland

import KZC.Check.State
import KZC.Error
import KZC.Flags
import KZC.Lint.State
import KZC.Trace
import KZC.Uniq

data KZCEnv = KZCEnv
    { uniq       :: !(IORef Uniq)
    , flags      :: !Flags
    , tracedepth :: !Int
    , errctx     :: ![ErrorContext]
    , tienvref   :: !(IORef TiEnv)
    , tistateref :: !(IORef TiState)
    , tcenvref   :: !(IORef TcEnv)
    }

defaultKZCEnv :: (MonadIO m, MonadRef IORef m)
              => Flags
              -> m KZCEnv
defaultKZCEnv fs = do
    u      <- newRef (Uniq 0)
    tieref <- newRef defaultTiEnv
    tisref <- newRef defaultTiState
    tceref <- newRef defaultTcEnv
    return KZCEnv { uniq       = u
                  , flags      = fs
                  , tracedepth = 0
                  , errctx     = []
                  , tienvref   = tieref
                  , tistateref = tisref
                  , tcenvref   = tceref
                  }

newtype KZC a = KZC { runKZC :: KZCEnv -> IO a }

evalKZC :: Flags -> KZC a -> IO a
evalKZC fs m = do
    env <- defaultKZCEnv fs
    runKZC m env

mapKZC :: forall a . (IO a -> IO a)
        -> KZC a
        -> KZC a
mapKZC f m = KZC $ \env -> f $ runKZC m env

kzcToIO :: KZC a -> KZCEnv -> IO a
kzcToIO m env = runKZC m env

ioToKZC :: IO a -> KZC a
ioToKZC m = KZC $ \_ -> m

class (MonadException m, MonadIO m) => MonadKZC m where
    liftKZC :: KZC a -> m a

instance Functor KZC where
    {-# INLINE fmap #-}
    fmap f x = x >>= return . f

instance Applicative KZC where
    {-# INLINE pure #-}
    pure = return
    {-# INLINE (<*>) #-}
    (<*>) = ap

instance Monad KZC where
    {-# INLINE (>>=) #-}
    m >>= k = KZC $ \env -> do
        a <- runKZC m env
        runKZC (k a) env

    {-# INLINE (>>) #-}
    m1 >> m2 = KZC $ \env -> do
        _ <- runKZC m1 env
        runKZC m2 env

    {-# INLINE return #-}
    return a = KZC $ \_ -> return a

    fail msg = throw (toException (FailException (string msg)))

instance MonadIO KZC where
    liftIO m = ioToKZC m

instance MonadRef IORef KZC where
    newRef a       = liftIO $ newIORef a
    readRef r      = liftIO $ readIORef r
    writeRef r a   = liftIO $ writeIORef r a
    modifyRef f r  = liftIO $ modifyIORef f r

instance MonadAtomicRef IORef KZC where
    {-# INLINE atomicModifyRef #-}
    atomicModifyRef r f = liftIO $ atomicModifyIORef r f

instance MonadReader KZCEnv KZC where
    ask        = KZC $ \env -> return env
    local f m  = KZC $ \env -> runKZC m (f env)
    reader f   = KZC $ \env -> return (f env)

instance MonadException KZC where
    throw e = liftIO $ throw e

    m `catch` h = KZC $ \s ->
      runKZC m s `catchContextException` \e -> runKZC (h e) s

instance MonadAsyncException KZC where
    mask act = KZC $ \s -> mask $ \restore ->
               runKZC (act (mapKZC restore)) s

instance MonadUnique KZC where
    {-# INLINE newUnique #-}
    newUnique = do
        ref <- asks uniq
        atomicModifyRef ref $ \(Uniq u) ->
            let u' = u + 1
            in
              u' `seq` (Uniq u', Uniq u)

instance MonadFlags KZC where
    askFlags = asks flags
    localFlags fs = local (\env -> env { flags = fs })

instance MonadTrace KZC where
    asksTraceDepth    = asks tracedepth
    localTraceDepth d = local (\env -> env { tracedepth = d })

instance MonadErr KZC where
    {-# INLINE askErrCtx #-}
    askErrCtx = asks errctx

    {-# INLINE localErrCtx #-}
    localErrCtx ctx m =
        local (\env -> env { errctx = ctx : errctx env }) m

    {-# INLINE warnIsError #-}
    warnIsError = asksFlags (testWarnFlag WarnError)
