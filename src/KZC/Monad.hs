{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Monad (
    KZCEnv(..),
    defaultKZCEnv,

    KZC(..),
    evalKZC,

    getPass,
    incPass
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception
import Control.Monad.Primitive (PrimMonad(..),
                                RealWorld)
import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef
import System.IO (stderr)
import Text.PrettyPrint.Mainland

import KZC.Check.State (TiEnv,
                        TiState,
                        defaultTiEnv,
                        defaultTiState)
import KZC.Core.Lint.Monad (TcEnv,
                            defaultTcEnv)
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq

data KZCEnv = KZCEnv
    { uniq       :: !(IORef Uniq)
    , tracedepth :: !Int
    , pass       :: !(IORef Int)
    , errctx     :: ![ErrorContext]
    , flags      :: !Flags
    , tienvref   :: !(IORef TiEnv)
    , tistateref :: !(IORef TiState)
    , tcenvref   :: !(IORef TcEnv)
    }

defaultKZCEnv :: (MonadIO m, MonadRef IORef m)
              => Flags
              -> m KZCEnv
defaultKZCEnv fs = do
    u      <- newRef (Uniq 0)
    p      <- newRef 0
    tieref <- newRef defaultTiEnv
    tisref <- newRef defaultTiState
    tceref <- newRef defaultTcEnv
    return KZCEnv { uniq       = u
                  , tracedepth = 0
                  , pass       = p
                  , errctx     = []
                  , flags      = fs
                  , tienvref   = tieref
                  , tistateref = tisref
                  , tcenvref   = tceref
                  }

newtype KZC a = KZC { unKZC :: ReaderT KZCEnv IO a }
    deriving (Functor, Applicative, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader KZCEnv)

instance PrimMonad KZC where
    type PrimState KZC = RealWorld
    primitive = KZC . primitive

runKZC :: KZC a -> KZCEnv -> IO a
runKZC = runReaderT . unKZC

evalKZC :: Flags -> KZC a -> IO a
evalKZC fs m = do
    env <- defaultKZCEnv fs
    runKZC m env

instance Monad KZC where
    {-# INLINE return #-}
    return a = KZC $ return a

    {-# INLINE (>>=) #-}
    m >>= f  = KZC $ unKZC m >>= unKZC  . f

    {-# INLINE (>>) #-}
    m1 >> m2 = KZC $ unKZC m1 >> unKZC m2

    fail msg = throw (FailException (string msg))

instance MonadException KZC where
    throw e = throwContextException (KZC . throw) e

    m `catch` h = KZC $ unKZC m `catchContextException` \e -> unKZC (h e)

instance MonadUnique KZC where
    {-# INLINE newUnique #-}
    newUnique = do
        ref <- asks uniq
        atomicModifyRef ref $ \(Uniq u) ->
            let u' = u + 1
            in
              u' `seq` (Uniq u', Uniq u)

instance MonadErr KZC where
    askErrCtx       = asks errctx
    localErrCtx f m = local (\env -> env { errctx = f (errctx env) }) m

    displayWarning ex = liftIO $ hPutDocLn stderr $ ppr ex

instance MonadFlags KZC where
    askFlags       = asks flags
    localFlags f m = local (\env -> env { flags = f (flags env) }) m

instance MonadTrace KZC where
    askTraceDepth     = asks tracedepth
    localTraceDepth f = local (\env -> env { tracedepth = f (tracedepth env) })

getPass :: KZC Int
getPass = asks pass >>= readRef

incPass :: KZC Int
incPass = do
    ref <- asks pass
    atomicModifyRef' ref (\i -> (i + 1, i))
