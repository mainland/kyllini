{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Monad
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Monad (
    KZCEnv(..),
    defaultKZCEnv,

    KZC(..),
    evalKZC
  ) where

import Control.Monad.Exception
import Control.Monad.Primitive (PrimMonad(..),
                                RealWorld)
import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef
import Data.Map (Map)
import System.IO (stderr)
import Text.PrettyPrint.Mainland

import KZC.Check.State (TiEnv,
                        TiState,
                        defaultTiEnv,
                        defaultTiState)
import KZC.Compiler.Types
import KZC.Config
import KZC.Expr.Lint.Monad (TcEnv,
                            defaultTcEnv)
import KZC.Name
import KZC.Platform
import KZC.Rename.State (RnEnv,
                         defaultRnEnv)
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

data KZCEnv = KZCEnv
    { uniq       :: !(IORef Uniq)
    , tracedepth :: !Int
    , errctx     :: ![ErrorContext]
    , flags      :: !Config
    , platform   :: !Platform
    , rnenvref   :: !(IORef RnEnv)
    , tienvref   :: !(IORef TiEnv)
    , tistateref :: !(IORef TiState)
    , tcenvref   :: !(IORef TcEnv)
    , modref     :: !(IORef (Map ModuleName ModuleInfo))
    }

defaultKZCEnv :: (MonadIO m, MonadRef IORef m)
              => Config
              -> m KZCEnv
defaultKZCEnv fs = do
    u      <- newRef (Uniq 0)
    rneref <- newRef defaultRnEnv
    tieref <- newRef defaultTiEnv
    tisref <- newRef defaultTiState
    tceref <- newRef defaultTcEnv
    mref   <- newRef mempty
    return KZCEnv { uniq       = u
                  , tracedepth = 0
                  , errctx     = []
                  , flags      = fs
                  , platform   = Platform { platformIntWidth = 32 }
                  , rnenvref   = rneref
                  , tienvref   = tieref
                  , tistateref = tisref
                  , tcenvref   = tceref
                  , modref     = mref
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

evalKZC :: Config -> KZC a -> IO a
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
    throw = throwContextException (KZC . throw)

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
    askErrCtx     = asks errctx
    localErrCtx f = local $ \env -> env { errctx = f (errctx env) }

    displayWarning ex = liftIO $ hPutDocLn stderr $ ppr ex

instance MonadConfig KZC where
    askConfig     = asks flags
    localConfig f = local (\env -> env { flags = f (flags env) })

instance MonadPlatform KZC where
    askPlatform     = asks platform
    localPlatform f = local (\env -> env { platform = f (platform env) })

instance MonadTrace KZC where
    askTraceDepth     = asks tracedepth
    localTraceDepth f = local $ \env -> env { tracedepth = f (tracedepth env) }
