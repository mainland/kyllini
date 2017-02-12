{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Rename.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Rename.Monad (
    liftRn,
    RnEnv(..),

    Rn(..),
    runRn,

    inCompScope,
    inPureScope
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef

import KZC.Config
import KZC.Monad
import KZC.Rename.State
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

-- | Run a @Rn@ computation in the @KZC@ monad and update the @Rn@ environment.
liftRn :: forall a . ((a -> Rn a) -> Rn a) -> KZC a
liftRn m = do
    eref <- asks rnenvref
    env  <- readRef eref
    runRn (m' eref) env
  where
    m' :: IORef RnEnv -> Rn a
    m' eref =
        m $ \x -> do
        ask >>= writeRef eref
        return x

newtype Rn a = Rn { unRn :: ReaderT RnEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader RnEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace)

runRn :: Rn a -> RnEnv -> KZC a
runRn m = runReaderT (unRn m)

inCompScope :: Rn a -> Rn a
inCompScope = local $ \env -> env { compScope = True }

inPureScope :: Rn a -> Rn a
inPureScope = local $ \env -> env { compScope = False }
