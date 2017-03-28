{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Optimize.LowerGenerators
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.LowerGenerators (
    lowerGenerators
  ) where

import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Primitive (PrimMonad(..))
import Control.Monad.Ref (MonadRef(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.IORef (IORef)
import Data.Loc (noLoc)

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Interp (compileAndRunGen)
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

newtype L m a = L { unL :: m a }
  deriving (Applicative, Functor, Monad, MonadIO,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadPlatform,
            MonadTrace,
            MonadTc)

deriving instance MonadRef IORef m => MonadRef IORef (L m)

deriving instance MonadTcRef m => MonadTcRef (L m)

instance PrimMonad m => PrimMonad (L m) where
  type PrimState (L m) = PrimState m
  primitive = L . primitive

instance MonadTrans L where
    lift = L

runL :: L m a -> m a
runL = unL

lowerGenerators :: MonadTcRef m => Program l -> m (Program l)
lowerGenerators = runL . programT

instance MonadTcRef m => TransformExp (L m) where
    expT (GenE e gs _) =
        ConstE <$> compileAndRunGen e gs <*> pure noLoc

    expT e =
        transExp e

instance MonadTcRef m => TransformComp l (L m) where
