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
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Rename.Monad (
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

inCompScope :: Rn a -> Rn a
inCompScope = local $ \env -> env { compScope = True }

inPureScope :: Rn a -> Rn a
inPureScope = local $ \env -> env { compScope = False }
