{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}

-- |
-- Module      :  KZC.Optimize.Eval.Monad
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval.Monad (
    EvalM
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))

import KZC.Config (MonadConfig)
import KZC.Core.Lint (MonadTc, MonadTcRef)
import KZC.Util.Error (MonadErr)
import KZC.Util.Trace (MonadTrace)
import KZC.Util.Uniq (MonadUnique)

data EvalEnv l (m :: * -> *)

data EvalState l (m :: * -> *)

newtype EvalM l m a = EvalM { unEvalM :: ReaderT (EvalEnv l m) (StateT (EvalState l m) m) a }

instance Monad m => Applicative (EvalM l m) where
instance Functor m => Functor (EvalM l m) where
instance Monad m => Monad (EvalM l m) where
instance MonadException m => MonadException (EvalM l m) where
instance MonadErr m => MonadErr (EvalM l m) where
instance MonadConfig m => MonadConfig (EvalM l m) where
instance MonadUnique m => MonadUnique (EvalM l m) where
instance MonadTrace m => MonadTrace (EvalM l m) where
instance MonadTc m => MonadTc (EvalM l m) where
instance MonadTcRef m => MonadTcRef (EvalM l m) where
