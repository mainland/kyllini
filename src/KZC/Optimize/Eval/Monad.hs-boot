{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))

import KZC.Flags
import KZC.Monad
import KZC.Uniq

data EvalEnv l

data EvalState l

newtype EvalM l a = EvalM { unEvalM :: ReaderT (EvalEnv l) (StateT (EvalState l) KZC) a }

instance Functor (EvalM l) where
instance Applicative (EvalM l) where
instance Monad (EvalM l) where
instance MonadFlags (EvalM l) where
instance MonadUnique (EvalM l) where
