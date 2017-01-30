{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}

-- |
-- Module      :  KZC.Optimize.Eval.Monad
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Eval.Monad (
    EvalM
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))

data EvalEnv l (m :: * -> *)

data EvalState l (m :: * -> *)

newtype EvalM l m a = EvalM { unEvalM :: ReaderT (EvalEnv l m) (StateT (EvalState l m) m) a }
