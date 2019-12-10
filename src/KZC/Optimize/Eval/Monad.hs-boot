{-# LANGUAGE KindSignatures #-}

-- |
-- Module      :  KZC.Optimize.Eval.Monad
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Eval.Monad (
    EvalM
  ) where

import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import Data.Kind (Type)

data EvalEnv l (m :: Type -> Type)

data EvalState l (m :: Type -> Type)

newtype EvalM l m a = EvalM { unEvalM :: ReaderT (EvalEnv l m) (StateT (EvalState l m) m) a }
