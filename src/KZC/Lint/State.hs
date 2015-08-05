{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Lint.State
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Lint.State (
    TcEnv(..),
    defaultTcEnv,

    TcState(..),
    defaultTcState
  ) where

import Data.Map (Map)
import qualified Data.Map as Map

import Language.Core.Syntax

import KZC.Error

data TcEnv = TcEnv
    { errctx     :: ![ErrorContext]
    , nestdepth  :: {-# UNPACK #-} !Int
    , curexp     :: Maybe Exp
    , structs    :: !(Map Struct [(Field, Type)])
    , varTypes   :: !(Map Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , iVars      :: !(Map IVar Kind)
    }

defaultTcEnv :: TcEnv
defaultTcEnv = TcEnv
    { errctx     = []
    , nestdepth  = 0
    , curexp     = Nothing
    , structs    = Map.empty
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , iVars      = Map.empty
    }

data TcState = TcState ()

defaultTcState :: TcState
defaultTcState = TcState ()
