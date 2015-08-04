{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.State
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.State (
    TiEnv(..),
    defaultTiEnv,

    TiState(..),
    defaultTiState
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Language.Core.Syntax as C
import qualified Language.Ziria.Syntax as Z

import KZC.Check.Types
import KZC.Error

data TiEnv = TiEnv
    { errctx     :: ![ErrorContext]
    , nestdepth  :: {-# UNPACK #-} !Int
    , curexp     :: Maybe Z.Exp
    , isrvalctx  :: {-# UNPACK #-} !Bool
    , structs    :: !(Map Z.Struct Struct)
    , varTypes   :: !(Map Z.Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , tyVarInsts :: !(Map TyVar Type)
    , iVars      :: !(Map IVar Kind)
    , envMtvs    :: !(Set MetaTv)
    }

defaultTiEnv :: TiEnv
defaultTiEnv = TiEnv
    { errctx     = []
    , nestdepth  = 0
    , curexp     = Nothing
    , isrvalctx  = False
    , structs    = Map.empty
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , tyVarInsts = Map.empty
    , iVars      = Map.empty
    , envMtvs    = Set.empty
    }

data TiState = TiState
    { rvalctx :: C.Exp -> C.Exp }

defaultTiState :: TiState
defaultTiState = TiState
    { rvalctx = id }
