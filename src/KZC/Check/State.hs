{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.State
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

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

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Types
import qualified KZC.Expr.Syntax as E

data TiEnv = TiEnv
    { curexp     :: Maybe Z.Exp
    , structs    :: !(Map Z.Struct StructDef)
    , cstructs   :: !(Map E.Struct E.StructDef)
    , varTypes   :: !(Map Z.Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , tyVarTypes :: !(Map TyVar Type)
    , envMtvs    :: !(Set MetaTv)
    , valCtxType :: Type
    }

defaultTiEnv :: TiEnv
defaultTiEnv = TiEnv
    { curexp     = Nothing
    , structs    = Map.empty
    , cstructs   = Map.empty
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , tyVarTypes = Map.empty
    , envMtvs    = Set.empty
    , valCtxType = error "valCtxType: not yet defined"
    }

data TiState = TiState
    { valctx :: E.Exp -> E.Exp }

defaultTiState :: TiState
defaultTiState = TiState
    { valctx = error "valctx: not yet defined" }
