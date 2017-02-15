{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.State
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check.State (
    TiEnv(..),
    defaultTiEnv,

    TiState(..),
    defaultTiState
  ) where

import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.Types
import qualified KZC.Expr.Syntax as E

data TiEnv = TiEnv
    { curexp     :: Maybe Z.Exp
    , structs    :: !(Map Z.Struct StructDef)
    , varTypes   :: !(Map Z.Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , envMtvs    :: !(Set MetaTv)
    , valCtxType :: Type
    }

defaultTiEnv :: TiEnv
defaultTiEnv = TiEnv
    { curexp     = Nothing
    , structs    = Map.fromList [(structName s, s) | s <- builtinStructs]
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , envMtvs    = Set.empty
    , valCtxType = error "valCtxType: not yet defined"
    }

data TiState = TiState
    { valctx :: E.Exp -> E.Exp }

defaultTiState :: TiState
defaultTiState = TiState
    { valctx = error "valctx: not yet defined" }

builtinStructs :: [StructDef]
builtinStructs =
    [ complexStruct "complex"   intT
    , complexStruct "complex8"  int8T
    , complexStruct "complex16" int16T
    , complexStruct "complex32" int32T
    , complexStruct "complex64" int64T ]
  where
    complexStruct :: Z.Struct -> Type -> StructDef
    complexStruct s tau =
        StructDef s [("im", tau), ("re", tau)] noLoc
