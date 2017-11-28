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

import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.Types
import qualified KZC.Expr.Smart as E
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
    , structs    = Map.fromList [(structName s, s) | s <- builtinStructs]
    , cstructs   = Map.fromList [(E.structName s, s) | s <- builtinEStructs]
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , tyVarTypes = Map.empty
    , envMtvs    = Set.empty
    , valCtxType = error "valCtxType: not yet defined"
    }
  where
    builtinStructs :: [StructDef]
    builtinStructs =
        [ StructDef "Complex" [(a, num)] [("re", tyVarT a), ("im", tyVarT a)] noLoc
        , complexType "complex"   intT
        , complexType "complex8"  int8T
        , complexType "complex16" int16T
        , complexType "complex32" int32T
        , complexType "complex64" int64T
        ]
      where
        a :: TyVar
        a = "a"

        num :: Kind
        num = TauK (R (traits [NumR]))

    complexType :: Z.Struct -> Type -> StructDef
    complexType s tau = TypeDef s [] (structT "Complex" [tau]) noLoc

    builtinEStructs :: [E.StructDef]
    builtinEStructs = [complexEStructDef]

    complexEStructDef :: E.StructDef
    complexEStructDef = E.StructDef "Complex" [(a, num)] [("re", E.tyVarT a), ("im", E.tyVarT a)] noLoc
      where
        a :: E.TyVar
        a = "a"

        num :: E.Kind
        num = E.TauK (E.traits [NumR])

data TiState = TiState
    { valctx :: E.Exp -> E.Exp }

defaultTiState :: TiState
defaultTiState = TiState
    { valctx = error "valctx: not yet defined" }
