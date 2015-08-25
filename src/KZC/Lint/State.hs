{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Lint.State
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Lint.State (
    TcEnv(..),
    defaultTcEnv
  ) where

import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map

import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error

data TcEnv = TcEnv
    { errctx     :: ![ErrorContext]
    , nestdepth  :: {-# UNPACK #-} !Int
    , curexp     :: Maybe Exp
    , structs    :: !(Map Struct StructDef)
    , varTypes   :: !(Map Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , iVars      :: !(Map IVar Kind)
    , stIndTys   :: !(Maybe (Type, Type, Type))
    }

defaultTcEnv :: TcEnv
defaultTcEnv = TcEnv
    { errctx     = []
    , nestdepth  = 0
    , curexp     = Nothing
    , structs    = Map.fromList [(structName s, s) | s <- builtinStructs]
    , varTypes   = Map.empty
    , tyVars     = Map.empty
    , iVars      = Map.empty
    , stIndTys   = Nothing
    }

builtinStructs :: [StructDef]
builtinStructs =
    [ complexStruct "complex"   intT
    , complexStruct "complex8"  int8T
    , complexStruct "complex16" int16T
    , complexStruct "complex32" int32T
    , complexStruct "complex64" int64T ]
  where
    complexStruct :: Struct -> Type -> StructDef
    complexStruct s tau =
        StructDef s [("im", tau), ("re", tau)] noLoc
