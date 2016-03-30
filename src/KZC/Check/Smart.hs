{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  KZC.Check.Smart
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.Smart where

import Data.Loc

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Types
import KZC.Platform

unitT :: Type
unitT = UnitT noLoc

boolT :: Type
boolT = BoolT noLoc

bitT :: Type
bitT = BitT noLoc

intT :: Type
intT = FixT I S dEFAULT_INT_WIDTH 0 noLoc

int8T :: Type
int8T = FixT I S 8 0 noLoc

int16T :: Type
int16T = FixT I S 16 0 noLoc

int32T :: Type
int32T = FixT I S 32 0 noLoc

int64T :: Type
int64T = FixT I S 64 0 noLoc

tyVarT :: TyVar -> Type
tyVarT tv@(TyVar n) = TyVarT tv (srclocOf n)

arrT :: Type -> Type -> Type
arrT iota tau = ArrT iota tau (iota `srcspan` tau)

refT :: Type -> Type
refT tau = RefT tau (srclocOf tau)

stT :: Type -> Type -> Type -> Type -> Type
stT omega sigma alpha beta =
    ST [] omega sigma alpha beta (omega `srcspan` sigma `srcspan` alpha `srcspan` beta)

cT :: Type -> Type
cT nu = C nu (srclocOf nu)

funT :: [Type] -> Type -> Type
funT taus tau = FunT [] taus tau (taus `srcspan` tau)

structName :: StructDef -> Z.Struct
structName (StructDef s _ _) = s

isRefT :: Type -> Bool
isRefT (RefT {}) = True
isRefT _         = False

isUnitT :: Type -> Bool
isUnitT (UnitT {}) = True
isUnitT _          = False

isPureT :: Type -> Bool
isPureT (ST {}) = False
isPureT _       = True
