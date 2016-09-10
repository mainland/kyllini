{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  KZC.Check.Smart
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check.Smart (
    tyVarT,
    metaT,

    unitT,
    boolT,
    bitT,
    intT,
    int8T,
    int16T,
    int32T,
    int64T,
    refT,
    arrT,
    stT,
    cT,
    funT,

    structName,

    isUnitT,
    isRefT,
    isPureT,
    isPureishT
  ) where

import Data.Loc
import Data.List (sort)

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Types
import KZC.Platform

tyVarT :: TyVar -> Type
tyVarT tv@(TyVar n) = TyVarT tv (srclocOf n)

metaT :: MetaTv -> Type
metaT mtv = MetaT mtv noLoc

unitT :: Type
unitT = UnitT noLoc

boolT :: Type
boolT = BoolT noLoc

bitT :: Type
bitT = FixT (U 1) noLoc

intT :: Type
intT = FixT (I dEFAULT_INT_WIDTH) noLoc

int8T :: Type
int8T = FixT (I 8) noLoc

int16T :: Type
int16T = FixT (I 16) noLoc

int32T :: Type
int32T = FixT (I 32) noLoc

int64T :: Type
int64T = FixT (I 64) noLoc

refT :: Type -> Type
refT tau = RefT tau (srclocOf tau)

arrT :: Type -> Type -> Type
arrT iota tau = ArrT iota tau (iota `srcspan` tau)

stT :: Type -> Type -> Type -> Type -> Type
stT omega sigma alpha beta =
    ST [] omega sigma alpha beta (omega `srcspan` sigma `srcspan` alpha `srcspan` beta)

cT :: Type -> Type
cT nu = C nu (srclocOf nu)

funT :: [Type] -> Type -> Type
funT taus tau = FunT [] taus tau (taus `srcspan` tau)

structName :: StructDef -> Z.Struct
structName (StructDef s _ _) = s

isUnitT :: Type -> Bool
isUnitT UnitT{} = True
isUnitT _       = False

isRefT :: Type -> Bool
isRefT RefT{} = True
isRefT _      = False

-- | Return 'True' if the type is pure.
isPureT :: Type -> Bool
isPureT ST{} = False
isPureT _    = True

-- | @'isPureishT' tau@ returns 'True' if @tau@ is a "pureish" computation,
-- @False@ otherwise. A pureish computation may use references, but it may not
-- take or emit, so it has type @forall s a b . ST omega s a b@.
isPureishT :: Type -> Bool
isPureishT (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) | sort [s,a,b] == sort [s',a',b'] =
    True

isPureishT ST{} =
    False

isPureishT _ =
    True
