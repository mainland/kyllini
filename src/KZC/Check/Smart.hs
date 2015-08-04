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

import KZC.Check.Types

unitT :: Type
unitT = UnitT noLoc

intT :: Type
intT = IntT W32 noLoc

tyVarT :: TyVar -> Type
tyVarT tv@(TyVar n) = TyVarT tv (srclocOf n)

arrT :: Type -> Type -> Type
arrT iota tau = ArrT iota tau (iota `srcspan` tau)

refT :: Type -> Type
refT tau = RefT tau (srclocOf tau)

stT :: Type -> Type -> Type -> Type
stT omega alpha beta =
    ST [] omega alpha beta (omega `srcspan` alpha `srcspan` beta)

cT :: Type -> Type
cT nu = C nu (srclocOf nu)

funT :: [Type] -> Type -> Type
funT taus tau = FunT [] taus tau (taus `srcspan` tau)
