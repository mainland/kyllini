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

tyVarT :: TyVar -> Type
tyVarT tv@(TyVar n) = TyVarT tv (srclocOf n)

refT :: Type -> Type
refT tau = RefT tau (srclocOf tau)

stT :: Type -> Type -> Type -> Type
stT omega alpha beta = ST omega alpha beta (omega `srcspan` alpha `srcspan` beta)
