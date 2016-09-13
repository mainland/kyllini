-- |
-- Module      : Language.Ziria.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Smart (
    mkVar,
    mkField,
    mkStruct,

    varE,
    stmsE,
    letS
  ) where

import Data.Loc

import Language.Ziria.Syntax

import KZC.Name

mkVar :: Name -> Var
mkVar = Var

mkField :: Name -> Field
mkField = Field

mkStruct :: Name -> Struct
mkStruct = Struct

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

stmsE :: [Stm] -> Exp
stmsE stms = StmE stms (srclocOf stms)

letS :: CompLet -> Stm
letS l = LetS l (srclocOf l)
