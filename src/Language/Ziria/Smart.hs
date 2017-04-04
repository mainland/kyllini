-- |
-- Module      : Language.Ziria.Smart
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Smart (
    mkVar,
    mkTyVar,
    mkField,
    mkStruct,
    mkCall,

    varE,
    letDeclE,
    stmsE,
    letS
  ) where

import Data.Loc
import qualified Data.Map as Map

import Language.Ziria.Syntax
import Language.Ziria.Parser.Tokens (unopFunMap)

import KZC.Name

mkVar :: Name -> Var
mkVar = Var

mkTyVar :: Name -> TyVar
mkTyVar = TyVar

mkField :: Name -> Field
mkField = Field

mkStruct :: Name -> Struct
mkStruct = Struct

mkCall :: Name -> Maybe [Type] -> [Exp] -> SrcLoc -> Exp
mkCall f Nothing [e] l | Just op <- Map.lookup (nameSym f) unopFunMap =
    UnopE op e l

mkCall f taus es l =
    CallE (mkVar f) taus es l

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

letDeclE :: Decl -> Exp -> Exp
letDeclE decl e = LetDeclE decl e (decl `srcspan` e)

stmsE :: [Stm] -> Exp
stmsE stms = StmE stms (srclocOf stms)

letS :: Decl -> Stm
letS l = LetS l (srclocOf l)
