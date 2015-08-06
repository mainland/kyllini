-- |
-- Module      : Language.Ziria.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Ziria.Smart (
    mkVar,
    mkField,
    mkStruct,

    varE,
    stmsE,
    cmdsE,
    letC
  ) where

import Data.Loc

import Language.Ziria.Syntax

import KZC.Name

mkVar :: Name -> Var
mkVar n = Var n

mkField :: Name -> Field
mkField n = Field n

mkStruct :: Name -> Struct
mkStruct n = Struct n

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

stmsE :: [Stm] -> Exp
stmsE stms = StmE stms (srclocOf stms)

cmdsE :: [Cmd] -> Exp
cmdsE cmds = CmdE cmds (srclocOf cmds)

letC :: CompLet -> Cmd
letC l = LetC l (srclocOf l)
