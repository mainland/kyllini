-- |
-- Module      : Language.Ziria.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Ziria.Smart (
    varE,
    stmsE,
    cmdsE,
    letC
  ) where

import Data.Loc

import Language.Ziria.Syntax

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

stmsE :: [Stm] -> Exp
stmsE stms = StmE stms (srclocOf stms)

cmdsE :: [Cmd] -> Exp
cmdsE cmds = CmdE cmds (srclocOf cmds)

letC :: CompLet -> Cmd
letC l = LetC l (srclocOf l)
