-- |
-- Module      :  KZC.Check
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check where

import qualified Language.Core.Syntax as C
import qualified Language.Ziria.Syntax as Z

import KZC.Check.Monad

checkProgram :: [Z.CompLet] -> Tc C.Exp
checkProgram _ = fail "Oh no!"
