-- |
-- Module      : Language.Core.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Core.Smart where

import Control.Applicative
import Data.Loc

import Language.Core.Syntax

import KZC.Name
import KZC.Uniq

mkUniqVar :: (Located a, Applicative m, MonadUnique m) => String -> a -> m Var
mkUniqVar s l = Var <$> mkUniqName s (locOf l)

mkVar :: String -> Var
mkVar s = Var (mkName s noLoc)

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

callE :: Var -> [Exp] -> Exp
callE v es = CallE v [] es (v `srcspan` es)

returnE :: Exp -> Exp
returnE e = ReturnE e (srclocOf e)

bindE :: Var -> Exp -> Exp -> Exp
bindE v e1 e2 = BindE (BindV v) e1 e2 (v `srcspan` e1 `srcspan` e2)

seqE :: Exp -> Exp -> Exp
seqE e1 e2 = BindE WildV e1 e2 (e1 `srcspan` e2)

takeE :: Exp
takeE = TakeE noLoc

takesE :: Int -> Exp
takesE n = TakesE n noLoc

emitE :: Exp -> Exp
emitE e = EmitE e (srclocOf e)

emitsE :: Exp -> Exp
emitsE e = EmitsE e (srclocOf e)

repeatE :: Exp -> Exp
repeatE e = RepeatE e (srclocOf e)

unitT :: Type
unitT = UnitT noLoc

boolT :: Type
boolT = BoolT noLoc

bitT :: Type
bitT = BitT noLoc

intT :: W -> Type
intT w = IntT w noLoc
