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

intE :: Integer -> Exp
intE i = ConstE (IntC dEFAULT_INT_WIDTH i) noLoc

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

callE :: Exp -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

returnE :: Exp -> Exp
returnE e = ReturnE e (srclocOf e)

bindE :: Var -> Exp -> Exp -> Exp
bindE v e1 e2 = BindE (BindV v) e1 e2 (v `srcspan` e1 `srcspan` e2)

seqE :: Exp -> Exp -> Exp
seqE e1 e2 = BindE WildV e1 e2 (e1 `srcspan` e2)

takeE :: Type -> Exp
takeE tau = TakeE tau (srclocOf tau)

takesE :: Int -> Type -> Exp
takesE n tau = TakesE n tau (srclocOf tau)

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

intT :: Type
intT = IntT dEFAULT_INT_WIDTH noLoc

int8T :: Type
int8T = IntT W8 noLoc

int16T :: Type
int16T = IntT W16 noLoc

int32T :: Type
int32T = IntT W32 noLoc

int64T :: Type
int64T = IntT W64 noLoc

refT :: Type -> Type
refT tau = RefT tau noLoc

arrKnownT :: Int -> Type -> Type
arrKnownT i tau = ArrT (ConstI i l) tau l
  where
    l :: SrcLoc
    l = srclocOf tau

stT :: Omega -> Type -> Type -> Type -> Type
stT omega s a b = ST [] omega s a b (omega `srcspan` s `srcspan` a `srcspan` b)

tyVarT :: TyVar -> Type
tyVarT alpha = TyVarT alpha noLoc

structName :: StructDef -> Struct
structName (StructDef s _ _) = s
