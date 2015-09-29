-- |
-- Module      : KZC.Core.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Smart where

import Control.Applicative
import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Core.Syntax
import KZC.Name
import KZC.Uniq

mkUniqVar :: (Located a, Applicative m, MonadUnique m) => String -> a -> m Var
mkUniqVar s l = Var <$> mkUniqName s (locOf l)

mkVar :: String -> Var
mkVar s = Var (mkName s noLoc)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integer -> Exp
intE i = ConstE (IntC dEFAULT_INT_WIDTH i) noLoc

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

(.<.) :: Exp -> Exp -> Exp
e1 .<. e2 = BinopE Lt e1 e2 l
  where
    l :: SrcLoc
    l = e1 `srcspan` e2

(.<=.) :: Exp -> Exp -> Exp
e1 .<=. e2 = BinopE Le e1 e2 l
  where
    l :: SrcLoc
    l = e1 `srcspan` e2

letE :: Decl -> Exp -> Exp
letE d e = LetE d e (d `srcspan` e)

callE :: Var -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

returnE :: Exp -> Exp
returnE e = ReturnE AutoInline e (srclocOf e)

bindE :: Var -> Type -> Exp -> Exp -> Exp
bindE v tau e1 e2 = BindE (BindV v tau) e1 e2 (v `srcspan` e1 `srcspan` e2)

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
repeatE e = RepeatE AutoVect e (srclocOf e)

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

isComplexT :: Type -> Bool
isComplexT (StructT s _) = isComplexStruct s
isComplexT _             = False

isUnitT :: Type -> Bool
isUnitT (UnitT {}) = True
isUnitT _          = False

isFunT :: Type -> Bool
isFunT (FunT {}) = True
isFunT _         = False

isSTUnitT :: Type -> Bool
isSTUnitT (ST [] (C (UnitT {})) _ _ _ _) = True
isSTUnitT _                              = False

structName :: StructDef -> Struct
structName (StructDef s _ _) = s

splitArrT :: Monad m => Type -> m (Iota, Type)
splitArrT (ArrT iota tau _) =
    return (iota, tau)

splitArrT tau =
    faildoc $ text "Expected array type, but got:" <+> ppr tau
