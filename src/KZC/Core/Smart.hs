-- |
-- Module      : KZC.Core.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Smart where

import Control.Applicative
import Data.List (sort)
import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Core.Syntax
import KZC.Name
import KZC.Platform
import KZC.Uniq

mkUniqVar :: (Located a, Applicative m, MonadUnique m) => String -> a -> m Var
mkUniqVar s l = Var <$> mkUniqName s (locOf l)

mkVar :: String -> Var
mkVar s = Var (mkName s noLoc)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

castE :: Type -> Exp -> Exp
castE tau e = UnopE (Cast tau) e (srclocOf e)

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integer -> Exp
intE i = ConstE (FixC I S dEFAULT_INT_WIDTH 0 (fromIntegral i)) noLoc

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

letE :: Decl -> Exp -> Exp
letE d e = LetE d e (d `srcspan` e)

callE :: Var -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

returnE :: Exp -> Exp
returnE e = ReturnE AutoInline e (srclocOf e)

bindE :: Var -> Type -> Exp -> Exp -> Exp
bindE v tau e1 e2 = BindE (TameV v) tau e1 e2 (v `srcspan` e1 `srcspan` e2)

seqE :: Type -> Exp -> Exp -> Exp
seqE tau e1 e2 = BindE WildV tau e1 e2 (e1 `srcspan` e2)

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
bitT = FixT I U (W 0) (BP 0) noLoc

intT :: Type
intT = FixT I S dEFAULT_INT_WIDTH 0 noLoc

int8T :: Type
int8T = FixT I S 8 0 noLoc

int16T :: Type
int16T = FixT I S 16 0 noLoc

int32T :: Type
int32T = FixT I S 32 0 noLoc

int64T :: Type
int64T = FixT I S 64 0 noLoc

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

-- | @'isCompT' tau@ returns 'True' if @tau@ is a computation, @False@ otherwise.
isCompT :: Type -> Bool
isCompT (ST {}) = True
isCompT _       = False

-- | Return 'True' if the type is pure.
isPureT :: Type -> Bool
isPureT (ST {}) = False
isPureT _       = True

-- | @'isPureishT' tau@ returns 'True' if @tau@ is a "pureish" computation, @False@
-- otherwise. A pureish computation may use references, but it may not take or
-- emit, so it has type @forall s a b . ST omega s a b@.
isPureishT :: Type -> Bool
isPureishT (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) | sort [s,a,b] == sort [s',a',b'] =
    True

isPureishT (ST {}) =
    False

isPureishT _ =
    True

structName :: StructDef -> Struct
structName (StructDef s _ _) = s

splitArrT :: Monad m => Type -> m (Iota, Type)
splitArrT (ArrT iota tau _) =
    return (iota, tau)

splitArrT tau =
    faildoc $ text "Expected array type, but got:" <+> ppr tau
