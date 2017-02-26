{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Expr.Smart
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Expr.Smart (
    tyVarT,

    unitT,
    boolT,
    bitT,
    intT,
    int8T,
    int16T,
    int32T,
    int64T,
    uintT,
    uint8T,
    uint16T,
    uint32T,
    uint64T,
    refT,
    unRefT,
    arrT,
    arrKnownT,
    structT,
    stT,
    unSTC,

    isBaseT,
    isUnitT,
    isBitT,
    isBitArrT,
    isComplexT,
    isFunT,
    isArrT,
    isArrOrRefArrT,
    isRefT,
    isSTUnitT,
    isCompT,
    isPureT,
    isPureishT,

    structName,

    splitArrT,

    constI,

    bitC,
    intC,
    uintC,
    arrayC,
    structC,

    isArrC,

    fromIntC,

    mkVar,

    notE,
    castE,
    unitE,
    intE,
    uintE,
    varE,
    letE,
    callE,
    derefE,
    returnE,
    bindE,
    seqE,
    takeE,
    takesE,
    emitE,
    emitsE,
    repeatE,
    repeatAnnE
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.List (sort)
import Data.Loc
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland

import KZC.Expr.Syntax
import KZC.Name
import KZC.Platform

tyVarT :: TyVar -> Type
tyVarT alpha = TyVarT alpha noLoc

unitT :: Type
unitT = UnitT noLoc

boolT :: Type
boolT = BoolT noLoc

bitT :: Type
bitT = FixT (U 1) noLoc

intT :: Type
intT = FixT (I dEFAULT_INT_WIDTH) noLoc

int8T :: Type
int8T = FixT (I 8) noLoc

int16T :: Type
int16T = FixT (I 16) noLoc

int32T :: Type
int32T = FixT (I 32) noLoc

int64T :: Type
int64T = FixT (I 64) noLoc

uintT :: Type
uintT = FixT (U dEFAULT_INT_WIDTH) noLoc

uint8T :: Type
uint8T = FixT (U 8) noLoc

uint16T :: Type
uint16T = FixT (U 16) noLoc

uint32T :: Type
uint32T = FixT (U 32) noLoc

uint64T :: Type
uint64T = FixT (U 64) noLoc

refT :: Type -> Type
refT tau = RefT tau noLoc

unRefT :: Type -> Type
unRefT (RefT tau _) = tau
unRefT tau          = tau

arrT :: Iota -> Type -> Type
arrT iota tau = ArrT iota tau l
  where
    l :: SrcLoc
    l = iota `srcspan` tau

arrKnownT :: Int -> Type -> Type
arrKnownT i tau = ArrT (ConstI i l) tau l
  where
    l :: SrcLoc
    l = srclocOf tau

structT :: Struct -> Type
structT struct = StructT struct (srclocOf struct)

stT :: Omega -> Type -> Type -> Type -> Type
stT omega s a b = ST [] omega s a b (omega `srcspan` s `srcspan` a `srcspan` b)

unSTC :: Type -> Type
unSTC (ST _ (C tau) _ _ _ _) = tau
unSTC tau                    = tau

-- | Return 'True' if a type is a base type.
isBaseT :: Type -> Bool
isBaseT UnitT{}  = True
isBaseT BoolT{}  = True
isBaseT FixT{}   = True
isBaseT FloatT{} = True
isBaseT _        = False

isUnitT :: Type -> Bool
isUnitT UnitT{} = True
isUnitT _       = False

isBitT :: Type -> Bool
isBitT (FixT (U 1) _) = True
isBitT _              = False

isBitArrT :: Type -> Bool
isBitArrT (ArrT _ tau _) = isBitT tau
isBitArrT _              = False

isComplexT :: Type -> Bool
isComplexT (StructT s _) = isComplexStruct s
isComplexT _             = False

isFunT :: Type -> Bool
isFunT FunT{} = True
isFunT _      = False

isArrT :: Type -> Bool
isArrT ArrT{} = True
isArrT _      = False

isArrOrRefArrT :: Type -> Bool
isArrOrRefArrT ArrT{}          = True
isArrOrRefArrT (RefT ArrT{} _) = True
isArrOrRefArrT _               = False

isRefT :: Type -> Bool
isRefT RefT{} = True
isRefT _      = False

isSTUnitT :: Type -> Bool
isSTUnitT (ST [] (C UnitT{}) _ _ _ _) = True
isSTUnitT _                           = False

-- | @'isCompT' tau@ returns 'True' if @tau@ is a computation, @False@ otherwise.
isCompT :: Type -> Bool
isCompT ST{} = True
isCompT _    = False

-- | Return 'True' if the type is pure.
isPureT :: Type -> Bool
isPureT ST{} = False
isPureT _    = True

-- | @'isPureishT' tau@ returns 'True' if @tau@ is a "pureish" computation, @False@
-- otherwise. A pureish computation may use references, but it may not take or
-- emit, so it has type @forall s a b . ST omega s a b@.
isPureishT :: Type -> Bool
isPureishT (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) | sort [s,a,b] == sort [s',a',b'] =
    True

isPureishT ST{} =
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

constI :: Integral a => a -> Iota
constI x = ConstI (fromIntegral x) noLoc

bitC :: Bool -> Const
bitC b = FixC (U 1) (if b then 1 else 0)

intC :: Integral i => i -> Const
intC i = FixC (I dEFAULT_INT_WIDTH) (fromIntegral i)

uintC :: Integral i => i -> Const
uintC i = FixC (U dEFAULT_INT_WIDTH) (fromIntegral i)

arrayC :: Vector Const -> Const
arrayC cs
  | n > 0 && V.all (== V.head cs) cs = ReplicateC n (V.head cs)
  | otherwise                         = ArrayC cs
  where
    n :: Int
    n = V.length cs

structC :: Struct -> [(Field, Const)] -> Const
structC = StructC

isArrC :: Const -> Bool
isArrC ArrayC{}     = True
isArrC ReplicateC{} = True
isArrC EnumC{}      = True
isArrC _            = False

fromIntC :: Monad m => Const -> m Int
fromIntC (FixC _ x) =
    return x

fromIntC _ =
    fail "fromIntC: not an integer"

mkVar :: String -> Var
mkVar s = Var (mkName s noLoc)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

castE :: Type -> Exp -> Exp
castE tau e = UnopE (Cast tau) e (srclocOf e)

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integral a => a -> Exp
intE i = ConstE (intC i) noLoc

uintE :: Integral a => a -> Exp
uintE i = ConstE (uintC i) noLoc

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

repeatAnnE :: VectAnn -> Exp -> Exp
repeatAnnE ann e = RepeatE ann e (srclocOf e)
