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
    forallST,
    unSTC,
    funT,
    unFunT,
    forallT,

    isNatK,

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

    natT,

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
    asintE,
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

arrT :: Type -> Type -> Type
arrT nat tau = ArrT nat tau l
  where
    l :: SrcLoc
    l = nat `srcspan` tau

arrKnownT :: Int -> Type -> Type
arrKnownT i tau = ArrT (NatT i l) tau l
  where
    l :: SrcLoc
    l = srclocOf tau

structT :: Struct -> Type
structT struct = StructT struct (srclocOf struct)

stT :: Omega -> Type -> Type -> Type -> Type
stT omega s a b = ST omega s a b (omega `srcspan` s `srcspan` a `srcspan` b)

forallST :: [TyVar] -> Omega -> Type -> Type -> Type -> SrcLoc -> Type
forallST [] omega s a b l =
    ST omega s a b l

forallST alphas omega s a b l =
    ForallT (alphas `zip` repeat TauK) (ST omega s a b l) l

unSTC :: Type -> Type
unSTC (ForallT _ tau@ST{} _) = unSTC tau
unSTC (ST (C tau) _ _ _ _)   = tau
unSTC tau                    = tau

funT :: [(TyVar, Kind)] -> [Type] -> Type -> SrcLoc -> Type
funT []   taus tau l = FunT taus tau l
funT tvks taus tau l = ForallT tvks (FunT taus tau l) l

unFunT :: Monad m => Type -> m ([(TyVar, Kind)], [Type], Type)
unFunT (ForallT tvks (FunT taus tau _) _) = return (tvks, taus, tau)
unFunT (FunT taus tau _)                  = return ([], taus, tau)
unFunT _                                  = fail "unFunT: not a function"

forallT :: [(TyVar, Kind)] -> Type -> Type
forallT []   tau = tau
forallT tvks tau = ForallT tvks tau (map fst tvks `srcspan` tau)

-- | Return 'True' if a kind is kind Nat
isNatK :: Kind -> Bool
isNatK NatK{} = True
isNatK _      = False

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
isSTUnitT (ForallT _ tau@ST{} _)   = isSTUnitT tau
isSTUnitT (ST (C UnitT{}) _ _ _ _) = True
isSTUnitT _                        = False

-- | @'isCompT' tau@ returns 'True' if @tau@ is a computation, @False@ otherwise.
isCompT :: Type -> Bool
isCompT (ForallT _ tau@ST{} _) = isCompT tau
isCompT ST{}                   = True
isCompT _                      = False

-- | Return 'True' if the type is pure.
isPureT :: Type -> Bool
isPureT (ForallT _ tau@ST{} _) = isPureT tau
isPureT ST{}                   = False
isPureT _                      = True

-- | @'isPureishT' tau@ returns 'True' if @tau@ is a "pureish" computation, @False@
-- otherwise. A pureish computation may use references, but it may not take or
-- emit, so it has type @forall s a b . ST omega s a b@.
isPureishT :: Type -> Bool
isPureishT (ForallT tvks (ST _ (TyVarT s _) (TyVarT a _) (TyVarT b _) _) _) =
    alphas' == alphas
  where
    alphas, alphas' :: [TyVar]
    alphas  = sort $ map fst tvks
    alphas' = sort [s, a, b]

isPureishT (ForallT _ ST{} _) =
    False

isPureishT ST{} =
    False

isPureishT _ =
    True

structName :: StructDef -> Struct
structName (StructDef s _ _) = s

splitArrT :: Monad m => Type -> m (Type, Type)
splitArrT (ArrT nat tau _) =
    return (nat, tau)

splitArrT tau =
    faildoc $ text "Expected array type, but got:" <+> ppr tau

natT :: Integral a => a -> Type
natT x = NatT (fromIntegral x) noLoc

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
castE tau (ConstE c l) | Just c' <- liftCast tau c =
    ConstE c' l

castE tau e = UnopE (Cast tau) e (srclocOf e)

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integral a => a -> Exp
intE i = ConstE (intC i) noLoc

uintE :: Integral a => a -> Exp
uintE i = ConstE (uintC i) noLoc

-- | Create an integer constant expression at the given integer type.
asintE :: Integral a => Type -> a -> Exp
asintE (FixT ip l) i = ConstE (FixC ip (fromIntegral i)) l
asintE tau         _ = errordoc $ text "Expected integer type but got:" <+> ppr tau

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
