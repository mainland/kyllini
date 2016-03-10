{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  KZC.Optimize.Eval.Monad
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval.Val (
    Val(..),
    Ref(..),
    VarPtr,
    Heap,

    isTrue,
    isFalse,
    isZero,
    isOne,

    isValue,
    liftBool,
    liftBool2,
    liftEq,
    liftOrd,
    liftNum,
    liftNum2,
    liftBits,
    liftBits2,
    liftShift,

    ToExp(..),
    ToComp(..)
  ) where

import Control.Applicative ((<$>))
import Data.Bits
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Ratio (numerator)
import Data.String (fromString)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Label
import {-# SOURCE #-} KZC.Optimize.Eval.Monad (EvalM)
import qualified KZC.Optimize.Eval.PArray as P
import KZC.Platform

type Theta = Map Var Var

data Val a where
    UnknownV :: Val Exp

    UnitV   :: Val Exp
    BoolV   :: !Bool -> Val Exp
    FixV    :: !Scale -> !Signedness -> !W -> !BP -> !Rational -> Val Exp
    FloatV  :: !FP -> !Rational -> Val Exp
    StringV :: !String -> Val Exp
    StructV :: !Struct -> !(Map Field (Val Exp)) -> Val Exp
    ArrayV  :: !(P.PArray (Val Exp)) -> Val Exp

    -- | An element of an array
    IdxV :: Val Exp -> Val Exp -> Val Exp

    -- | An array slice
    SliceV :: Val Exp -> Val Exp -> Int -> Val Exp

    -- | A Reference
    RefV :: Ref -> Val Exp

    -- | A residual expression.
    ExpV :: Exp -> Val Exp

    -- | A value returned from a monadic action. We need to wrap it in a
    -- 'ReturnV' constructor so that we can convert it to a type-correct
    -- expression later.
    ReturnV :: Val Exp -> Val Exp

    -- | A residual command that cannot be fully evaluated. The 'Heap' argument
    -- is the state of the heap right before the residual expression is
    -- executed.
    CmdV :: Heap -> Exp -> Val Exp

    -- | A function closure
    FunClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM (Val Exp)) -> Val Exp

    -- | A value returned from a computation.
    CompReturnV :: Val Exp -> Val LComp

    -- | A residual computation.
    CompV :: Heap -> [LStep] -> Val LComp

    -- | A computation or computation function we know nothing about except its name.
    CompVarV :: Var -> Val LComp

    -- | A computation closure.
    CompClosV :: !Theta -> Type -> !(EvalM (Val LComp)) -> Val LComp

    -- | A computation function closure.
    FunCompClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM (Val LComp)) -> Val LComp

deriving instance Eq (Val a)
deriving instance Ord (Val a)
deriving instance Show (Val a)

instance Num (Val Exp) where
    x + y | isZero x  = y
          | isZero y  = x
          | otherwise = liftNum2 Add (+) x y

    x - y | isZero x  = - y
          | isZero y  = x
          | otherwise = liftNum2 Sub (-) x y

    x * y | isOne x   = y
          | isOne y   = x
          | otherwise = liftNum2 Mul (*) x y

    negate x = liftNum Neg negate x

    fromInteger i = FixV I S dEFAULT_INT_WIDTH (BP 0) (fromInteger i)

    abs _ = error "Val: abs undefined"

    signum _ = error "Val: signum undefined"

data Ref = VarR Var VarPtr
         | IdxR Ref (Val Exp) (Maybe Int)
         | ProjR Ref Field
  deriving (Eq, Ord, Show)

type VarPtr = Int

type Heap = IntMap (Val Exp)

isTrue :: Val Exp -> Bool
isTrue (BoolV True) = True
isTrue _            = False

isFalse :: Val Exp -> Bool
isFalse (BoolV False) = True
isFalse _             = False

isZero :: Val Exp -> Bool
isZero (FixV _ _ _ _ 0) = True
isZero (FloatV _ 0)     = True
isZero _                = False

isOne :: Val Exp -> Bool
isOne (FixV _ _ _ _ 1) = True
isOne (FloatV _ 1)     = True
isOne _                = False

-- | Return 'True' if a 'Val Exp' is actually a value and 'False'
-- otherwise.
isValue :: Val Exp -> Bool
isValue UnitV            = True
isValue (BoolV {})       = True
isValue (FixV {})        = True
isValue (FloatV {})      = True
isValue (StringV {})     = True
isValue (StructV _ flds) = all isValue (Map.elems flds)
isValue (ArrayV vals)    = isValue (P.defaultValue vals) &&
                           all (isValue . snd) (P.nonDefaultValues vals)
isValue _                = False

liftBool :: Unop -> (Bool -> Bool) -> Val Exp -> Val Exp
liftBool _ f (BoolV b) =
    BoolV (f b)

liftBool op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftBool2 :: Binop -> (Bool -> Bool -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftBool2 _ f (BoolV x) (BoolV y) =
    BoolV (f x y)

liftBool2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftEq :: Binop -> (forall a . Eq a => a -> a -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftEq _ f val1 val2 | isValue val1 && isValue val2 =
    BoolV (f val1 val2)

liftEq op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftOrd :: Binop -> (forall a . Ord a => a -> a -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftOrd _ f val1 val2 | isValue val1 && isValue val2 =
    BoolV (f val1 val2)

liftOrd op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftNum :: Unop -> (forall a . Num a => a -> a) -> Val Exp -> Val Exp
liftNum _ f (FixV sc s w bp r) =
    FixV sc s w bp (f r)

liftNum _ f (FloatV fp r) =
    FloatV fp (f r)

liftNum op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftNum2 :: Binop -> (forall a . Num a => a -> a -> a) -> Val Exp -> Val Exp -> Val Exp
liftNum2 _ f (FixV sc s w bp r1) (FixV _ _ _ _ r2) =
    FixV sc s w bp (f r1 r2)

liftNum2 _ f (FloatV fp r1) (FloatV _ r2) =
    FloatV fp (f r1 r2)

liftNum2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftBits :: Unop -> (forall a . Bits a => a -> a) -> Val Exp -> Val Exp
liftBits _ f (FixV sc s w (BP 0) r) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r)))

liftBits op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftBits2 :: Binop -> (forall a . Bits a => a -> a -> a) -> Val Exp -> Val Exp -> Val Exp
liftBits2 _ f (FixV sc s w (BP 0) r1) (FixV _ _ _ _ r2) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r1) (numerator r2)))

liftBits2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftShift :: Binop -> (forall a . Bits a => a -> Int -> a) -> Val Exp -> Val Exp -> Val Exp
liftShift _ f (FixV sc s w (BP 0) r1) (FixV _ _ _ _ r2) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r1) (fromIntegral (numerator r2))))

liftShift op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

class ToExp a where
    toExp :: a -> Exp

instance ToExp (Val Exp) where
    toExp UnknownV =
        errordoc $ text "toExp: Cannot convert unknown value to expression"

    toExp UnitV =
        constE UnitC

    toExp (BoolV f) =
        constE $ BoolC f

    toExp (FixV sc s w bp r) =
        constE $ FixC sc s w bp r

    toExp (FloatV fp r) =
        constE $ FloatC fp r

    toExp (StringV s) =
        constE $ StringC s

    toExp (StructV s flds) =
        structE s (fs `zip` map toExp vals)
      where
        fs :: [Field]
        vals :: [Val Exp]
        (fs, vals) = unzip $ Map.assocs flds

    toExp (ArrayV vvals) =
        arrayE (map toExp vals)
      where
        vals :: [Val Exp]
        vals = P.toList vvals

    toExp (IdxV arr i) =
        idxE (toExp arr) (toExp i)

    toExp (SliceV arr start len) =
        sliceE (toExp arr) (toExp start) len

    toExp (RefV r) =
        toExp r

    toExp (ReturnV v) =
        returnE (toExp v)

    toExp (ExpV e) =
        e

    toExp (CmdV _ e) =
        e

    toExp val =
        errordoc $ text "toExp: Cannot convert value to expression:" <+> ppr val

instance ToExp Ref where
    toExp (VarR v _) =
        varE v

    toExp (IdxR r start len) =
        IdxE (toExp r) (toExp start) len noLoc

    toExp (ProjR r f) =
        ProjE (toExp r) f noLoc

class ToComp a where
    toComp :: a -> EvalM LComp
    toComp x = Comp <$> toSteps x

    toSteps :: a -> EvalM [LStep]

instance ToComp (Val LComp) where
    toSteps (CompReturnV val) =
        unComp <$> returnC (toExp val)

    toSteps (CompV _ steps) =
        return steps

    toSteps (CompVarV v) =
        unComp <$> varC v

    toSteps val =
        faildoc $ text "toSteps: Cannot convert value to steps:" <+> ppr val

instance Eq (EvalM (Val a)) where
    (==) = error "EvalM incomparable"

instance Ord (EvalM (Val a)) where
    compare = error "EvalM incomparable"

instance Show (EvalM (Val a)) where
    show _ = "<evaluation action>"

instance Pretty (Val a) where
    ppr UnknownV         = text "<unknown>"
    ppr val@UnitV        = ppr (toExp val)
    ppr val@(BoolV {})   = ppr (toExp val)
    ppr val@(FixV {})    = ppr (toExp val)
    ppr val@(FloatV {})  = ppr (toExp val)
    ppr val@(StringV {}) = ppr (toExp val)
    ppr val@(StructV {}) = ppr (toExp val)
    ppr val@(ArrayV {})  = ppr (toExp val)
    ppr val@(IdxV {})    = ppr (toExp val)
    ppr val@(SliceV {})  = ppr (toExp val)
    ppr (RefV ref)       = ppr ref
    ppr val@(ExpV {})    = ppr (toExp val)
    ppr val@(ReturnV {}) = ppr (toExp val)

    ppr (CmdV h e) =
        nest 2 $ pprPrec appPrec1 e <+> text "with heap" <+/> pprHeap h

    ppr (FunClosV _env ivs vs tau_ret _) =
        langle <> text "fun" <+> ppr ivs <+> ppr vs <+> colon <+> ppr tau_ret <> rangle

    ppr (CompReturnV val) =
        ppr ([ReturnC (fromString "" :: Label) (toExp val) noLoc])

    ppr (CompV h c) =
        nest 2 $ ppr c <> nest (-2) (line <> text "with heap") <+/> pprHeap h

    ppr (CompVarV v) =
        ppr v

    ppr (CompClosV _ tau_ret _) =
        langle <> text "computation" <+> colon <+> ppr tau_ret <> rangle

    ppr (FunCompClosV _env ivs vs tau_ret _) =
        langle <> text "fun comp" <+> ppr ivs <+> ppr vs <+> colon <+> ppr tau_ret <> rangle

instance Pretty Ref where
    ppr = string . show

pprHeap :: Heap -> Doc
pprHeap m = braces $ commasep (map ppr (IntMap.assocs m))
