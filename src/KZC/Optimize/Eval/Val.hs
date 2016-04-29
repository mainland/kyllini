{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

    unitV,

    uintV,
    intV,
    fromIntV,

    zeroBitV,
    oneBitV,

    catV,

    idxV,
    sliceV,

    toBitsV,
    packValues,
    fromBitsV,
    unpackValues,

    bitcastV,

    complexV,
    uncomplexV,

    isTrue,
    isFalse,
    isZero,
    isOne,

    isValue,
    defaultValue,
    isDefaultValue,
    isKnown,

    ToExp(..),
    ToComp(..),
    toConst
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (foldM)
import Data.Binary.IEEE754 (floatToWord,
                            wordToFloat,
                            doubleToWord,
                            wordToDouble)
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
import KZC.Auto.Label
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Label
import {-# SOURCE #-} KZC.Optimize.Eval.Monad (EvalM)
import qualified KZC.Optimize.Eval.PArray as P

type Theta = Map Var Var

data Val l m a where
    UnknownV :: Val l m Exp

    ConstV  :: !Const -> Val l m Exp
    StructV :: !Struct -> !(Map Field (Val l m Exp)) -> Val l m Exp
    ArrayV  :: !(P.PArray (Val l m Exp)) -> Val l m Exp

    -- An element of an array
    IdxV :: Val l m Exp -> Val l m Exp -> Val l m Exp

    -- An array slice
    SliceV :: Val l m Exp -> Val l m Exp -> Int -> Val l m Exp

    -- A Reference
    RefV :: Ref l m -> Val l m Exp

    -- A residual expression.
    ExpV :: Exp -> Val l m Exp

    -- A value returned from a monadic action. We need to wrap it in a 'ReturnV'
    -- constructor so that we can convert it to a type-correct expression later.
    ReturnV :: Val l m Exp -> Val l m Exp

    -- A residual command that cannot be fully evaluated. The 'Heap' argument is
    -- the state of the heap right before the residual expression is executed.
    CmdV :: Heap l m -> Exp -> Val l m Exp

    -- A function closure
    FunClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM l m (Val l m Exp)) -> Val l m Exp

    -- A value returned from a computation.
    CompReturnV :: Val l m Exp -> Val l m (Comp l)

    -- A residual computation.
    CompV :: Heap l m -> [Step l] -> Val l m (Comp l)

    -- A computation or computation function we know nothing about except its
    -- name.
    CompVarV :: Var -> Val l m (Comp l)

    -- A computation closure.
    CompClosV :: !Theta -> Type -> !(EvalM l m (Val l m (Comp l))) -> Val l m (Comp l)

    -- A computation function closure.
    FunCompClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM l m (Val l m (Comp l))) -> Val l m (Comp l)

deriving instance Eq l => Eq (Val l m a)
deriving instance Ord l => Ord (Val l m a)
deriving instance Show l => Show (Val l m a)

instance IsLabel l => Num (Val l m Exp) where
    x + y = liftNum2 Add (+) x y
    x - y = liftNum2 Sub (-) x y
    x * y = liftNum2 Mul (*) x y

    negate x = liftNum Neg negate x

    fromInteger i = intV i

    abs _ = error "Val: abs undefined"

    signum _ = error "Val: signum undefined"

data Ref l m = VarR Var VarPtr
             | IdxR (Ref l m) (Val l m Exp) (Maybe Int)
             | ProjR (Ref l m) Field
  deriving (Eq, Ord, Show)

type VarPtr = Int

type Heap l m = IntMap (Val l m Exp)

unitV :: Val l m Exp
unitV  = ConstV UnitC

uintV :: Integral a => a -> Val l m Exp
uintV i = ConstV $ uintC i

intV :: Integral a => a -> Val l m Exp
intV i = ConstV $ intC i

fromIntV :: Val l m Exp -> Maybe Integer
fromIntV (ConstV (FixC I _ _ (BP 0) r)) =
    Just $ numerator r

fromIntV _ =
    Nothing

zeroBitV, oneBitV :: Val l m Exp
zeroBitV = ConstV $ FixC I U (W 1) (BP 0) 0
oneBitV  = ConstV $ FixC I U (W 1) (BP 0) 1

isTrue :: Val l m Exp -> Bool
isTrue (ConstV (BoolC b)) = b
isTrue _                  = False

isFalse :: Val l m Exp -> Bool
isFalse (ConstV (BoolC b)) = not b
isFalse _                  = False

isZero :: Val l m Exp -> Bool
isZero (ConstV (FixC _ _ _ _ 0)) = True
isZero (ConstV (FloatC _ 0))     = True
isZero _                         = False

isOne :: Val l m Exp -> Bool
isOne (ConstV (FixC _ _ _ _ 1)) = True
isOne (ConstV (FloatC _ 1))     = True
isOne _                         = False

-- | Return 'True' if a 'Val l m Exp' is actually a value and 'False'
-- otherwise.
isValue :: Val l m Exp -> Bool
isValue ConstV{}         = True
isValue (StructV _ flds) = all isValue (Map.elems flds)
isValue (ArrayV vals)    = isValue (P.defaultValue vals) &&
                           all (isValue . snd) (P.nonDefaultValues vals)
isValue _                = False

-- | Produce a default value of the given type.
defaultValue :: forall l m m' . (MonadTc m, MonadTc m')
             => Type
             -> m' (Val l m Exp)
defaultValue tau =
    go tau
  where
    go :: Type -> m' (Val l m Exp)
    go (UnitT {})         = return $ ConstV $ UnitC
    go (BoolT {})         = return $ ConstV $ BoolC False
    go (FixT sc s w bp _) = return $ ConstV $ FixC sc s w bp 0
    go (FloatT fp _)      = return $ ConstV $ FloatC fp 0
    go (StringT {})       = return $ ConstV $ StringC ""

    go (StructT s _) = do
        StructDef s flds _ <- lookupStruct s
        let (fs, taus)     =  unzip flds
        vals               <- mapM go taus
        return $ StructV s (Map.fromList (fs `zip` vals))

    go (ArrT (ConstI n _) tau _) = do
        val <- go tau
        return $ ArrayV (P.replicateDefault n val)

    go tau =
        faildoc $ text "Cannot generate default value for type" <+> ppr tau

-- | Given a type and a value, return 'True' if the value is the
-- default of that type and 'False' otherwise.
isDefaultValue :: Val l m Exp -> Bool
isDefaultValue (ConstV UnitC)            = True
isDefaultValue (ConstV (BoolC False))    = True
isDefaultValue (ConstV (FixC _ _ _ _ 0)) = True
isDefaultValue (ConstV (FloatC _ 0))     = True
isDefaultValue (ConstV (StringC ""))     = True
isDefaultValue (StructV _ flds)          = all isDefaultValue (Map.elems flds)
isDefaultValue (ArrayV vals)             = all isDefaultValue (P.toList vals)
isDefaultValue _                         = False

-- | Return 'True' if a 'Val' is completely known, even if it is a residual,
-- 'False' otherwise.
isKnown :: Val l m Exp -> Bool
isKnown UnknownV         = False
isKnown ConstV{}         = True
isKnown (StructV _ flds) = all isKnown (Map.elems flds)
isKnown (ArrayV vals)    = isKnown (P.defaultValue vals) &&
                           all (isKnown . snd) (P.nonDefaultValues vals)
isKnown (IdxV arr i)     = isKnown arr && isKnown i
isKnown (SliceV arr i _) = isKnown arr && isKnown i
isKnown ExpV{}           = True
isKnown _                = False

catV :: IsLabel l => Val l m Exp -> Val l m Exp -> Val l m Exp
catV (ArrayV vs1) (ArrayV vs2) =
    ArrayV $ P.fromList (P.defaultValue vs1) $
    P.toList vs2 ++ P.toList vs1

catV (ArrayV vs1) val2 | P.length vs1 == 0 =
    val2

catV val1 (ArrayV vs2) | P.length vs2 == 0 =
    val1

catV val1 val2 =
    ExpV $ catE (toExp val1) (toExp val2)

-- | Extract a slice of an array
idxV :: (IsLabel l, Applicative m, Monad m)
      => Val l m Exp -> Int -> m (Val l m Exp)
idxV (ArrayV vs) off = vs P.!? off
idxV val off         = return $ ExpV $ idxE (toExp val) (fromIntegral off)

-- | Extract a slice of an array
sliceV :: (IsLabel l, MonadTc m)
       => Val l m Exp
       -> Int
       -> Int
       -> EvalM l m (Val l m Exp)
sliceV (ArrayV vs) off len = ArrayV <$> P.slice off len vs
sliceV val off len         = return $ ExpV $ sliceE (toExp val) (fromIntegral off) len

toBitsV :: forall l m . (IsLabel l, MonadTc m)
       => Val l m Exp
       -> Type
       -> EvalM l m (Val l m Exp)
toBitsV val tau =
    go val tau
  where
    go :: Val l m Exp -> Type -> EvalM l m (Val l m Exp)
    go (ConstV UnitC) _ =
        return $ ArrayV $ P.replicateDefault 0 zeroBitV

    go (ConstV (BoolC f)) _ =
        toBitArr (fromIntegral (fromEnum f)) 1

    go (ConstV (FixC I U (W w) (BP 0) r)) _ =
        toBitArr (numerator r) w

    go (ConstV (FixC I S (W w) (BP 0) r)) _
        | r >= 0    = toBitArr (numerator r) w
        | otherwise = toBitArr (numerator r + 2^w) w

    go (ConstV (FloatC FP32 r)) _ =
        toBitArr (fromIntegral (floatToWord (fromRational r))) 32

    go(ConstV  (FloatC FP64 r)) _ =
        toBitArr (fromIntegral (doubleToWord (fromRational r))) 64

    go (StructV _ m) (StructT sname _) = do
        StructDef _ flds _ <- lookupStruct sname
        packValues [(m Map.! f, tau) | (f, tau) <- flds]

    go (ArrayV arr) (ArrT _ tau _) =
        packValues (P.toList arr `zip` repeat tau)

    go (ReturnV val) (ST _ (C tau) _ _ _ _) =
        toBitsV val tau

    go val tau = do
        w <- typeSize tau
        return $ ExpV $ bitcastE (arrKnownT w bitT) (toExp val)

    toBitArr :: Integer -> Int -> EvalM l m (Val l m Exp)
    toBitArr n w = ArrayV <$> (P.replicateDefault w zeroBitV P.// [(i,oneBitV) | i <- [0..w-1], n `testBit` i])

packValues :: forall l m . (IsLabel l, MonadTc m)
            => [(Val l m Exp, Type)]
            -> EvalM l m (Val l m Exp)
packValues vtaus =
    go emptyBitArr (reverse vtaus)
  where
    go :: Val l m Exp -> [(Val l m Exp, Type)] -> EvalM l m (Val l m Exp)
    go bits [] =
        return bits

    go bits ((x, tau):xs) = do
        x_bits <- toBitsV x tau
        go (bits `catV` x_bits) xs

    emptyBitArr :: Val l m Exp
    emptyBitArr = ArrayV $ P.fromList zeroBitV []

fromBitsV :: forall l m . (IsLabel l, MonadTc m)
          => Val l m Exp
          -> Type
          -> EvalM l m (Val l m Exp)
fromBitsV (ArrayV vs) tau =
    go vs tau
  where
    go :: P.PArray (Val l m Exp) -> Type -> EvalM l m (Val l m Exp)
    go _ (UnitT {}) =
        return $ ConstV UnitC

    go vs (BoolT {}) =
        ConstV . BoolC . toEnum . fromIntegral <$> fromBitArr vs

    go vs (FixT I U (W w) (BP 0) _) =
        ConstV . FixC I U (W w) (BP 0) . fromIntegral <$> fromBitArr vs

    go vs (FixT I S (W w) (BP 0) _) = do
        i <- fromBitArr vs
        return $ ConstV $
            if i < 2^(w-1)
            then FixC I S (W w) (BP 0) (fromIntegral i)
            else FixC I S (W w) (BP 0) (fromIntegral (i - 2^w))

    go vs (FloatT FP32 _) =
        ConstV . FloatC FP32 . toRational . wordToFloat . fromIntegral <$> fromBitArr vs

    go vs (FloatT FP64 _) =
        ConstV . FloatC FP64 . toRational . wordToDouble . fromIntegral <$> fromBitArr vs

    go vs (RefT tau _) =
        go vs tau

    go vs (StructT sname _) = do
        StructDef _ flds _ <- lookupStruct sname
        vals <- unpackValues (ArrayV vs) (map snd flds)
        return $ StructV sname (Map.fromList (map fst flds `zip` vals))

    go vs (ArrT (ConstI n _) tau _) = do
        vals <- unpackValues (ArrayV vs) (replicate n tau)
        dflt <- defaultValue tau
        return $ ArrayV $ P.fromList dflt vals

    go vs _ =
        return $ ExpV $ bitcastE tau (toExp (ArrayV vs))

    fromBitArr :: P.PArray (Val l m Exp) -> EvalM l m Integer
    fromBitArr vs = foldM set 0 $ reverse $ P.toList vs
      where
        set :: Integer -> Val l m Exp -> EvalM l m Integer
        set i (ConstV (FixC I U (W 1) (BP 0) 0)) = return $ i `shiftL` 1
        set i (ConstV (FixC I U (W 1) (BP 0) 1)) = return $ i `shiftL` 1 .|. 1
        set _ val                                = faildoc $ text "Not a bit:" <+> ppr val

fromBitsV val tau = do
    w <- typeSize tau
    return $ ExpV $ bitcastE (arrKnownT w bitT) (toExp val)

unpackValues :: forall l m . (IsLabel l, MonadTc m)
             => Val l m Exp
             -> [Type]
             -> EvalM l m [Val l m Exp]
unpackValues bits taus = do
    go 0 taus
  where
    go :: Int -> [Type] -> EvalM l m [Val l m Exp]
    go _ [] =
        return []

    go n (UnitT {}:taus) = do
        vals <- go n taus
        return $ ConstV UnitC : vals

    go n (tau:taus) = do
        w    <- typeSize tau
        slc  <- sliceV bits n w
        val  <- bitcastV slc (arrKnownT w bitT) tau
        vals <- go (n + w) taus
        return $ val : vals

-- | Bitcast a value from one type to another
bitcastV :: forall l m . (IsLabel l, MonadTc m)
         => Val l m Exp
         -> Type
         -> Type
         -> EvalM l m (Val l m Exp)
bitcastV val tau_from tau_to@(ArrT (ConstI n _) tau_elem _) | isBitT tau_elem = do
    n' <- typeSize tau_from
    if n' == n
      then toBitsV val tau_from
      else return $ ExpV $ bitcastE tau_to (toExp val)

bitcastV val (ArrT (ConstI n _) tau_elem _) tau_to | isBitT tau_elem = do
    n' <- typeSize tau_to
    if n' == n
      then fromBitsV val tau_to
      else return $ ExpV $ bitcastE tau_to (toExp val)

bitcastV val _ tau_to =
    return $ ExpV $ bitcastE tau_to (toExp val)

complexV :: Struct -> Val l m Exp -> Val l m Exp -> Val l m Exp
complexV sname a b =
    StructV sname (Map.fromList [("re", a), ("im", b)])

uncomplexV :: IsLabel l => Val l m Exp -> (Val l m Exp, Val l m Exp)
uncomplexV (StructV sname x) | isComplexStruct sname =
    (x Map.! "re", x Map.! "im")

uncomplexV val =
    errordoc $ text "Not a complex value:" <+> ppr val

instance IsLabel l => LiftedBool (Val l m Exp) (Val l m Exp) where
    liftBool op f (ConstV c) | Just c' <- liftBool op f c =
        ConstV c'

    liftBool op _ val =
        ExpV $ UnopE op (toExp val) noLoc

    liftBool2 op f (ConstV x) (ConstV y) | Just c' <- liftBool2 op f x y =
        ConstV c'

    liftBool2 op _ val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedEq (Val l m Exp) (Val l m Exp) where
    liftEq _ f val1 val2 | isValue val1 && isValue val2 =
        ConstV $ BoolC $ f val1 val2

    liftEq op _ val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedOrd (Val l m Exp) (Val l m Exp) where
    liftOrd _ f val1 val2 | isValue val1 && isValue val2 =
        ConstV $ BoolC $ f val1 val2

    liftOrd op _ val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedNum (Val l m Exp) (Val l m Exp) where
    liftNum op f (ConstV c) | Just c' <- liftNum op f c =
        ConstV c'

    liftNum op _f val =
        ExpV $ UnopE op (toExp val) noLoc

    liftNum2 Add _ val1 val2 | isZero val1 = val2
                             | isZero val2 = val1

    liftNum2 Sub _ val1 val2 | isZero val1 = negate val2
                             | isZero val2 = val1

    liftNum2 Mul _ val1 val2 | isZero val1 = val1
                             | isZero val2 = val2
                             | isOne  val1 = val2
                             | isOne  val2 = val1

    liftNum2 op f (ConstV c1) (ConstV c2) | Just c' <- liftNum2 op f c1 c2 =
        ConstV c'

    liftNum2 Add _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
        complexV sn (a+c) (b+d)
      where
        a, b, c, d :: Val l m Exp
        (a, b) = uncomplexV x
        (c, d) = uncomplexV y

    liftNum2 Sub _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
        complexV sn (a-c) (b-d)
      where
        a, b, c, d :: Val l m Exp
        (a, b) = uncomplexV x
        (c, d) = uncomplexV y

    liftNum2 Mul _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
        complexV sn (a*c - b*d) (b*c + a*d)
      where
        a, b, c, d :: Val l m Exp
        (a, b) = uncomplexV x
        (c, d) = uncomplexV y

    liftNum2 op _f val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedIntegral (Val l m Exp) (Val l m Exp) where
    liftIntegral2 op f (ConstV c1) (ConstV c2) | Just c' <- liftIntegral2 op f c1 c2 =
        ConstV c'

    liftIntegral2 Div _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
        complexV sn ((a*c + b*d)/(c*c + d*d)) ((b*c - a*d)/(c*c + d*d))
      where
        a, b, c, d :: Val l m Exp
        (a, b) = uncomplexV x
        (c, d) = uncomplexV y

        (/) :: Val l m Exp -> Val l m Exp -> Val l m Exp
        x / y = liftIntegral2 Div (quot) x y

    liftIntegral2 op _f val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedBits (Val l m Exp) (Val l m Exp) where
    liftBits op f (ConstV c) | Just c' <- liftBits op f c =
        ConstV c'

    liftBits op _ val =
        ExpV $ UnopE op (toExp val) noLoc

    liftBits2 Bor _ val1 val2 | isZero val1 = val2
                              | isZero val2 = val1

    liftBits2 Bxor _ val1 val2 | isZero val1 = val2
                               | isZero val2 = val1

    liftBits2 op f (ConstV x) (ConstV y) | Just c' <- liftBits2 op f x y =
        ConstV c'

    liftBits2 op _ val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

    liftShift op f (ConstV x) (ConstV y) | Just c' <- liftShift op f x y =
        ConstV c'

    liftShift op _ val1 val2 =
        ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

instance IsLabel l => LiftedCast (Val l m Exp) (Val l m Exp) where
    liftCast tau (ConstV c) | Just c' <- liftCast tau c =
        ConstV c'

    liftCast tau val =
        ExpV $ UnopE (Cast tau) (toExp val) noLoc

toConst :: forall l m . IsLabel l => Val l m Exp -> Const
toConst (ConstV c) =
    c

toConst (StructV s flds) =
    structC s (fs `zip` map toConst vals)
  where
    fs :: [Field]
    vals :: [Val l m Exp]
    (fs, vals) = unzip $ Map.assocs flds

toConst (ArrayV vvals) =
    arrayC (map toConst vals)
  where
    vals :: [Val l m Exp]
    vals = P.toList vvals

toConst val =
    errordoc $ text "toConst: not a constant:" <+> ppr val

class ToExp a where
    toExp :: a -> Exp

instance IsLabel l => ToExp (Val l m Exp) where
    toExp val | isValue val =
        constE $ toConst val

    toExp UnknownV =
        errordoc $ text "toExp: Cannot convert unknown value to expression"

    toExp (ConstV c) =
        constE c

    toExp (StructV s flds) =
        structE s (fs `zip` map toExp vals)
      where
        fs :: [Field]
        vals :: [Val l m Exp]
        (fs, vals) = unzip $ Map.assocs flds

    toExp (ArrayV vvals) =
        arrayE (map toExp vals)
      where
        vals :: [Val l m Exp]
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

instance IsLabel l => ToExp (Ref l m) where
    toExp (VarR v _) =
        varE v

    toExp (IdxR r start len) =
        IdxE (toExp r) (toExp start) len noLoc

    toExp (ProjR r f) =
        ProjE (toExp r) f noLoc

class (IsLabel l, MonadTc m) => ToComp l m a where
    toComp :: a -> EvalM l m (Comp l)
    toComp x = Comp <$> toSteps x

    toSteps :: a -> EvalM l m [Step l]

instance (IsLabel l, MonadTc m) => ToComp l m (Val l m (Comp l)) where
    toSteps (CompReturnV val) =
        unComp <$> returnC (toExp val)

    toSteps (CompV _ steps) =
        return steps

    toSteps (CompVarV v) =
        unComp <$> varC v

    toSteps val =
        faildoc $ text "toSteps: Cannot convert value to steps:" <+> ppr val

instance Eq (EvalM l m (Val l m a)) where
    (==) = error "EvalM incomparable"

instance Ord (EvalM l m (Val l m a)) where
    compare = error "EvalM incomparable"

instance Show (EvalM l m (Val l m a)) where
    show _ = "<evaluation action>"

instance IsLabel l => Pretty (Val l m a) where
    ppr UnknownV      = text "<unknown>"
    ppr val@ConstV{}  = ppr (toExp val)
    ppr val@StructV{} = ppr (toExp val)
    ppr val@ArrayV{}  = ppr (toExp val)
    ppr val@IdxV{}    = ppr (toExp val)
    ppr val@SliceV{}  = ppr (toExp val)
    ppr (RefV ref)    = ppr ref
    ppr val@ExpV{}    = ppr (toExp val)
    ppr val@ReturnV{} = ppr (toExp val)

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

instance IsLabel l => Pretty (Ref l m) where
    ppr = string . show

pprHeap :: IsLabel l => Heap l m -> Doc
pprHeap m = braces $ commasep (map ppr (IntMap.assocs m))
