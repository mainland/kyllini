{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

    uintV,
    intV,

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
import KZC.Auto.Lint
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

    fromInteger i = intV i

    abs _ = error "Val: abs undefined"

    signum _ = error "Val: signum undefined"

data Ref = VarR Var VarPtr
         | IdxR Ref (Val Exp) (Maybe Int)
         | ProjR Ref Field
  deriving (Eq, Ord, Show)

type VarPtr = Int

type Heap = IntMap (Val Exp)

uintV :: Integral a => a -> Val Exp
uintV i = FixV I U dEFAULT_INT_WIDTH (BP 0) (fromIntegral i)

intV :: Integral a => a -> Val Exp
intV i = FixV I S dEFAULT_INT_WIDTH (BP 0) (fromIntegral i)

zeroBitV, oneBitV :: Val Exp
zeroBitV = FixV I U (W 1) (BP 0) 0
oneBitV  = FixV I U (W 1) (BP 0) 1

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

-- | Produce a default value of the given type.
defaultValue :: forall m . MonadTc m
             => Type -> m (Val Exp)
defaultValue tau =
    go tau
  where
    go :: Type -> m (Val Exp)
    go (UnitT {})         = return UnitV
    go (BoolT {})         = return $ BoolV False
    go (FixT sc s w bp _) = return $ FixV sc s w bp 0
    go (FloatT fp _)      = return $ FloatV fp 0
    go (StringT {})       = return $ StringV ""

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
isDefaultValue :: Val Exp -> Bool
isDefaultValue UnitV            = True
isDefaultValue (BoolV False)    = True
isDefaultValue (FixV _ _ _ _ 0) = True
isDefaultValue (FloatV _ 0)     = True
isDefaultValue (StringV "")     = True
isDefaultValue (StructV _ flds) = all isDefaultValue (Map.elems flds)
isDefaultValue (ArrayV vals)    = all isDefaultValue (P.toList vals)
isDefaultValue _                = False

-- | Return 'True' if a 'Val' is completely known, even if it is a residual,
-- 'False' otherwise.
isKnown :: Val Exp -> Bool
isKnown UnknownV         = False
isKnown (BoolV {})       = True
isKnown (FixV {})        = True
isKnown (FloatV {})      = True
isKnown (StringV {})     = True
isKnown (StructV _ flds) = all isKnown (Map.elems flds)
isKnown (ArrayV vals)    = isKnown (P.defaultValue vals) &&
                           all (isKnown . snd) (P.nonDefaultValues vals)
isKnown (IdxV arr i)     = isKnown arr && isKnown i
isKnown (SliceV arr i _) = isKnown arr && isKnown i
isKnown (ExpV {})        = True
isKnown _                = False

catV :: Val Exp -> Val Exp -> Val Exp
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
idxV :: (Applicative m, Monad m)
      => Val Exp -> Int -> m (Val Exp)
idxV (ArrayV vs) off = vs P.!? off
idxV val off         = return $ ExpV $ idxE (toExp val) (fromIntegral off)

-- | Extract a slice of an array
sliceV :: (Applicative m, Monad m)
       => Val Exp -> Int -> Int -> m (Val Exp)
sliceV (ArrayV vs) off len = ArrayV <$> P.slice off len vs
sliceV val off len         = return $ ExpV $ sliceE (toExp val) (fromIntegral off) len

toBitsV :: forall m . MonadTc m
       => Val Exp -> Type -> m (Val Exp)
toBitsV val tau =
    go val tau
  where
    go :: Val Exp -> Type -> m (Val Exp)
    go (UnitV {}) _ =
        return $ ArrayV $ P.replicateDefault 0 zeroBitV

    go (BoolV f) _ =
        toBitArr (fromIntegral (fromEnum f)) 1

    go (FixV I U (W w) (BP 0) r) _ =
        toBitArr (numerator r) w

    go (FixV I S (W w) (BP 0) r) _
        | r >= 0    = toBitArr (numerator r) w
        | otherwise = toBitArr (numerator r + 2^w) w

    go (FloatV FP32 r) _ =
        toBitArr (fromIntegral (floatToWord (fromRational r))) 32

    go (FloatV FP64 r) _ =
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

    toBitArr :: Integer -> Int -> m (Val Exp)
    toBitArr n w = ArrayV <$> (P.replicateDefault w zeroBitV P.// [(i,oneBitV) | i <- [0..w-1], n `testBit` i])

packValues :: forall m . MonadTc m
            => [(Val Exp, Type)] -> m (Val Exp)
packValues vtaus =
    go emptyBitArr (reverse vtaus)
  where
    go :: Val Exp -> [(Val Exp, Type)] -> m (Val Exp)
    go bits [] =
        return bits

    go bits ((x, tau):xs) = do
        x_bits <- toBitsV x tau
        go (bits `catV` x_bits) xs

    emptyBitArr :: Val Exp
    emptyBitArr = ArrayV $ P.fromList zeroBitV []

fromBitsV :: forall m . MonadTc m
          => Val Exp -> Type -> m (Val Exp)
fromBitsV (ArrayV vs) tau =
    go vs tau
  where
    go :: P.PArray (Val Exp) -> Type -> m (Val Exp)
    go _ (UnitT {}) =
        return UnitV

    go vs (BoolT {}) =
        BoolV . toEnum . fromIntegral <$> fromBitArr vs

    go vs (FixT I U (W w) (BP 0) _) =
        FixV I U (W w) (BP 0) . fromIntegral <$> fromBitArr vs

    go vs (FixT I S (W w) (BP 0) _) = do
        i <- fromBitArr vs
        return $ if i < 2^(w-1)
                 then FixV I S (W w) (BP 0) (fromIntegral i)
                 else FixV I S (W w) (BP 0) (fromIntegral (i - 2^w))

    go vs (FloatT FP32 _) =
        FloatV FP32 . toRational . wordToFloat . fromIntegral <$> fromBitArr vs

    go vs (FloatT FP64 _) =
        FloatV FP64 . toRational . wordToDouble . fromIntegral <$> fromBitArr vs

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

    fromBitArr :: P.PArray (Val Exp) -> m Integer
    fromBitArr vs = foldM set 0 $ reverse $ P.toList vs
      where
        set :: Integer -> Val Exp -> m Integer
        set i (FixV I U (W 1) (BP 0) 0) = return $ i `shiftL` 1
        set i (FixV I U (W 1) (BP 0) 1) = return $ i `shiftL` 1 .|. 1
        set _ val                       = faildoc $ text "Not a bit:" <+> ppr val

fromBitsV val tau = do
    w <- typeSize tau
    return $ ExpV $ bitcastE (arrKnownT w bitT) (toExp val)

unpackValues :: forall m . MonadTc m
             => Val Exp -> [Type] -> m [Val Exp]
unpackValues bits taus = do
    go 0 taus
  where
    go :: Int -> [Type] -> m [Val Exp]
    go _ [] =
        return []

    go n (UnitT {}:taus) = do
        vals <- go n taus
        return $ UnitV : vals

    go n (tau:taus) = do
        w    <- typeSize tau
        slc  <- sliceV bits n w
        val  <- bitcastV slc (arrKnownT w bitT) tau
        vals <- go (n + w) taus
        return $ val : vals

-- | Bitcast a value from one type to another
bitcastV :: forall m . MonadTc m
         => Val Exp -> Type -> Type -> m (Val Exp)
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

complexV :: Struct -> Val Exp -> Val Exp -> Val Exp
complexV sname a b =
    StructV sname (Map.fromList [("re", a), ("im", b)])

uncomplexV :: Val Exp -> (Val Exp, Val Exp)
uncomplexV (StructV sname x) | isComplexStruct sname =
    (x Map.! "re", x Map.! "im")

uncomplexV val =
    errordoc $ text "Not a complex value:" <+> ppr val

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

liftNum2 Add _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
    complexV sn (a+c) (b+d)
  where
    a, b, c, d :: Val Exp
    (a, b) = uncomplexV x
    (c, d) = uncomplexV y

liftNum2 Sub _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
    complexV sn (a-c) (b-d)
  where
    a, b, c, d :: Val Exp
    (a, b) = uncomplexV x
    (c, d) = uncomplexV y

liftNum2 Mul _ x@(StructV sn _) y@(StructV sn' _) | isComplexStruct sn && sn' == sn =
    complexV sn (a*c - b*d) (b*c + a*d)
  where
    a, b, c, d :: Val Exp
    (a, b) = uncomplexV x
    (c, d) = uncomplexV y

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

toConst :: Val Exp -> Const
toConst UnitV =
    UnitC

toConst (BoolV f) =
    BoolC f

toConst (FixV sc s w bp r) =
    FixC sc s w bp r

toConst (FloatV fp r) =
    FloatC fp r

toConst (StringV s) =
    StringC s

toConst (StructV s flds) =
    structC s (fs `zip` map toConst vals)
  where
    fs :: [Field]
    vals :: [Val Exp]
    (fs, vals) = unzip $ Map.assocs flds

toConst (ArrayV vvals) =
    arrayC (map toConst vals)
  where
    vals :: [Val Exp]
    vals = P.toList vvals

toConst val =
    errordoc $ text "toConst: not a constant:" <+> ppr val

class ToExp a where
    toExp :: a -> Exp

instance ToExp (Val Exp) where
    toExp val | isValue val =
        constE $ toConst val

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
