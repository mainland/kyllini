{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Expr.Enum
-- Copyright   : (c) 2016-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Expr.Enum (
    streamConst,
    streamTypeValues,
    streamProduct,

    enumType
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Data.Binary.IEEE754 (wordToFloat,
                            wordToDouble)
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Bundle.Monadic as B
import qualified Data.Vector.Fusion.Bundle.Size as B
import Data.Vector.Fusion.Stream.Monadic (Step(..),
                                          Stream(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic.Mutable as MV
import Data.Word (Word32,
                  Word64)
import GHC.Float (float2Double)
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Expr.Syntax
import KZC.Expr.Lint

-- | Stream all values of a constant. If the constant is an array, yield each
-- element of the array in turn. If the stream is a scalar, yield the singe
-- scalar.
streamConst :: forall m m' . (MonadTc m, MonadFail m')
            => Const
            -> m (Stream m' Const)
streamConst (ArrayC cs) = return $ Stream f 0
  where
    n :: Int
    n = V.length cs

    f :: Int -> m' (Step Int Const)
    f i | i < n     = return $ Yield (cs V.! i) (i+1)
        | otherwise = return Done

streamConst (ReplicateC n c) = return $ Stream f 0
  where
    f :: Int -> m' (Step Int Const)
    f i | i < n     = return $ Yield c (i+1)
        | otherwise = return Done

streamConst (EnumC tau) = streamTypeValues tau
-- streamConst (EnumC tau) = enumTypeArray tau >>= streamConst

streamConst c = return $ Stream f (Just c)
  where
    f :: Maybe Const -> m' (Step (Maybe Const) Const)
    f (Just c) = return $ Yield c Nothing
    f Nothing  = return Done

-- | Stream all constants of the given type in bit order.
streamTypeValues :: forall m m' . (MonadTc m, MonadFail m')
                 => Type
                 -> m (Stream m' Const)
streamTypeValues UnitT{} = return $ Stream f 0
  where
    f :: Int -> m' (Step Int Const)
    f 0 = return $ Yield UnitC 1
    f _ = return Done

streamTypeValues BoolT{} = return $ Stream f 0
  where
    f :: Int -> m' (Step Int Const)
    f i | i <= hi   = return $ Yield (BoolC (toEnum i)) (i+1)
        | otherwise = return Done

    hi :: Int
    hi = fromEnum (maxBound :: Bool)

streamTypeValues (IntT ip@(U w) _) = return $ Stream f 0
  where
    f :: Int -> m' (Step Int Const)
    f i | i <= hi   = return $ Yield (IntC ip i) (i+1)
        | otherwise = return Done

    hi :: Int
    hi = 2^w-1

streamTypeValues (IntT ip@(I w) _) = return $ Stream f 0
  where
    f :: Int -> m' (Step Int Const)
    f i | i <= pos  = return $ Yield (IntC ip i)       (i+1)
        | i <= neg  = return $ Yield (IntC ip (i-2^w)) (i+1)
        | otherwise = return Done

    pos, neg :: Int
    pos = 2^(w-1)-1
    neg = 2^w-1

streamTypeValues (FloatT FP32 _) = return $ Stream f 0
  where
    f :: Word32 -> m' (Step Word32 Const)
    f w | w <= hi   = return $ Yield (FloatC FP32 ((float2Double . wordToFloat) w)) (w+1)
        | otherwise = return Done

    hi :: Word32
    hi = 2^(32::Int) - 1

streamTypeValues (FloatT FP64 _) = return $ Stream f 0
  where
    f :: Word64 -> m' (Step Word64 Const)
    f w | w <= hi   = return $ Yield (FloatC FP32 (wordToDouble w)) (w+1)
        | otherwise = return Done

    hi :: Word64
    hi = 2^(64::Int) - 1

streamTypeValues (StructT struct taus _) = do
    flds <- tyAppStruct struct taus
    let fs :: [Field]
        taus :: [Type]
        (fs, taus) = unzip flds

        mkStruct :: Vector Const -> Const
        mkStruct cs = StructC struct taus (fs `zip` V.toList cs)
    ss0 <- V.fromList <$> mapM streamTypeValues taus
    return $ S.map mkStruct $ streamProduct ss0

streamTypeValues tau@ArrT{} = do
    (n, tau_lem) <- checkKnownArrT tau
    stream       <- streamTypeValues tau_lem
    return $ S.map ArrayC $ streamProduct (V.replicate n stream)

streamTypeValues tau =
    faildoc $ text "Cannot stream values of type" <+> ppr tau

type ProductState m a = Maybe (Vector (Stream m a), Vector a)

-- | Stream the product of a vector of streams. The first stream in teh vector
-- of streams varies fastest.
streamProduct :: forall a m . MonadFail m
              => Vector (Stream m a)
              -> Stream m (Vector a)
streamProduct ss0 = Stream (f ss0) Nothing
  where
    f :: Vector (Stream m a)
      -> ProductState m a
      -> m (Step (ProductState m a) (Vector a))
    f ss0 Nothing = do
        (ss, xs) <- V.unzip <$> mapM first ss0
        return $ Yield xs (Just (ss, xs))
      where
        first :: Stream m a -> m (Stream m a, a)
        first (Stream f s) = do
            Yield x s' <- f s
            return (Stream f s', x)

    f ss0 (Just (ss, xs)) = loop ss xs 0
      where
        n :: Int
        n = V.length ss

        loop :: Vector (Stream m a)
             -> Vector a
             -> Int
             -> m (Step (ProductState m a) (Vector a))
        loop _ss _xs i | i == n =
            return Done

        loop ss xs i =
            case ss V.! i of
              Stream g s -> do
                x <- g s
                case x of
                  Yield x' s' -> do
                    let ss' = ss V.// [(i, Stream g s')]
                    let xs' = xs V.// [(i, x')]
                    return $ Yield xs' (Just (ss', xs'))
                  Skip s' -> do
                      let ss' = ss V.// [(i, Stream g s')]
                      return $ Skip (Just (ss', xs))
                  Done ->
                    case ss0 V.! i of
                      Stream g s0 -> do
                        Yield x0 s1     <- g s0
                        let ss'         =  ss V.// [(i, Stream g s1)]
                        let xs'         =  xs V.// [(i, x0)]
                        loop ss' xs' (i+1)

-- | Return a 'Vector' containing all values of the given type in bit order.
enumType :: MonadTcRef m => Type -> m (Vector Const)
enumType tau = do
    w     <- typeSize tau
    let n =  2^w
    s     <- streamTypeValues tau
    mv    <- MV.munstream $ B.fromStream s (B.Exact n)
    V.unsafeFreeze mv
