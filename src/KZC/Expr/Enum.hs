-- |
-- Module      : KZC.Expr.Enum
-- Copyright   : (c) 2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Expr.Enum (
    enumType,
    enumTypes,
    enumTypeArray
  ) where

import Data.Binary.IEEE754 (wordToFloat,
                            wordToDouble)
import qualified Data.Vector as V
import Data.Word (Word32,
                  Word64)
import GHC.Float (float2Double)
import Text.PrettyPrint.Mainland

import KZC.Expr.Syntax
import KZC.Expr.Lint

-- | Enumerate all values of the given type /in bit order/.
enumType :: MonadTc m => Type -> m [Const]
enumType UnitT{} =
    return [UnitC]

enumType BoolT{} =
    return $ map BoolC [(minBound :: Bool)..]

enumType (FixT I U (W w) (BP 0) _) =
    return $ map (FixC I U (W w) (BP 0)) [0..hi]
  where
    hi :: Int
    hi = 2^w-1

enumType (FixT I S (W w) (BP 0) _) =
    return $ map (FixC I S (W w) (BP 0)) $ [0..hi] ++ [lo..(-1)]
  where
    hi, lo :: Int
    hi = 2^(w-1)-1
    lo = -(2^(w-1))

enumType (FloatT FP32 _) =
    return $ map (FloatC FP32 . float2Double . wordToFloat)
                 [(minBound :: Word32)..]

enumType (FloatT FP64 _) =
    return $ map (FloatC FP64 . wordToDouble)
                 [(minBound :: Word64)..]

enumType (RefT tau _) =
    enumType tau

enumType (StructT sname _) = do
    StructDef _ flds _ <- lookupStruct sname
    let fs :: [Field]
        taus :: [Type]
        (fs, taus) = unzip flds
    valss <- enumTypes taus
    return [StructC sname (fs `zip` vals) | vals <- valss]

enumType (ArrT (ConstI n _) tau _) = do
    valss <- enumTypes (replicate n tau)
    return [ArrayC (V.fromList vals) | vals <- valss]

enumType tau =
    faildoc $ text "Cannot enumerate type" <+> ppr tau

-- | Enumerate all values of the given types.
enumTypes :: MonadTc m => [Type] -> m [[Const]]
enumTypes [] =
    return []

enumTypes [tau] = do
    vals <- enumType tau
    return [[val] | val <- vals]

enumTypes (tau:taus) = do
    vals  <- enumType tau
    valss <- enumTypes taus
    return [val':vals' | vals' <- valss, val' <- vals]

-- | Enumerate all values of the given type and return the result as a constant
-- array.
enumTypeArray :: MonadTc m => Type -> m Const
enumTypeArray tau = (ArrayC . V.fromList) <$> enumType tau
