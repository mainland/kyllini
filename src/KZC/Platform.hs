{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Platform
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Platform (
    W(..),

    dEFAULT_INT_WIDTH,

    bIT_ARRAY_ELEM_TYPE,
    bIT_ARRAY_ELEM_BITS,

    bitArrayLen
  ) where

import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Quote.C

-- | Fixed-point width
newtype W = W Int
  deriving (Eq, Ord, Read, Show, Num)

instance Pretty W where
    ppr (W w) = ppr w

dEFAULT_INT_WIDTH :: W
dEFAULT_INT_WIDTH = W 32

-- Change these next three definitions to change the type of bit array elements.
bIT_ARRAY_ELEM_TYPE :: C.Type
bIT_ARRAY_ELEM_TYPE = [cty|typename uint8_t|]

bIT_ARRAY_ELEM_LOG_BITS :: Num a => a
bIT_ARRAY_ELEM_LOG_BITS = 3

bIT_ARRAY_ELEM_BITS :: Num a => a
bIT_ARRAY_ELEM_BITS = 2^(bIT_ARRAY_ELEM_LOG_BITS :: Int)

-- | Given the length of a bit array, return the number of elements of type
-- 'bIT_ARRAY_ELEM_TYPE' in the array's representation.
bitArrayLen :: Integral a => a -> a
bitArrayLen n = (n + (bIT_ARRAY_ELEM_BITS-1)) `quot` bIT_ARRAY_ELEM_BITS
