{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Platform
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Platform (
    dEFAULT_INT_WIDTH,

    bIT_ARRAY_ELEM_TYPE,
    bIT_ARRAY_ELEM_BITS,

    bitArrayLen,
    bitArrayIdxOff,
    bitArrayIdx,
    bitArrayOff
  ) where

import qualified Language.C.Syntax as C

import KZC.Quote.C

dEFAULT_INT_WIDTH :: Int
dEFAULT_INT_WIDTH = 32

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

-- | Given the index of a bit in a bit array, return the index of the bit array
-- element holding the bit and the index of the bit within that element.
bitArrayIdxOff :: Integral a => a -> (a, a)
bitArrayIdxOff i = i `quotRem` bIT_ARRAY_ELEM_BITS

-- | Given the index of a bit in a bit array, return the index of the bit array
-- element holding the bit.
bitArrayIdx :: Integral a => a -> a
bitArrayIdx i = i `quot` bIT_ARRAY_ELEM_BITS

-- | Given the index of a bit in a bit array, return the index of the bit within
-- the bit array element holding the bit.
bitArrayOff :: Integral a => a -> a
bitArrayOff i = i `rem` bIT_ARRAY_ELEM_BITS
