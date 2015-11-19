{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Platform
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Platform (
    dEFAULT_INT_WIDTH,

    bIT_ARRAY_ELEM_TYPE,
    bIT_ARRAY_ELEM_BITS,

    BitArrayElemType,
    bitArrayLen
  ) where

import Data.Word
import qualified Language.C.Syntax as C

import KZC.Core.Syntax
import KZC.Quote.C

dEFAULT_INT_WIDTH :: W
dEFAULT_INT_WIDTH = W 32

-- Change these next three definitions to change the type of bit array elements.
bIT_ARRAY_ELEM_TYPE :: C.Type
bIT_ARRAY_ELEM_TYPE = [cty|typename uint8_t|]

bIT_ARRAY_ELEM_LOG_BITS :: Num a => a
bIT_ARRAY_ELEM_LOG_BITS = 3

type BitArrayElemType = Word8

bIT_ARRAY_ELEM_BITS :: Num a => a
bIT_ARRAY_ELEM_BITS = 2^(bIT_ARRAY_ELEM_LOG_BITS :: Int)

-- | Given the length of a bit array, return the number of elements of type
-- 'bIT_ARRAY_ELEM_TYPE' in the array's representation.
bitArrayLen :: Integral a => a -> a
bitArrayLen n = (n + (bIT_ARRAY_ELEM_BITS-1)) `quot` bIT_ARRAY_ELEM_BITS
