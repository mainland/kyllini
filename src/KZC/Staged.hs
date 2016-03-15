{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  KZC.Staged
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Staged (
  IfThenElse(..),

  IsEq(..),
  IsOrd(..),
  IsBool(..),
  IsBits(..)
  ) where

class IfThenElse a b where
    ifThenElse :: a -> b -> b -> b

instance IfThenElse Bool a where
    ifThenElse c t e = if c then t else e

infix 4 .==., ./=.

class IsEq a where
    (.==.) :: a -> a -> a
    (./=.) :: a -> a -> a

infix 4 .<., .<=., .>=., .>.

class IsEq a => IsOrd a where
    (.<.)  :: a -> a -> a
    (.<=.) :: a -> a -> a
    (.>=.) :: a -> a -> a
    (.>.)  :: a -> a -> a

infixr 3 .&&.
infixr 2 .||.

class IsEq a => IsBool a where
    (.&&.) :: a -> a -> a
    (.||.) :: a -> a -> a

infixl 5 ..|..
infixl 7 ..&..
infixl 8 `shiftL'`, `shiftR'`

class Num a => IsBits a where
    (..&..) :: a -> a -> a
    (..|..) :: a -> a -> a

    shiftL' :: a -> a -> a
    shiftR' :: a -> a -> a
