-- |
-- Module      :  KZC.Staged
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Staged (
  IsEq(..),
  IsOrd(..),
  IsBits(..)
  ) where

class IsEq a where
    (.==.) :: a -> a -> a
    (./=.) :: a -> a -> a

class IsEq a => IsOrd a where
    (.<.)  :: a -> a -> a
    (.<=.) :: a -> a -> a
    (.>=.) :: a -> a -> a
    (.>.)  :: a -> a -> a

class Num a => IsBits a where
    bit' :: a -> a
