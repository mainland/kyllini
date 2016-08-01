{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      :  KZC.Analysis.Interval
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Interval (
    IsInterval(..),
    Interval,
    BoundedInterval(..),
    PreciseInterval(..)
  ) where

import Prelude hiding ((<=))

import Test.QuickCheck
import Text.PrettyPrint.Mainland hiding (empty)

import KZC.Analysis.Lattice

-- | An interval.
class IsInterval a where
    empty :: a

    unit :: Integral i => i -> a
    fromUnit :: (Integral i, Monad m) => a -> m i

    interval :: Integral i => i -> i -> a
    fromInterval :: (Integral i, Monad m) => a -> m (i, i)

    extend :: Integral i => a -> i -> a

instance IsInterval a => IsInterval (Top a) where
    empty = NotTop empty

    unit i = NotTop $ unit i

    fromUnit (NotTop i) = fromUnit i
    fromUnit _          = fail "Non-unit interval"

    interval i j = NotTop $ interval i j

    fromInterval (NotTop i) = fromInterval i
    fromInterval _          = fail "Non-interval"

    extend (NotTop i) x = NotTop (extend i x)
    extend i          _ = i

-- | An interval
data Interval -- | Empty interval
              = Empty
              -- | An inclusive interval of numbers. Invariant: @'Interval' i1
              -- i2@ iff @i1@ <= @i2@.
              | Interval !Integer !Integer
  deriving (Eq, Ord, Show)

instance Arbitrary Interval where
    arbitrary = do NonNegative x   <- arbitrary
                   NonNegative len <- arbitrary
                   return $ if len == 0 then Empty else Interval x (x+len)

    shrink Empty                       = []
    shrink (Interval x y) | y - x == 1 = [Empty]
                          | otherwise  = [Interval (x+1) y,Interval x (y-1)]

instance Pretty Interval where
    ppr Empty          = text "()"
    ppr (Interval lo hi)
        | hi == lo     = ppr lo
        | otherwise    = brackets $ ppr lo <> comma <> ppr hi

instance IsInterval Interval where
    empty = Empty

    unit i = Interval i' i'
      where
        i' = fromIntegral i

    fromUnit (Interval i j) | i == j =
        return (fromIntegral i)

    fromUnit _ =
        fail "Non-unit interval"

    interval i j = Interval i' j'
      where
        i' = fromIntegral i
        j' = fromIntegral j

    fromInterval (Interval i j) =
        return (fromIntegral i, fromIntegral j)

    fromInterval _ =
        fail "Non-interval"

    extend Empty          _   = error "Cannot extend empty interval"
    extend (Interval i j) len = Interval i (j + fromIntegral len - 1)

instance Poset Interval where
    Empty        <= _              = True
    Interval i j <= Interval i' j' = i' <= i && j <= j'
    _            <= _              = False

instance Lattice Interval where
    Empty        `lub` i              = i
    i            `lub` Empty          = i
    Interval i j `lub` Interval i' j' = Interval l h
      where
        l = min i i'
        h = max j j'

    Interval i j `glb` Interval i' j' | j' >= i || i' <= j =
        Interval (max i i') (min j j')

    _ `glb` _ =
        Empty

instance BottomLattice Interval where
    bot = Empty

-- | A bounded known interval
newtype BoundedInterval = BI (Top Interval)
  deriving (Eq, Ord, Show, Pretty, Arbitrary,
            IsInterval, Poset, Lattice,
            BottomLattice, TopLattice, BoundedLattice)

instance BranchLattice BoundedInterval where
    bub = lub

-- | A precisely known interval
newtype PreciseInterval = PI (Top Interval)
  deriving (Eq, Ord, Show, Pretty, Arbitrary,
            IsInterval, Poset)

instance Lattice PreciseInterval where
    PI (NotTop (Interval i j)) `lub` PI (NotTop (Interval i' j'))
        | gap       = top
        | otherwise = PI (NotTop (Interval l h))
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 && i' - j > 1

    PI i `lub` PI j = PI (i `lub` j)

    PI i `glb` PI j = PI (i `glb` j)

instance BottomLattice PreciseInterval where
    bot = PI bot

instance TopLattice PreciseInterval where
    top = PI top

instance BoundedLattice PreciseInterval

-- If the two branches don't result in the same precise intervals, then we go to
-- top.
instance BranchLattice PreciseInterval where
    i `bub` j | i == j    = i
              | otherwise = top
