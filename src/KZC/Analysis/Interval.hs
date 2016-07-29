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

instance IsInterval a => IsInterval (Bound a) where
    empty = KnownB empty

    unit i = KnownB $ unit i

    fromUnit (KnownB i) = fromUnit i
    fromUnit _          = fail "Non-unit interval"

    interval i j = KnownB $ interval i j

    fromInterval (KnownB i) = fromInterval i
    fromInterval _          = fail "Non-interval"

    extend (KnownB i) x = KnownB (extend i x)
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
newtype BoundedInterval = BI (Bound Interval)
  deriving (Eq, Ord, Show, IsInterval, Poset, Lattice,
            BottomLattice, TopLattice, BoundedLattice)

instance Arbitrary BoundedInterval where
    arbitrary = BI <$> arbitrary

instance Pretty BoundedInterval where
    ppr (BI x) = ppr x

-- | A precisely known interval
newtype PreciseInterval = PI (Bound Interval)
  deriving (Eq, Ord, Show, IsInterval, Poset)

instance Arbitrary PreciseInterval where
    arbitrary = PI <$> arbitrary

instance Pretty PreciseInterval where
    ppr (PI x) = ppr x

instance Lattice PreciseInterval where
    PI (KnownB (Interval i j)) `lub` PI (KnownB (Interval i' j'))
        | gap       = top
        | otherwise = PI (KnownB (Interval l h))
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 && i' - j > 1

    i `lub` j | i <= j    = j
              | j <= i    = i
              | otherwise = top

    PI i `glb` PI j = PI (i `glb` j)

instance BottomLattice PreciseInterval where
    bot = PI bot

instance TopLattice PreciseInterval where
    top = PI top

instance BoundedLattice PreciseInterval where
