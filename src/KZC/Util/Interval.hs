{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      :  KZC.Util.Interval
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Util.Interval (
    Interval(..),
    singI,
    fromSingI,
    intersectionI,

    BoundedInterval(..),
    PreciseInterval(..)
  ) where

import Prelude hiding ((<=))

import Test.QuickCheck
import Text.PrettyPrint.Mainland hiding (empty)

import KZC.Util.Lattice

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

singI :: Integral a => a -> Bound Interval
singI i = KnownB $ Interval i' i'
  where
    i' = fromIntegral i

fromSingI :: Monad m => Bound Interval -> m Integer
fromSingI (KnownB (Interval i j)) | i == j =
    return i

fromSingI _ =
    fail "Non-unit interval"

intersectionI :: Interval -> Interval -> Interval
intersectionI (Interval i j) (Interval i' j') | j' >= i || i' <= j =
    Interval (max i i') (min j j')

intersectionI _ _ =
    Empty

instance Pretty Interval where
    ppr Empty          = text "()"
    ppr (Interval lo hi)
        | hi == lo     = ppr lo
        | otherwise    = brackets $ ppr lo <> comma <> ppr hi

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

    glb = intersectionI

-- | A bounded known interval
newtype BoundedInterval = BI (Bound Interval)
  deriving (Eq, Ord, Show, Poset, Lattice, BoundedLattice)

instance Arbitrary BoundedInterval where
    arbitrary = BI <$> arbitrary

instance Pretty BoundedInterval where
    ppr (BI x) = ppr x

-- | A precisely known interval
newtype PreciseInterval = PI (Bound Interval)
  deriving (Eq, Ord, Show, Poset)

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

instance BoundedLattice PreciseInterval where
    top = PI top
    bot = PI bot
