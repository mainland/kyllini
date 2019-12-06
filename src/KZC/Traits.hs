{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  KZC.Traits
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Traits (
    Trait(..),
    Traits,

    traits,
    nullTraits,
    impliesTraits,
    reduceTraits,
    intersectTraits
  ) where

#if !MIN_VERSION_base(4,11,0)
import Data.Monoid ((<>))
#endif /* !MIN_VERSION_base(4,11,0) */
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Util.EnumSet (Set)
import qualified KZC.Util.EnumSet as Set

data Trait = EqR
           | OrdR
           | BoolR
           | NumR
           | IntegralR
           | FractionalR
           | BitsR
  deriving (Eq, Ord, Enum, Bounded, Read, Show)

type Traits = Set Trait

instance Pretty Trait where
    ppr EqR         = text "Eq"
    ppr OrdR        = text "Ord"
    ppr BoolR       = text "Bool"
    ppr NumR        = text "Num"
    ppr IntegralR   = text "Integral"
    ppr FractionalR = text "Fractional"
    ppr BitsR       = text "Bits"

instance Pretty Traits where
    ppr = folddoc (\x y -> x <+> char '+' <+> y) . map ppr . Set.toList

-- | Convert a list of traits to a set of traits.
traits :: [Trait] -> Traits
traits = Set.fromList

-- | Is the set of traits empty?
nullTraits :: Traits -> Bool
nullTraits = Set.null

impliesTraits :: Traits -> Traits -> Bool
impliesTraits ts1 ts2 = reduceTraits (ts1 <> ts2) == reduceTraits ts1

-- | Perform "context reduction" on traits, reducing the set of traits to the
-- minimal set that implies the original set of traits.
reduceTraits :: Traits -> Traits
reduceTraits = fixpoint (reduce implications)
  where
    reduce :: [(Trait, Traits)] -> Traits -> Traits
    reduce [] ts = ts
    reduce ((t, imp):imps) ts
      | t `Set.member` ts = reduce imps (ts Set.\\ imp)
      | otherwise         = reduce imps ts

    implications :: [(Trait, Traits)]
    implications = [ (OrdR,        Set.fromList [EqR])
                   , (BitsR,       Set.fromList [EqR])
                   , (BoolR,       Set.fromList [EqR])
                   , (NumR,        Set.fromList [OrdR])
                   , (IntegralR,   Set.fromList [NumR])
                   , (FractionalR, Set.fromList [NumR])
                   ]

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x | x' == x   = x
             | otherwise = fixpoint f (f x)
  where
    x' = f x

intersectTraits :: Traits -> Traits -> Traits
intersectTraits = Set.intersection
