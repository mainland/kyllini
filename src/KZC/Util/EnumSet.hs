{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Util.EnumSet
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Util.EnumSet (
    -- * Set type
    Set(..),

    -- * Operators
    (\\),

    -- * Query
    null,
    size,
    member,
    notMember,
    isSubsetOf,

    -- * Construction
    empty,
    singleton,
    insert,
    delete,

    -- * Combine
    union,
    difference,
    intersection,

    -- * Conversion
    -- ** List
    toList,
    fromList
  ) where

import Prelude hiding (null)

import Data.Bits
import Data.Data (Data, Typeable)
import Data.List (foldl')
import Data.Word (Word32)

newtype Set a = Set Word32
  deriving (Eq, Ord, Data, Typeable)

infixl 9 \\
(\\) :: Ord a => Set a -> Set a -> Set a
(\\) = difference

-- | Test for empty set.
null :: Set a -> Bool
null (Set bits) = bits == 0

-- | Compute number of elements in the set.
size :: Set a -> Int
size (Set bits) = popCount bits

-- | Test for set membership.
member :: Enum a => a -> Set a -> Bool
member x (Set bits) = bits `testBit` fromEnum x

-- | Is the element not in the set?
notMember :: Enum a => a -> Set a -> Bool
notMember x (Set bits) = not (bits `testBit` fromEnum x)

-- | Is this a subset?
isSubsetOf :: Set a -> Set a -> Bool
isSubsetOf (Set bits1) (Set bits2) = bits1 .&. bits2 == bits1

-- | The empty set.
empty :: Set a
empty = Set 0

-- | Create a singleton set
singleton :: Enum a => a -> Set a
singleton x = Set (bit (fromEnum x))

-- | Insert an element in a set.
insert :: Enum a => a -> Set a -> Set a
insert x (Set bits) = Set $ bits `setBit` fromEnum x

-- | Delete an element from a set.
delete :: Enum a => a -> Set a -> Set a
delete x (Set bits) = Set $ bits `clearBit` fromEnum x

-- | The union of two sets.
union :: Set a -> Set a -> Set a
union (Set bits1) (Set bits2) = Set (bits1 .|. bits2)

-- | The difference of two sets.
difference :: Set a -> Set a -> Set a
difference (Set bits1) (Set bits2) = Set (bits1 .&. complement bits2)

-- | The intersection of two sets.
intersection :: Set a -> Set a -> Set a
intersection (Set bits1) (Set bits2) = Set (bits1 .&. bits2)

-- | Convert the set to a list of elements.
toList :: forall a . (Enum a, Bounded a) => Set a -> [a]
toList (Set bits) = [x | x <- [minBound..maxBound::a],
                         bits `testBit` fromEnum x ]

-- | Construct a set from a list of elements.
fromList :: forall a . Enum a => [a] -> Set a
fromList xs = Set (foldl' setBit 0 (map fromEnum xs))

instance Monoid (Set a) where
    mempty = Set 0

    Set x `mappend` Set y = Set (x .|. y)

instance (Enum a, Bounded a, Show a) => Show (Set a) where
    show = show . toList

instance (Enum a, Bounded a, Read a) => Read (Set a) where
    readsPrec p s = [(fromList xs, s') | (xs, s') <- readsPrec p s]
