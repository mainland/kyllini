{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

--------------------------------------------------------------------------------
-- |
-- Module      : KZC.Util.SetLike
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>
--
--------------------------------------------------------------------------------

module KZC.Util.SetLike (
    MultiSetLike(..),
    SetLike,
    OrderedSet
  ) where

import qualified Data.List as List
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

infixl 9 <\\>

class (Monoid (m a), Ord a) => MultiSetLike m a where
    singleton :: a -> m a

    (<\\>) :: m a -> m a -> m a

    delete :: a -> m a -> m a
    delete x xs = xs <\\> singleton x

    fromList :: [a] -> m a
    fromList xs = List.foldl' (<>) mempty (map singleton xs)

    toList :: m a -> [a]

    unique :: m a -> m a

class MultiSetLike m a => SetLike m a where

instance Ord a => MultiSetLike [] a where
    singleton x = [x]
    xs <\\> ys  = xs List.\\ ys
    delete x xs = List.delete x xs
    fromList xs = xs
    toList xs   = xs
    unique xs   = Set.toList (Set.fromList xs)

instance Ord a => MultiSetLike Set a where
    singleton x = Set.singleton x
    xs <\\> ys  = xs Set.\\ ys
    delete x xs = Set.delete x xs
    fromList xs = Set.fromList xs
    toList xs   = Set.toList xs
    unique xs   = xs

instance Ord a => SetLike Set a where

-- | A set data type that preserves the order of element insertion.
data OrderedSet a = OS [a] (Set a)

mkOrderedSet :: Ord a => [a] -> Set a -> [a] -> OrderedSet a
mkOrderedSet xs xs' [] = OS xs xs'
mkOrderedSet xs xs' (y:ys)
    | y `Set.member` xs' = mkOrderedSet xs xs' ys
    | otherwise          = mkOrderedSet (xs ++ [y]) (Set.insert y xs') ys

instance Ord a => Monoid (OrderedSet a) where
    mempty = OS mempty mempty

    OS xs xs' `mappend` OS ys _ = mkOrderedSet xs xs' ys

instance Ord a => MultiSetLike OrderedSet a where
    singleton x = OS (singleton x) (singleton x)

    OS xs xs' <\\> OS ys ys' = OS (xs <\\> ys) (xs' <\\> ys')

    delete x (OS xs xs') = OS (List.delete x xs) (Set.delete x xs')

    fromList ys = mkOrderedSet [] Set.empty ys

    toList (OS xs _) = xs

    unique xs = xs

instance Ord a => SetLike OrderedSet a where
