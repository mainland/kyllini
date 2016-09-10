{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

--------------------------------------------------------------------------------
-- |
-- Module      : KZC.Util.SetLike
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

module KZC.Util.SetLike (
    SetLike(..),
    MultiSetLike(..),
    OrderedSet
  ) where

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable
#endif /* !MIN_VERSION_base(4,8,0) */
import qualified Data.List as List
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

infixl 9 <\\>

class (Foldable f, Monoid (f a), Ord a) => SetLike f a where
    member :: a -> f a -> Bool

    notMember :: a -> f a -> Bool
    notMember x ys = not (x `member` ys)

    singleton :: a -> f a

    insert :: a -> f a -> f a

    (<\\>) :: f a -> f a -> f a

    delete :: a -> f a -> f a
    delete x xs = xs <\\> singleton x

    fromList :: [a] -> f a
    fromList xs = List.foldl' (<>) mempty (map singleton xs)

class SetLike f a => MultiSetLike f a where
    unique :: f a -> f a

instance Ord a => SetLike [] a where
    member x xs = x `List.elem` xs
    singleton x = [x]
    insert x xs = x:xs
    (<\\>)      = (List.\\)
    delete      = List.delete
    fromList xs = xs

instance Ord a => MultiSetLike [] a where
    unique xs = Set.toList (Set.fromList xs)

instance Ord a => SetLike Set a where
    member    = Set.member
    singleton = Set.singleton
    insert    = Set.insert
    (<\\>)    = (Set.\\)
    delete    = Set.delete
    fromList  = Set.fromList

-- | A set data type that preserves the order of element insertion.
data OrderedSet a = OS [a] (Set a)

mkOrderedSet :: Ord a => [a] -> Set a -> [a] -> OrderedSet a
mkOrderedSet xs xs' [] = OS xs xs'
mkOrderedSet xs xs' (y:ys)
    | y `Set.member` xs' = mkOrderedSet xs xs' ys
    | otherwise          = mkOrderedSet (xs ++ [y]) (Set.insert y xs') ys

instance Foldable OrderedSet where
    foldr f z (OS xs _) = List.foldr f z xs

instance Ord a => Monoid (OrderedSet a) where
    mempty = OS mempty mempty

    OS xs xs' `mappend` OS ys _ = mkOrderedSet xs xs' ys

instance Ord a => SetLike OrderedSet a where
    member x (OS _ ys) = Set.member x ys

    singleton x = OS (singleton x) (singleton x)

    insert x (OS xs ys) = OS (xs ++ [x]) (Set.insert x ys)

    OS xs xs' <\\> OS ys ys' = OS (xs <\\> ys) (xs' <\\> ys')

    delete x (OS xs xs') = OS (List.delete x xs) (Set.delete x xs')

    fromList = mkOrderedSet [] mempty
