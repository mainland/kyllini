-- |
-- Module      :  KZC.Optimize.Eval.PArray
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval.PArray (
    PArray,
    defaultValue,
    nonDefaultValues,
    fromList,
    toList,
    length,
    (!?),
    (//),
    slice,
    replicateDefault
  ) where

import qualified Prelude as P
import Prelude hiding (length)

import Control.Monad (when)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (foldl')

data PArray a = PArray !a !Int !(IntMap a)
  deriving (Eq, Ord, Show)

defaultValue :: PArray a -> a
defaultValue (PArray dflt _ _) = dflt

nonDefaultValues :: PArray a -> [(Int, a)]
nonDefaultValues (PArray _ _ m) =
    IntMap.assocs m

fromList :: a -> [a] -> PArray a
fromList dflt xs =
    PArray dflt (P.length xs) (IntMap.fromList ([0..] `zip` xs))

toList :: PArray a -> [a]
toList (PArray dflt len m) =
    map lookup [0..len-1]
  where
    lookup i = case IntMap.lookup i m of
                 Nothing -> dflt
                 Just x  -> x

length :: PArray a -> Int
length (PArray _ len _) = len

(!?) :: PArray a -> Int -> Maybe a
PArray dflt len m !? i
    | i < 0 || i >= len = fail "Array index out of bounds"
    | otherwise         = case IntMap.lookup i m of
                            Nothing -> return dflt
                            Just x  -> return x

(//) :: Monad m => PArray a -> [(Int, a)] -> m (PArray a)
arr // [] =
    return arr

PArray dflt len m // ixs = do
    when (minimum is < 0 || maximum is >= len) $
        fail "Array index out of bounds"
    return $ PArray dflt len (foldl' update m ixs)
  where
    is :: [Int]
    is = map fst ixs

    update :: IntMap a -> (Int, a) -> IntMap a
    update m (i, x) = IntMap.insert i x m

slice :: Monad m => Int -> Int -> PArray a -> m (PArray a)
slice i n (PArray dflt len m)
    | i < 0 || n < 0 || i + n > len = fail "Array index out of bounds"
    | otherwise                     = return $ PArray dflt n m'
  where
    m' = IntMap.fromList [(j-i, x) | (j,x) <- IntMap.toList m, j >= i, j < i+n]

replicateDefault :: Int -> a -> PArray a
replicateDefault n dflt = PArray dflt n IntMap.empty
