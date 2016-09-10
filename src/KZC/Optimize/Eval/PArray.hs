-- |
-- Module      :  KZC.Optimize.Eval.PArray
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Eval.PArray (
    PArray,
    defaultValue,
    nonDefaultValues,
    fromList,
    toList,
    fromVector,
    toVector,
    length,
    (!?),
    (//),
    slice,
    replicateDefault
  ) where

import qualified Prelude as P
import Prelude hiding (length)

import Control.Monad (when)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V

tHRESHOLD :: Int
tHRESHOLD = 1024

data PArray a = ArrP !a !Int !(IntMap a)
              | ArrF !a !(Vector a)
  deriving (Eq, Ord, Show)

defaultValue :: PArray a -> a
defaultValue (ArrP dflt _ _) = dflt
defaultValue (ArrF dflt _)   = dflt

nonDefaultValues :: Eq a => PArray a -> [(Int, a)]
nonDefaultValues (ArrP _ _ m) =
    IntMap.assocs m

nonDefaultValues (ArrF dflt v) =
    [(i, x) | (i, x) <- [0..] `zip` V.toList v, x /= dflt]

fromList :: a -> [a] -> PArray a
fromList dflt xs | P.length xs < tHRESHOLD =
    ArrF dflt (V.fromList xs)

fromList dflt xs =
    ArrP dflt (P.length xs) (IntMap.fromList ([0..] `zip` xs))

toList :: PArray a -> [a]
toList (ArrP dflt len m) =
    map lookup [0..len-1]
  where
    lookup i = fromMaybe dflt (IntMap.lookup i m)

toList (ArrF _ v) =
    V.toList v

fromVector :: a -> Vector a -> PArray a
fromVector = ArrF

toVector :: PArray a -> Vector a
toVector (ArrP dflt n xs) = V.replicate n dflt V.// IntMap.toList xs
toVector (ArrF _ v)       = v

length :: PArray a -> Int
length (ArrP _ len _) = len
length (ArrF _ v)     = V.length v

(!?) :: Monad m => PArray a -> Int -> m a
ArrP dflt len m !? i
    | i < 0 || i >= len = fail "Array index out of bounds"
    | otherwise         = case IntMap.lookup i m of
                            Nothing -> return dflt
                            Just x  -> return x
ArrF _ v !? i = maybe (fail "Array index out of bounds")
                      return
                      (v V.!? i)

(//) :: Monad m => PArray a -> [(Int, a)] -> m (PArray a)
arr // [] =
    return arr

ArrP dflt len m // ixs = do
    when (minimum is < 0 || maximum is >= len) $
        fail "Array index out of bounds"
    return $ ArrP dflt len (foldl' update m ixs)
  where
    is :: [Int]
    is = map fst ixs

    update :: IntMap a -> (Int, a) -> IntMap a
    update m (i, x) = IntMap.insert i x m

ArrF dflt v // ixs =
    return $ ArrF dflt (v V.// ixs)

slice :: Monad m => Int -> Int -> PArray a -> m (PArray a)
slice i n (ArrP dflt len m)
    | i < 0 || n < 0 || i + n > len = fail "Array index out of bounds"
    | otherwise                     = return $ ArrP dflt n m'
  where
    m' = IntMap.fromList [(j-i, x) | (j,x) <- IntMap.toList m, j >= i, j < i+n]

slice i n (ArrF dflt v) =
    return $ ArrF dflt (V.slice i n v)

replicateDefault :: Int -> a -> PArray a
replicateDefault n dflt
    | n < tHRESHOLD = ArrF dflt (V.replicate n dflt)
    | otherwise     = ArrP dflt n IntMap.empty
