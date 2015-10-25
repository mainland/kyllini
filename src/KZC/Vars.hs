{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  KZC.Vars
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Vars (
    Binders(..),
    Fvs(..),
    HasVars(..),
    FreshVars(..),
    SubstM,
    Subst(..),
    Freshen(..),

    (/->)
  ) where

import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)

import KZC.Uniq
import KZC.Util.SetLike

class Ord n => Binders x n where
    binders :: SetLike m n => x -> m n

instance (Binders x n) => Binders [x] n where
    binders = foldMap binders

class Ord n => Fvs x n where
    fvs :: SetLike m n => x -> m n
    fvs _ = mempty

instance Fvs x n => Fvs (Maybe x) n where
    fvs = foldMap fvs

class Ord n => HasVars x n where
    allVars :: SetLike m n => x -> m n
    allVars _ = mempty

instance (Foldable f, HasVars x n) => HasVars (f x) n where
    allVars = foldMap allVars

class FreshVars a where
    freshVars :: (Functor m, MonadUnique m)
              => Int
              -> [a]
              -> m [a]

-- Performing Substitutions
--
-- The constraints for the @Subst@ class should be read as ``substitute @e@s for
-- @v@s in @a@.'' We use the substitution algorithm from "Secrets of the Glasgow
-- Haskell Inliner", where $\theta$ is the current substitution and $\phi$ is
-- the set of in-scope variables (note that this convention is the *opposite*
-- from that used in the paper).

(/->) :: k -> a -> Map k a
(/->) = Map.singleton

type SubstM v e a = (Map v e, Set v) -> a

class (Ord v, Fvs e v) => Subst e v a where
    subst :: Map v e -> Set v -> a -> a
    subst theta phi x = substM x (theta, phi)

    substM :: a -> SubstM v e a

instance (Functor f, Subst e v a) => Subst e v (f a) where
    substM a (theta, phi) = fmap (\x -> substM x (theta, phi)) a

class Freshen a v e where
    freshen :: a -> (a -> SubstM v e b) -> SubstM v e b

instance Freshen a v e => Freshen (Maybe a) v e where
    freshen Nothing  k = k Nothing
    freshen (Just x) k = freshen x $ \x -> k (Just x)

instance Freshen a v e => Freshen [a] v e where
    freshen []     k = k []
    freshen (v:vs) k = freshen v  $ \v' ->
                       freshen vs $ \vs' ->
                       k (v':vs')

