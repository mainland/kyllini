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
    binders :: MultiSetLike m n => x -> m n

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

class (Ord v, Fvs e v) => Subst e v a where
    subst :: Map v e -> Set v -> a -> a

instance (Functor f, Subst e v a) => Subst e v (f a) where
    subst theta phi a = fmap (subst theta phi) a

class Freshen a b c where
    freshen :: a -> Map b c -> Set b -> (a, Map b c, Set b)

instance Freshen a b c => Freshen (Maybe a) b c where
    freshen Nothing  theta phi = (Nothing, theta, phi)
    freshen (Just x) theta phi = (Just x', theta', phi')
      where
        (x', theta', phi') = freshen x theta phi

instance Freshen a b c => Freshen [a] b c where
    freshen []     theta phi = ([],     theta,   phi)
    freshen (v:vs) theta phi = (v':vs', theta'', phi'')
      where
        (v',  theta',  phi')  = freshen v theta phi
        (vs', theta'', phi'') = freshen vs theta' phi'
