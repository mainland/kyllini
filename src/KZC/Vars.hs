{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  KZC.Vars
-- Copyright   :  (c) 2014-2016 Drexel University
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

    freshenV,

    (/->),
    subst1
  ) where

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Map (Map)
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set

import KZC.Util.Uniq
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

instance Ord a => HasVars a a where
    allVars = singleton

instance HasVars x n => HasVars (Maybe x) n where
    allVars = foldMap allVars

instance HasVars x n => HasVars [x] n where
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

infix 1 /->
(/->) :: k -> a -> Map k a
(/->) = Map.singleton

type SubstM e v a = (Map v e, Set v) -> a

class (Ord v, Fvs e v) => Subst e v a where
    subst :: Map v e -> Set v -> a -> a
    subst theta phi x = substM x (theta, phi)

    substM :: a -> SubstM e v a

-- | Substitute without freshening.
subst1 :: Subst e v a => Map v e -> a -> a
subst1 m = subst m Set.empty

instance Subst e v a => Subst e v [a] where
    substM a (theta, phi) = fmap (\x -> substM x (theta, phi)) a

instance Subst e v a => Subst e v (Maybe a) where
    substM a (theta, phi) = fmap (\x -> substM x (theta, phi)) a

class Ord v => Freshen a e v where
    -- | Freshen a value of type @a@ within a substitution that is mapping
    -- values of type @v@ to values of type @e@.
    freshen :: a -> (a -> SubstM e v b) -> SubstM e v b

freshenV :: Ord v
         => String
         -> (String -> v)
         -> (v -> e)
         -> v -> (v -> SubstM e v b) -> SubstM e v b
freshenV s mkV mkE alpha k (theta, phi) | alpha `member` phi =
    k alpha' (theta', phi')
  where
    phi'    = insert alpha' phi
    theta'  = Map.insert alpha (mkE alpha') theta
    alpha'  = head [beta  | i <- [show i | i <- [(1::Integer)..]]
                          , let beta = mkV (s ++ i)
                          , beta `notMember` phi]

freshenV _ _ _ alpha k (theta, phi) =
    k alpha (theta', phi')
  where
    phi'    = insert alpha phi
    theta'  = Map.delete alpha theta

instance Freshen a e v => Freshen (Maybe a) e v where
    freshen Nothing  k = k Nothing
    freshen (Just x) k = freshen x $ \x -> k (Just x)

instance Freshen a e v => Freshen [a] e v where
    freshen []     k = k []
    freshen (v:vs) k = freshen v  $ \v' ->
                       freshen vs $ \vs' ->
                       k (v':vs')
