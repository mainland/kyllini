{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  KZC.Label
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Label (
    IsLabel(..),
    Label(..)
  ) where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.String (IsString(..))
import Data.Symbol
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Cg.Util
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

class ( Ord l
      , IsString l
      , C.ToIdent l
      , Pretty l
      , Gensym l
      , Fvs l l
      , Subst l l l ) => IsLabel l where
    pairLabel :: l -> l -> l

-- | A code label
data Label = L !Symbol (Maybe Uniq)
           | PairL Label Label
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = L (fromString s) Nothing

instance Pretty Label where
    ppr (L s Nothing)  = text (unintern s)
    ppr (L s (Just u)) = text (unintern s) <> braces (ppr u)
    ppr (PairL l1 l2)  = ppr (l1, l2)

instance C.ToIdent Label where
    toIdent l = (C.Id . zencode . flip displayS "" . renderCompact . ppr) l

instance Gensym Label where
    gensym s = L (intern s) <$> maybeNewUnique

    uniquify (L s _)       = L s <$> maybeNewUnique
    uniquify (PairL l1 l2) = PairL <$> uniquify l1 <*> uniquify l2

instance IsLabel Label where
    pairLabel = PairL

instance Fvs Label Label where
    fvs l = singleton l

instance Subst Label Label Label where
    substM x (theta, _) = fromMaybe x (Map.lookup x theta)
