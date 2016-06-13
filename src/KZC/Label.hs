{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  KZC.Label
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Label (
    IsLabel(..)
  ) where

import Data.String (IsString(..))
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Uniq
import KZC.Vars

class ( Ord l
      , Show l
      , IsString l
      , C.ToIdent l
      , Pretty l
      , Gensym l
      , Fvs l l
      , Subst l l l ) => IsLabel l where
    -- | Produced a label indexed by the value of a (for) loop index variable.
    indexLabel :: Int -> l -> l
    -- | Produce a joint label for a fused computational step.
    jointLabel :: (l, l) -> l
