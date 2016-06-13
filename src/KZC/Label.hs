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
    jointLabel :: (l, l) -> l
