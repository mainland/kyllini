-- |
-- Module      : KZC.Name
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Name where

import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland

data Name = Name Symbol !SrcLoc
  deriving (Eq, Ord, Read, Show)

symbol :: Name -> Symbol
symbol (Name sym _) = sym

instance Located Name where
    locOf (Name _ loc) = locOf loc

instance Pretty Name where
    ppr (Name sym _) = text (unintern sym)
