-- |
-- Module      : KZC.Name
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Name (
    Name(..),
    Named(..),
    mkName,
    mkSymName
  ) where

import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland

data Name = Name
    { nameSym :: !Symbol
    , nameLoc :: !Loc
    }
  deriving (Read, Show)

instance Eq Name where
    n1 == n2 = nameSym n1 == nameSym n2

instance Ord Name where
    compare n1 n2 = compare (nameSym n1) (nameSym n2)

instance Located Name where
    locOf (Name _ loc) = locOf loc

instance Pretty Name where
    ppr (Name sym _) = text (unintern sym)

class Named a where
    namedSymbol :: a -> Symbol

    namedString :: a -> String
    namedString n = unintern (namedSymbol n)

instance Named Name where
    namedSymbol n = nameSym n

mkName :: String -> Loc -> Name
mkName s l = Name (intern s) l

mkSymName :: Symbol -> Loc -> Name
mkSymName s l = Name s l
