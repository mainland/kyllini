-- |
-- Module      : KZC.Name
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Name (
    Name(..),
    NameSort(..),
    Named(..),
    mkName,
    mkSymName,
    mkUniqName
  ) where

import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Uniq

data Name = Name
    { nameSort :: !NameSort
    , nameSym  :: !Symbol
    , nameLoc  :: !Loc
    }
  deriving (Read, Show)

instance Eq Name where
    n1 == n2 = nameSym n1 == nameSym n2

instance Ord Name where
    compare n1 n2 =
        case compare (nameSort n1) (nameSort n2) of
          LT -> LT
          GT -> GT
          EQ -> compare (nameSym n1) (nameSym n2)

instance Located Name where
    locOf (Name _ _ loc) = locOf loc

instance Pretty Name where
    ppr (Name _ sym _) = text (unintern sym)

data NameSort = Orig
              | Internal {-# UNPACK #-} !Uniq
  deriving (Eq, Ord, Read, Show)

class Named a where
    namedSymbol :: a -> Symbol

    namedString :: a -> String
    namedString n = unintern (namedSymbol n)

instance Named Name where
    namedSymbol n = nameSym n

mkName :: String -> Loc -> Name
mkName s l = Name Orig (intern s) l

mkSymName :: Symbol -> Loc -> Name
mkSymName s l = Name Orig s l

mkUniqName :: MonadUnique m => String -> Loc -> m Name
mkUniqName s l = do
    u <- newUnique
    return $ Name (Internal u) (intern s) l
