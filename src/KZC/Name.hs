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
    mkUniqName,
    mkUniq
  ) where

import Data.Loc
import Data.String
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Globals
import KZC.Uniq

data Name = Name
    { nameSort :: !NameSort
    , nameSym  :: !Symbol
    , nameLoc  :: !SrcLoc
    }
  deriving (Read)

instance Show Name where
    show (Name sort sym _)
        | printUniques = unintern sym <> pprSort sort
        | otherwise    = unintern sym
      where
        pprSort :: NameSort -> String
        pprSort Orig         = ""
        pprSort (Internal u) = "{" ++ show u ++ "}"

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
    ppr (Name sort sym _)
        | printUniques = text (unintern sym) <> pprSort sort
        | otherwise    = text (unintern sym)
      where
        pprSort :: NameSort -> Doc
        pprSort Orig         = empty
        pprSort (Internal u) = braces (ppr u)

instance IsString Name where
    fromString s = Name Orig (intern s) noLoc

data NameSort = Orig
              | Internal {-# UNPACK #-} !Uniq
  deriving (Eq, Ord, Read, Show)

class Named a where
    namedSymbol :: a -> Symbol

    namedString :: a -> String
    namedString n = unintern (namedSymbol n)

    mapName :: (Name -> Name) -> a -> a

instance Named Name where
    namedSymbol n = nameSym n
    mapName f n = f n

mkName :: String -> Loc -> Name
mkName s l = Name Orig (intern s) (SrcLoc l)

mkSymName :: Symbol -> Loc -> Name
mkSymName s l = Name Orig s (SrcLoc l)

mkUniqName :: MonadUnique m => String -> Loc -> m Name
mkUniqName s l = do
    u <- newUnique
    return $ Name (Internal u) (intern s) (SrcLoc l)

mkUniq :: (MonadUnique m, Named n)
       => n -> m n
mkUniq n = do
    u <- newUnique
    return $ mapName (\n -> n { nameSort = Internal u }) n
