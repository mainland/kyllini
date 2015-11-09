{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Label
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Label (
    IsLabel,
    Label(..),

    genLabel,
    uniquifyLabel
  ) where

import Data.String (IsString(..))
import Data.Symbol
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Cg.Util
import KZC.Uniq

class (Ord l, Pretty l, C.ToIdent l) => IsLabel l where

-- | A code label
data Label = Label
    { lblSym  :: !Symbol
    , lblUniq :: Maybe Uniq
    }
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = Label (fromString s) Nothing

instance Pretty Label where
    ppr (Label s Nothing)  = text (unintern s)
    ppr (Label s (Just u)) = text (unintern s) <> braces (ppr u)

instance C.ToIdent Label where
    toIdent l = (C.Id . zencode . flip displayS "" . renderCompact . ppr) l

instance IsLabel Label where

instance IsLabel (Label, Label) where

instance C.ToIdent (Label, Label) where
    toIdent l = (C.Id . zencode . flip displayS "" . renderCompact . ppr) l

genLabel :: MonadUnique m => String -> m Label
genLabel s = do
    u <- newUnique
    return $ Label (intern s) (Just u)

uniquifyLabel :: MonadUnique m => Label -> m Label
uniquifyLabel (Label l _) = do
    u <- newUnique
    return $ Label l (Just u)
