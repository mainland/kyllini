-- |
-- Module      :  KZC.Label
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Label (
    IsLabel,
    Label(..),

    genLabel
  ) where

import Data.String (IsString(..))
import Data.Symbol
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Uniq

class (Ord l, Pretty l) => IsLabel l where

-- | A code label
newtype Label = Label { unLabel :: Symbol }
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = Label (fromString s)

instance Pretty Label where
    ppr (Label s) = text (unintern s)

instance IsLabel Label where

instance C.ToIdent Label where
    toIdent lbl = C.Id (unintern (unLabel lbl))

genLabel :: MonadUnique m => String -> m Label
genLabel s = do
    Uniq u <- newUnique
    return $ Label (intern (s ++ "__" ++ show u))
