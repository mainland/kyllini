-- |
-- Module      :  KZC.Backend.C.Util
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Backend.C.Util (
    ToInitializer(..),
    ToBlockItems(..)
  ) where

import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Language.C.Quote as C

class ToInitializer a where
    toInitializer :: a -> C.Initializer

class ToBlockItems a where
    toBlockItems :: a -> [C.BlockItem]

    toBlockItemsList :: [a] -> [C.BlockItem]
    toBlockItemsList = concatMap toBlockItems

instance ToBlockItems a => ToBlockItems [a] where
    toBlockItems = toBlockItemsList

instance ToBlockItems a => ToBlockItems (Seq a) where
    toBlockItems = toBlockItemsList . toList

instance ToBlockItems C.Stm where
    toBlockItems stm = [C.BlockStm stm]

    toBlockItemsList = map C.BlockStm

instance ToBlockItems C.InitGroup where
    toBlockItems decl = [C.BlockDecl decl]

    toBlockItemsList = map C.BlockDecl
