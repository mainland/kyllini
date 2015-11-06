-- |
-- Module      :  KZC.Summary
-- Copyright   :  (c) 2014-2015 Drexel University 2014
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Summary (
    Summary(..),
    withSummaryContext
  ) where

import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Error

class Summary a where
    summary :: a -> Doc

withSummaryContext :: (Located a, Summary a, MonadErr m)
                   => a
                   -> m b
                   -> m b
withSummaryContext a act =
    withLocContext a doc act
  where
    doc = text "In" <+> summary a
