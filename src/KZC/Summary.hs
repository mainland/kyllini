-- |
-- Module      :  KZC.Summary
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Summary (
    Summary(..),
    withSummaryContext,
    alwaysWithSummaryContext,
    maybeWithSummaryContext
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
withSummaryContext a = withLocContext a doc
  where
    doc = text "In" <+> summary a

alwaysWithSummaryContext :: (Located a, Summary a, MonadErr m)
                         => a
                         -> m b
                         -> m b
alwaysWithSummaryContext a = alwaysWithLocContext a doc
  where
    doc = text "In" <+> summary a

maybeWithSummaryContext :: (Located a, Summary a, MonadErr m)
                        => Maybe a
                        -> m b
                        -> m b
maybeWithSummaryContext Nothing  act = act
maybeWithSummaryContext (Just a) act = withLocContext a doc act
  where
    doc = text "In" <+> summary a
