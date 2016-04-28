{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : KZC.Auto.Label
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Auto.Label (
    Label(..),

    LProgram,
    LDecl,
    LComp,
    LArg,
    LStep
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.String (IsString(..))
import Data.Symbol
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Auto.Syntax
import KZC.Cg.Util
import KZC.Label
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

-- | A code label
data Label = SeqL !Symbol (Maybe Uniq)
           | ParL Label Label
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = SeqL (fromString s) Nothing

instance Pretty Label where
    ppr (SeqL s Nothing)  = text (unintern s)
    ppr (SeqL s (Just u)) = text (unintern s) <> braces (ppr u)
    ppr (ParL l1 l2)      = ppr (l1, l2)

instance C.ToIdent Label where
    toIdent l = (C.Id . zencode . flip displayS "" . renderCompact . ppr) l

instance Gensym Label where
    gensym s = SeqL (intern s) <$> maybeNewUnique

    uniquify (SeqL s _)   = SeqL s <$> maybeNewUnique
    uniquify (ParL l1 l2) = ParL <$> uniquify l1 <*> uniquify l2

instance IsLabel Label where
    pairLabel = ParL

instance Fvs Label Label where
    fvs l = singleton l

instance Subst Label Label Label where
    substM x (theta, _) = fromMaybe x (Map.lookup x theta)

type LProgram = Program Label

type LDecl = Decl Label

type LComp = Comp Label

type LArg = Arg Label

type LStep = Step Label