{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : KZC.Core.Label
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Core.Label (
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
import Text.PrettyPrint.Mainland.Class

import KZC.Core.Syntax
import KZC.Label
import KZC.Util.SetLike
import KZC.Util.Uniq
import KZC.Util.ZEncode
import KZC.Vars

-- | A code label
data Label = SeqL !Symbol (Maybe Uniq)
           | IdxL !Int Label
           | ParL Label Label
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = SeqL (fromString s) Nothing

instance Pretty Label where
    ppr (SeqL s Nothing)  = text (unintern s)
    ppr (SeqL s (Just u)) = text (unintern s) <> braces (ppr u)
    ppr (IdxL i l)        = ppr i <> char '@' <> ppr l
    ppr (ParL l1 l2)      = ppr (l1, l2)

instance C.ToIdent Label where
    toIdent = C.Id . zencode . ppr

instance Gensym Label where
    gensym s = SeqL (intern s) <$> maybeNewUnique

    uniquify (SeqL s _)   = SeqL s <$> maybeNewUnique
    uniquify (IdxL i l)   = IdxL i <$> uniquify l
    uniquify (ParL l1 l2) = ParL <$> uniquify l1 <*> uniquify l2

instance Fvs Label Label where
    fvs = singleton

instance Subst Label Label Label where
    substM x (theta, _) = fromMaybe x (Map.lookup x theta)

instance IsLabel Label where
    indexLabel = IdxL
    jointLabel = ParL

type LProgram = Program Label

type LDecl = Decl Label

type LComp = Comp Label

type LArg = Arg Label

type LStep = Step Label
