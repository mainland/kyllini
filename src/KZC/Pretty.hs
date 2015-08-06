-- |
-- Module      : KZC.Pretty
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Pretty (
    quote,

    commaEmbrace,
    semiEmbrace,
    semiEmbraceWrap,
    embrace,

    Fixity(..),
    Assoc(..),
    infix_,
    infixl_,
    infixr_,
    HasFixity(..),
    precOf,
    infixop
  ) where

import Text.PrettyPrint.Mainland

quote :: Pretty a => a -> Doc
quote x = char '`' <> ppr x <> char '\''

commaEmbrace :: [Doc] -> Doc
commaEmbrace = embrace commasep

embrace :: ([Doc] -> Doc) -> [Doc] -> Doc
embrace combine ds =
    case ds of
      []   -> lbrace <> rbrace
      [d]  -> lbrace <+> d <+> rbrace
      _    -> align $ lbrace <+> combine ds <+> rbrace

-- | Print a block of code surrounded by braces and separate by semicolons and
-- newlines.
semiEmbrace :: [Doc] -> Doc
semiEmbrace ds =
    case ds of
      []   -> lbrace <> rbrace
      [d]  -> lbrace <+> d <+> rbrace
      _    -> lbrace <+> (align . folddoc (</>) . punctuate semi) ds </> rbrace

-- | Print a block of code surrounded by braces and separate by semicolons and
-- newlines. The opening braces appears on its own line.
semiEmbraceWrap :: [Doc] -> Doc
semiEmbraceWrap ds =
    case ds of
      []   -> lbrace <> rbrace
      [d]  -> lbrace </> d </> rbrace
      _    -> nest 2 (lbrace </> (align . folddoc (</>) . punctuate semi) ds) </> rbrace

data Fixity = Fixity Assoc Int
  deriving (Eq, Ord)

data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Eq, Ord)

infix_ :: Int -> Fixity
infix_ = Fixity NonAssoc

infixl_ :: Int -> Fixity
infixl_ = Fixity LeftAssoc

infixr_ :: Int -> Fixity
infixr_ = Fixity RightAssoc

class HasFixity a where
    fixity :: a -> Fixity

precOf :: HasFixity a => a -> Int
precOf op =
    p
  where
    Fixity _ p = fixity op

infixop :: (Pretty a, Pretty b, Pretty op, HasFixity op)
        => Int -- ^ precedence of context
        -> op  -- ^ operator
        -> a   -- ^ left argument
        -> b   -- ^ right argument
        -> Doc
infixop prec op l r =
    parensIf (prec > opPrec) $
    pprPrec leftPrec l <+> ppr op <+/> pprPrec rightPrec r
  where
    leftPrec | opAssoc == RightAssoc = opPrec + 1
             | otherwise             = opPrec

    rightPrec | opAssoc == LeftAssoc = opPrec + 1
              | otherwise            = opPrec

    Fixity opAssoc opPrec = fixity op
