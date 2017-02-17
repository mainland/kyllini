{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Util.Pretty
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Util.Pretty (
    ifPrec,
    ifPrec1,
    parrPrec,
    parrPrec1,
    doPrec,
    doPrec1,
    appPrec,
    appPrec1,
    arrowPrec,
    arrowPrec1,
    tyappPrec,
    tyappPrec1,

    enquote,

    embrace,

    pprStruct,

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

-- %nonassoc IF
-- %left ','
-- %left '&&' '||'
-- %left '==' '!='
-- %left '|'
-- %left '^'
-- %left '&'
-- %left '<' '<=' '>' '>='
-- %left '<<' '>>'
-- %left '+' '-'
-- %left '*' '/' '%'
-- %left '**'
-- %left 'length'
-- %left '~' 'not' NEG

-- %left '|>>>|'
-- %left '>>>'

-- %left 'in'

-- application

ifPrec :: Int
ifPrec = 0

ifPrec1 :: Int
ifPrec1 = ifPrec + 1

parrPrec :: Int
parrPrec = 15

parrPrec1 :: Int
parrPrec1 = parrPrec + 1

doPrec :: Int
doPrec = 12

doPrec1 :: Int
doPrec1 = doPrec + 1

appPrec :: Int
appPrec = 17

appPrec1 :: Int
appPrec1 = appPrec + 1

arrowPrec :: Int
arrowPrec = 0

arrowPrec1 :: Int
arrowPrec1 = arrowPrec + 1

tyappPrec :: Int
tyappPrec = 1

tyappPrec1 :: Int
tyappPrec1 = tyappPrec + 1

-- | Surround a 'Doc' with single quotes.
enquote :: Doc -> Doc
enquote d = char '`' <> d <> char '\''

-- | Print a block of code surrounded by braces and separated by semicolons and
-- newlines. The opening brace appears on its own line, and all lines are nested
-- and aligned.
embrace :: [Doc] -> Doc
embrace ds =
    case ds of
      [] -> lbrace <> rbrace
      _  -> nest 2 (lbrace </> (align . folddoc (</>) . punctuate semi) ds) </> rbrace

pprStruct :: forall a b . (Pretty a, Pretty b) => Doc -> Doc -> [(a, b)] -> Doc
pprStruct fldsep valsep flds =
    enclosesep lbrace rbrace fldsep
    [ppr k <+> valsep <+> ppr v | (k, v) <- flds]

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
