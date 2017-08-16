-- |
-- Module      : Language.Ziria.Parser.Monad
-- Copyright   : (c) 2014-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Ziria.Parser.Monad (
    P,
    runP,
    evalP,

    PState(..),
    emptyPState,

    addStructIdentifier,
    addStructIdentifiers,
    isStructIdentifier,

    getInput,
    setInput,
    pushLexState,
    popLexState,
    getLexState,
    getCurToken,
    setCurToken,

    getDialect,

    alexGetCharOrFail,
    peekChar,
    peekChars,
    nextChar,
    skipChar,

    failAt,
    lexerError,
    unexpectedEOF,
    parserError,
    unclosed,
    expected,
    expectedAt,
  ) where

import Control.Monad.Exception
import Control.Monad.State
import Data.Int (Int64)
import Data.Loc
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Symbol
import qualified Data.Text.Lazy as T
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import Language.Ziria.Parser.Alex
import Language.Ziria.Parser.Tokens
import Language.Ziria.Parser.Exceptions
import Language.Ziria.Syntax (Dialect(..))

import KZC.Util.Pretty

data PState = PState
    { input             :: !AlexInput
    , curToken          :: L Token
    , lexState          :: ![Int]
    , dialect           :: !Dialect
    , structIdentifiers :: !(Set Symbol)
    }

emptyPState :: Dialect
            -> T.Text
            -> Pos
            -> PState
emptyPState d buf pos = PState
    { input             = alexInput buf pos
    , curToken          = error "no token"
    , lexState          = [0]
    , dialect           = d
    , structIdentifiers = Set.fromList ["Complex", "complex", "complex8", "complex16", "complex32", "complex64"]
    }

newtype P a = P { runP :: PState -> Either SomeException (a, PState) }

instance Functor P where
    fmap f x = x >>= return . f

instance Applicative P where
    pure  = return
    (<*>) = ap

instance Monad P where
    m >>= k = P $ \s ->
        case runP m s of
          Left e         -> Left e
          Right (a, s')  -> runP (k a) s'

    m1 >> m2 = P $ \s ->
        case runP m1 s of
          Left e         -> Left e
          Right (_, s')  -> runP m2 s'

    return a = P $ \s -> Right (a, s)

    fail msg = do
        inp <- getInput
        throw $ ParserException (Loc (alexPos inp) (alexPos inp))
                                (ppr (alexPos inp) <> colon <+> text msg)

instance MonadState PState P where
    get    = P $ \s -> Right (s, s)
    put s  = P $ \_ -> Right ((), s)

instance MonadException P where
    throw e = P $ \_ -> Left (toException e)

    m `catch` h = P $ \s ->
        case runP m s of
          Left e ->
              case fromException e of
                Just e'  -> runP (h e') s
                Nothing  -> Left e
          Right (a, s')  -> Right (a, s')

evalP :: P a -> PState -> Either SomeException a
evalP comp st =
    case runP comp st of
      Left e        -> Left e
      Right (a, _)  -> Right a

addStructIdentifier :: Symbol -> P ()
addStructIdentifier ident =
    modify $ \s -> s { structIdentifiers = Set.insert ident (structIdentifiers s) }

addStructIdentifiers :: Set Symbol -> P ()
addStructIdentifiers idents =
  modify $ \s -> s { structIdentifiers = idents <> structIdentifiers s }

isStructIdentifier :: Symbol -> P Bool
isStructIdentifier ident =
    gets (Set.member ident . structIdentifiers)

getInput  :: P AlexInput
getInput = gets input

setInput  :: AlexInput -> P ()
setInput inp = modify $ \s ->
    s { input = inp }

pushLexState :: Int -> P ()
pushLexState ls = modify $ \s ->
    s { lexState = ls : lexState s }

popLexState :: P Int
popLexState = do
    ls <- getLexState
    modify $ \s ->
        s { lexState = tail (lexState s) }
    return ls

getLexState :: P Int
getLexState = gets (head . lexState)

getCurToken :: P (L Token)
getCurToken = gets curToken

setCurToken :: L Token -> P ()
setCurToken tok = modify $ \s -> s { curToken = tok }

getDialect :: P Dialect
getDialect = gets dialect

alexGetCharOrFail :: AlexInput -> P (Char, AlexInput)
alexGetCharOrFail inp =
    case alexGetChar inp of
      Nothing         -> unexpectedEOF inp
      Just (c, inp')  -> return (c, inp')

peekChar :: P Char
{-# INLINE peekChar #-}
peekChar = do
    inp <- getInput
    case T.uncons (alexBuf inp) of
      Nothing      -> unexpectedEOF inp
      Just (c, _)  -> return c

peekChars :: Int64 -> P String
{-# INLINE peekChars #-}
peekChars n = do
    inp    <-  getInput
    let s  =   T.take n (alexBuf inp)
    if T.length s < n
      then unexpectedEOF inp
      else return (T.unpack s)

nextChar :: P Char
{-# INLINE nextChar #-}
nextChar = do
    inp <- getInput
    case alexGetChar inp of
      Nothing         -> unexpectedEOF inp
      Just (c, inp')  -> setInput inp' >> return c

skipChar :: P ()
{-# INLINE skipChar #-}
skipChar = do
    inp <- getInput
    case alexGetChar inp of
      Nothing         -> unexpectedEOF inp
      Just (_, inp')  -> setInput inp'

failAt :: Loc -> String -> P a
failAt loc msg =
    throw $ ParserException loc (text msg)

lexerError :: AlexInput -> Doc -> P a
lexerError inp s =
    throw $ LexerException (alexPos inp) (text "lexer error on" <+> s)

unexpectedEOF :: AlexInput -> P a
unexpectedEOF inp =
    lexerError inp (text "unexpected end of file")

parserError :: Loc -> Doc -> P a
parserError loc msg =
    throw $ ParserException loc msg

unclosed :: Loc -> String -> P a
unclosed loc x =
    parserError (locEnd loc) (text "unclosed" <+> enquote (text x))

expected :: [String] -> Maybe String -> P b
expected alts after = do
    tok <- getCurToken
    expectedAt tok alts after

expectedAt :: L Token -> [String] -> Maybe String -> P b
expectedAt tok@(L loc _) alts after =
    parserError (locStart loc) (text "expected" <+> pprAlts alts <+> pprGot tok <+> pprAfter after)
  where
    pprAlts :: [String] -> Doc
    pprAlts []        = empty
    pprAlts [s]       = text s
    pprAlts [s1, s2]  = text s1 <+> text "or" <+> text s2
    pprAlts (s : ss)  = text s <> comma <+> pprAlts ss

    pprGot :: L Token -> Doc
    pprGot (L _ Teof)  = text "but reached end of file"
    pprGot (L _ t)     = text "but got" <+> enquote (ppr t)

    pprAfter :: Maybe String -> Doc
    pprAfter Nothing     = empty
    pprAfter (Just what) = text "after" <+> text what
