-- -*- mode: haskell -*-

{
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS -w #-}

--------------------------------------------------------------------------------
-- |
-- Module      : Language.Ziria.Parser.Lexer
-- Copyright   : (c) 2014-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

module Language.Ziria.Parser.Lexer (
    lexToken,
    lexTokens
  ) where

import Control.Applicative
import Control.Monad (when)
import Control.Monad.Exception
import Control.Monad.State
import Data.Char (chr,
                  isDigit,
                  isHexDigit,
                  isOctDigit,
                  toLower)
import Data.List (intersperse)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Symbol
import qualified Data.Text.Lazy as T
import Text.PrettyPrint.Mainland

import Language.Ziria.Parser.Alex
import Language.Ziria.Parser.Monad
import Language.Ziria.Parser.Tokens
import Language.Ziria.Syntax (Dialect(..))

-- import Debug.Trace (trace)
}

--
-- These definitions are lifted straight from the haskell Report
-- See https://www.haskell.org/definition/haskell98-report.pdf
--

$special   = [\(\)\,\;\[\]\`\{\}]

$uniWhite  = []
$whitechar = [\ \t\n\r\f\v]

$ascSmall = [a-z]
$uniSmall = []
$small    = [$ascSmall $uniSmall \_]

$ascLarge = [A-Z]
$uniLarge = []
$large    = [$ascLarge $uniLarge]

$alpha     = [$small $large]

$ascSymbol = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]
$uniSymbol = []
$symbol    = [$ascSymbol $uniSymbol] # [$special \_\:\"\']

$ascDigit = [0-9]
$uniDigit = []
$digit    = [$ascDigit $uniDigit]
$octit    = [0-7]
$hexit    = [$digit A-F a-f]

$graphic  = [$small $large $symbol $digit $special \:\"\']

-- Identifiers
$idchar = [$small $large $digit \']
@id     = $alpha $idchar*

-- Types
@width = [1-9] [0-9]*

@frac = @width "_" @width

-- Numerical constants
@decimal     = $digit+
@octal       = $octit+
@hexadecimal = $hexit+
@exponent    = [eE] [\-\+] @decimal | [eE] @decimal

-- String and characters constants
$charesc  = [abfnrtv\\\"\'\&]
$cntrl    = [$ascLarge\@\[\\\]\^\_]
@ascii    = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
          | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
          | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN
          | EM | SUB | ESC | FS | GS | RS | US | SP | DEL
@escape   = \\ ($charesc | @ascii | @decimal | o @octal | x @hexadecimal)

-- For characters, since Alex doesn't accept the syntax @escape # [\\\&]
$ccharesc = [abfnrtv\"\']
@cescape  = \\ ($ccharesc | @ascii | @decimal | o @octal | x @hexadecimal)

@gap     = \\ $whitechar+ \\
@char    = \' ($graphic # [\'\\] | " " | @cescape) \'
@string  = \" ($graphic # [\"\\] | " " | @escape | @gap)* \"

ziria :-

<0> {
  ^ $whitechar* "#line" $whitechar+ $digit+ $whitechar+ \" [^\"]* \" .* { setLineFromPragma }
  ^ $whitechar* "#" $whitechar+ $digit+ $whitechar+ \" [^\"]* \" .*     { setLineFromPragma }

  $whitechar+ ;
  "--"\-*.*   ;
  "//".*      ;

  "{-" { lexNestedComment }

  "i" @width / { ifKyllini } { lexTypeWidth 1 Ti }
  "u" @width / { ifKyllini } { lexTypeWidth 1 Tu }
  "f32"      / { ifKyllini } { token $ Tf 32 }
  "f64"      / { ifKyllini } { token $ Tf 64 }

  "q"  @width / { ifKyllini } { lexTypeWidth 1 (Tq 0) }
  "q"  @frac  / { ifKyllini } { lexTypeFrac 1 Tq }
  "uq" @width / { ifKyllini } { lexTypeWidth 2 (Tuq 0) }
  "uq" @frac  / { ifKyllini } { lexTypeFrac 2 Tuq }

  @id { identifier }

  @decimal            { lexConst (TintConst S) }
  0[oO] @octal        { lexConst (TintConst S) }
  0[xX] @hexadecimal  { lexConst (TintConst S) }

  @decimal [uU]            { lexConst1 (TintConst U) }
  0[oO] @octal [uU]        { lexConst1 (TintConst U) }
  0[xX] @hexadecimal [uU]  { lexConst1 (TintConst U) }

  @decimal (\. @decimal @exponent? | @exponent) { lexFloat }

  @char   { lexConst TcharConst }
  @string { lexConst TstringConst }

  "("   { token Tlparen }
  ")"   { token Trparen }
  "["   { token Tlbrack }
  "]"   { token Trbrack }
  "{"   { token Tlbrace }
  "}"   { token Trbrace }

  "!"   { token Tbang }
  "."   { token Tdot }
  ","   { token Tcomma }
  ";"   { token Tsemi }
  ":"   { token Tcolon }

  "+"   { token Tplus }
  "-"   { token Tminus }
  "*"   { token Tstar }
  "/"   { token Tdiv }
  "%"   { token Trem }
  "**"  { token Tpow }
  "<<"  { token Tshiftl }
  ">>"  { token Tshiftr }

  "=="   { token Teq }
  "!="   { token Tne }
  "<"    { token Tlt }
  ">"    { token Tgt }
  "<="   { token Tle }
  ">="   { token Tge }

  "~"    { token Tbneg }
  "&"    { token Tband }
  "|"    { token Tbor }
  "^"    { token Tbxor }

  "&&"   { token Tland }
  "||"   { token Tlor }

  "="     { token Tdef }
  ":="    / { ifClassic } { token Tassign }
  "<-"    { token Tbind }
  ">>>"   { token Tcompose }
  "|>>>|" { token Tpcompose }

  "'0" { token TzeroBit }
  "'1" { token ToneBit }

  -- For the new dialect
  "->" / { ifKyllini } { token Tarrow }
  ".." / { ifKyllini } { token Tdotdot }
}

{
-- | The components of an 'AlexPredicate' are the predicate state, input stream
-- before the token, length of the token, input stream after the token.
type AlexPredicate =  PState
                   -> AlexInput
                   -> Int
                   -> AlexInput
                   -> Bool

ifDialect :: Dialect -> AlexPredicate
ifDialect d s _ _ _ = dialect s == d

ifClassic :: AlexPredicate
ifClassic = ifDialect Classic

ifKyllini :: AlexPredicate
ifKyllini = ifDialect Kyllini

identifier :: Action P Token
identifier beg end =
    case Map.lookup ident keywordMap of
      Nothing  -> do isStruct <- isStructIdentifier ident
                     if isStruct
                        then token (TstructIdentifier ident) beg end
                        else token (Tidentifier ident) beg end
      Just (tok, Nothing) -> token tok beg end
      Just (tok, Just d') -> do d <- getDialect
                                if d == d'
                                  then token tok beg end
                                  else token (Tidentifier ident) beg end
  where
    ident :: Symbol
    ident = intern (inputString beg end)

lexTypeWidth :: Int -> (Int -> Token) -> Action P Token
lexTypeWidth n k beg end = token (k i) beg end
  where
    it :: T.Text
    it = T.drop (fromIntegral n) (inputText beg end)

    i :: Int
    i = (read . T.unpack) it

lexTypeFrac :: Int -> (Int -> Int -> Token) -> Action P Token
lexTypeFrac n k beg end = token (k i f) beg end
  where
    it, ft :: T.Text
    [it, ft] = (T.split (== '_') . T.drop (fromIntegral n)) (inputText beg end)

    i, f :: Int
    i = (read . T.unpack) it
    f = (read . T.unpack) ft

lexConst :: Read a => ((String, a) -> Token) -> Action P Token
lexConst tok beg end = do
    token (tok (s, read s)) beg end
  where
    s :: String
    s = inputString beg end

-- Lex a constant, dropping the final character.
lexConst1 :: Read a => ((String, a) -> Token) -> Action P Token
lexConst1 tok beg end = do
    token (tok (s, read s)) beg end1
  where
    s :: String
    s = inputString beg end1

    end1 :: AlexInput
    end1 = end { alexOff = alexOff end -1 }

lexFloat :: Action P Token
lexFloat beg end =
    case i of
      [n] -> return $ locateTok beg end (TfloatConst (s, fromRational n))
      _   -> fail "bad parse for float"
  where
    s :: String
    s = inputString beg end

    i :: [Rational]
    i = do (n, _) <- readRational s
           return n

setLineFromPragma :: Action P Token
setLineFromPragma beg end = do
    inp <- getInput
    setInput inp { alexPos = pos' }
    lexToken
  where
    (_ : l : ws) = words (inputString beg end)
    line = read l - 1
    filename = (takeWhile (/= '\"') . drop 1 . concat . intersperse " ") ws

    pos' :: Pos
    pos' = Pos filename line 1 (posCoff (alexPos beg))

lexNestedComment :: Action P Token
lexNestedComment beg _ = do
    scan 1
    lexToken
  where
    scan :: Int -> P ()
    scan 0 =
        return ()

    scan n = do
        c <- nextChar
        case c of
          '-' -> do
              c2 <- nextChar
              case c2 of
                '}'  -> scan (n-1)
                _    -> scan n
          '{' -> do
              c2 <- nextChar
              case c2 of
                '-'  -> scan (n+1)
                _    -> scan n
          _ -> scan n

    retreatPos :: Pos -> Int -> Pos
    retreatPos (Pos f l c coff) n = Pos f l (c-n) (coff-n)

lexToken :: P (L Token)
lexToken = do
    beg  <- getInput
    st   <- get
    case alexScanUser st beg 0 of
      AlexEOF ->
          return $ L (Loc (alexPos beg) (alexPos beg)) Teof
      AlexError end ->
          lexerError end (text rest)
        where
          rest :: String
          rest = T.unpack $ T.take 80 $ T.drop (alexOff end) (alexBuf end)

      AlexSkip end _ ->
          setInput end >> lexToken

      AlexToken end _ t ->
          setInput end >> t beg end
{-
          do x <- setInput end >> t beg end
             return $! trace (show x) x
-}

lexTokens :: MonadException m
          => Dialect
          -> T.Text
          -> Pos
          -> m [L Token]
lexTokens dialect buf start =
    liftException (evalP tokens (emptyPState dialect buf start))
  where
    tokens :: P [L Token]
    tokens = do
        t <- lexToken
        case t of
          L _ Teof  -> return [t]
          _         -> (t :) <$> tokens
}
