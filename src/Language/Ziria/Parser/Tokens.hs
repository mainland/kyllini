{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Language.Ziria.Parser.Tokens
-- Copyright   : (c) 2014-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Parser.Tokens (
    Signedness(..),
    Token(..),
    keywords,
    keywordMap,
    unopFuns,
    unopFunMap
  ) where

import qualified Data.Map as Map
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid ((<>))
#endif /* !MIN_VERSION_base(4,11,0) */
import Data.Symbol
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import Language.Ziria.Syntax

data Signedness = S
                | U
  deriving (Eq, Ord, Read, Show)

data Token = Teof
           | TintConst Signedness (String, Integer)
           | TfloatConst (String, Double)
           | TcharConst (String, Char)
           | TstringConst (String, String)
           | Tidentifier Symbol
           | TstructIdentifier Symbol

           | TzeroBit
           | ToneBit
           | TC
           | TST
           | TT
           | Tarr
           | Tautoinline
           | Tbit
           | Tbool
           | Tcomp
           | Tdo
           | Tdouble
           | Telse
           | Temit
           | Temits
           | Terror
           | Texternal
           | Tfalse
           | Tfilter
           | Tfloat
           | Tfor
           | Tforceinline
           | Tfun
           | Tif
           | Timport
           | Timpure
           | Tin
           | Tint
           | Tint8
           | Tint16
           | Tint32
           | Tint64
           | Tlength
           | Tlet
           | Tmap
           | Tnot
           | Tnoinline
           | Tnounroll
           | Tprint
           | Tprintln
           | Tread
           | Trepeat
           | Treturn
           | Tseq
           | Tstandalone
           | Tstruct
           | Ttake
           | Ttakes
           | Tthen
           | Ttimes
           | Ttrue
           | Tuint
           | Tuint8
           | Tuint16
           | Tuint32
           | Tuint64
           | Tunroll
           | Tuntil
           | Tvar
           | Twhile
           | Twrite

           | Tplus   -- ^ Addition
           | Tminus  -- ^ Subtraction
           | Tstar   -- ^ Multiplication
           | Tdiv    -- ^ Division
           | Trem    -- ^ Remainder
           | Tpow    -- ^ Raise to power
           | Tshiftl -- ^ Shift right
           | Tshiftr -- ^ Shift left

           | Teq -- ^ equal
           | Tne -- ^ Not equal
           | Tlt -- ^ Less than
           | Tgt -- ^ Greater than
           | Tle -- ^ Less than or equal
           | Tge -- ^ Greater than or equal

           | Tbneg -- ^ Bit-wise negation
           | Tband -- ^ Bit-wise and
           | Tbor  -- ^ Bit-wise or
           | Tbxor -- ^ Bit-wise xor

           | Tland -- ^ Logical and
           | Tlor  -- ^ Logical or

           | Tdef      -- ^ Bind (=)
           | Tassign   -- ^ Assignment (:=)
           | Tbind     -- ^ Bind (<-)
           | Tcompose  -- ^ Composition (>>>)
           | Tpcompose -- ^ Parallel composition (|>>>|)

           | Tlparen
           | Trparen
           | Tlbrack
           | Trbrack
           | Tlbrace
           | Trbrace

           | Tbang
           | Tdot
           | Tcomma
           | Tsemi
           | Tcolon

           -- Tokens for the new dialect
           | Tbitcast
           | Tcast
           | Tmut
           | Tnat
           | Ttype

           | TEq
           | TOrd
           | TBool
           | TNum
           | TIntegral
           | TFractional
           | TBits

           | Ti Int      -- ^ General-width signed integer type
           | Tu Int      -- ^ General-width unsigned integer type
           | Tf Int      -- ^ General-width float type
           | Tq Int Int  -- ^ Signed fixed-point type
           | Tuq Int Int -- ^ Unsigned fixed-point type

           | Tarrow  -- ^ Right arrow (->)
           | Tdotdot -- ^ Range (..)
  deriving (Eq, Ord, Read, Show)

instance Pretty Token where
    ppr Teof = text "end of file"

    ppr (TintConst _ (s, _))  = text s
    ppr (TfloatConst (s, _))  = text s
    ppr (TcharConst (s, _))   = text s
    ppr (TstringConst (s, _)) = text s
    ppr (Tidentifier sym)     = (text . unintern) sym
    ppr (TstructIdentifier sym) = (text . unintern) sym

    ppr TzeroBit     = text "'0"
    ppr ToneBit      = text "'1"
    ppr TC           = text "C"
    ppr TST          = text "ST"
    ppr TT           = text "T"
    ppr Tarr         = text "arr"
    ppr Tautoinline  = text "autoinline"
    ppr Tbit         = text "bit"
    ppr Tbool        = text "bool"
    ppr Tcomp        = text "comp"
    ppr Tdo          = text "do"
    ppr Tdouble      = text "double"
    ppr Telse        = text "else"
    ppr Temit        = text "emit"
    ppr Temits       = text "emits"
    ppr Terror       = text "error"
    ppr Texternal    = text "external"
    ppr Tfalse       = text "false"
    ppr Tfilter      = text "filter"
    ppr Tfloat       = text "float"
    ppr Tfor         = text "for"
    ppr Tforceinline = text "Tforceinline"
    ppr Tfun         = text "fun"
    ppr Tif          = text "if"
    ppr Timport      = text "import"
    ppr Timpure      = text "impure"
    ppr Tin          = text "in"
    ppr Tint         = text "int"
    ppr Tint8        = text "int8"
    ppr Tint16       = text "int16"
    ppr Tint32       = text "int32"
    ppr Tint64       = text "int64"
    ppr Tlength      = text "length"
    ppr Tlet         = text "let"
    ppr Tmap         = text "map"
    ppr Tnot         = text "not"
    ppr Tnoinline    = text "noinline"
    ppr Tnounroll    = text "nounroll"
    ppr Tprint       = text "print"
    ppr Tprintln     = text "println"
    ppr Tread        = text "read"
    ppr Trepeat      = text "repeat"
    ppr Treturn      = text "return"
    ppr Tseq         = text "seq"
    ppr Tstandalone  = text "standalone"
    ppr Tstruct      = text "struct"
    ppr Ttake        = text "take"
    ppr Ttakes       = text "takes"
    ppr Tthen        = text "then"
    ppr Ttimes       = text "times"
    ppr Ttrue        = text "true"
    ppr Tuint        = text "uint"
    ppr Tuint8       = text "uint8"
    ppr Tuint16      = text "uint16"
    ppr Tuint32      = text "uint32"
    ppr Tuint64      = text "uint64"
    ppr Tunroll      = text "unroll"
    ppr Tuntil       = text "until"
    ppr Tvar         = text "var"
    ppr Twhile       = text "while"
    ppr Twrite       = text "write"

    ppr Tplus   = text "+"
    ppr Tminus  = text "-"
    ppr Tstar   = text "*"
    ppr Tdiv    = text "/"
    ppr Trem    = text "%"
    ppr Tpow    = text "**"
    ppr Tshiftl = text "<<"
    ppr Tshiftr = text ">>"

    ppr Teq = text "=="
    ppr Tne = text "!="
    ppr Tlt = text "<"
    ppr Tgt = text ">"
    ppr Tle = text "<="
    ppr Tge = text ">="

    ppr Tbneg = text "~"
    ppr Tband = text "&"
    ppr Tbor  = text "|"
    ppr Tbxor = text "^"

    ppr Tland = text "&&"
    ppr Tlor  = text "||"

    ppr Tdef      = text "="
    ppr Tassign   = text ":="
    ppr Tbind     = text "<-"
    ppr Tcompose  = text ">>>"
    ppr Tpcompose = text "|>>>|"

    ppr Tlparen = text "("
    ppr Trparen = text ")"
    ppr Tlbrack = text "["
    ppr Trbrack = text "]"
    ppr Tlbrace = text "{"
    ppr Trbrace = text "}"

    ppr Tbang  = text "!"
    ppr Tdot   = text "."
    ppr Tcomma = text ","
    ppr Tsemi  = text ";"
    ppr Tcolon = text ":"

    -- Tokens for the new dialect
    ppr Tbitcast = text "bitcast"
    ppr Tcast    = text "cast"
    ppr Tmut     = text "mut"
    ppr Tnat     = text "nat"
    ppr Ttype    = text "type"

    ppr TEq         = text "Eq"
    ppr TOrd        = text "Ord"
    ppr TBool       = text "Bool"
    ppr TNum        = text "Num"
    ppr TIntegral   = text "Integral"
    ppr TFractional = text "Fractional"
    ppr TBits       = text "Bits"

    ppr (Ti n)    = text "i" <> ppr n
    ppr (Tu n)    = text "u" <> ppr n
    ppr (Tf n)    = text "f" <> ppr n
    ppr (Tq 0 f)  = text "q" <> ppr f
    ppr (Tq i f)  = text "q" <> ppr i <> char '_' <> ppr f
    ppr (Tuq 0 f) = text "uq" <> ppr f
    ppr (Tuq i f) = text "uq" <> ppr i <> char '_' <> ppr f

    ppr Tarrow  = text "->"
    ppr Tdotdot = text ".."

keywords :: [(Symbol, Token, Maybe Dialect)]
keywords = [ ("C",           TC,           Nothing)
           , ("ST",          TST,          Nothing)
           , ("T",           TT,           Nothing)
           , ("arr",         Tarr,         Nothing)
           , ("bit",         Tbit,         Nothing)
           , ("bool",        Tbool,        Nothing)
           , ("autoinline",  Tautoinline,  Nothing)
           , ("comp",        Tcomp,        Nothing)
           , ("do",          Tdo,          Just Classic)
           , ("double",      Tdouble,      Nothing)
           , ("else",        Telse,        Nothing)
           , ("emit",        Temit,        Nothing)
           , ("emits",       Temits,       Nothing)
           , ("error",       Terror,       Nothing)
           , ("external",    Texternal,    Nothing)
           , ("false",       Tfalse,       Nothing)
           , ("filter",      Tfilter,      Nothing)
           , ("float",       Tfloat,       Nothing)
           , ("for",         Tfor,         Nothing)
           , ("forceinline", Tforceinline, Nothing)
           , ("fun",         Tfun,         Nothing)
           , ("if",          Tif,          Nothing)
           , ("import",      Timport,      Nothing)
           , ("impure",      Timpure,      Nothing)
           , ("in",          Tin,          Nothing)
           , ("int",         Tint,         Nothing)
           , ("int8",        Tint8,        Nothing)
           , ("int16",       Tint16,       Nothing)
           , ("int32",       Tint32,       Nothing)
           , ("int64",       Tint64,       Nothing)
           , ("length",      Tlength,      Nothing)
           , ("let",         Tlet,         Nothing)
           , ("map",         Tmap,         Nothing)
           , ("not",         Tnot,         Nothing)
           , ("noinline",    Tnoinline,    Nothing)
           , ("nounroll",    Tnounroll,    Nothing)
           , ("print",       Tprint,       Nothing)
           , ("println",     Tprintln,     Nothing)
           , ("read",        Tread,        Nothing)
           , ("repeat",      Trepeat,      Nothing)
           , ("return",      Treturn,      Nothing)
           , ("seq",         Tseq,         Just Classic)
           , ("standalone",  Tstandalone,  Nothing)
           , ("struct",      Tstruct,      Nothing)
           , ("take",        Ttake,        Nothing)
           , ("takes",       Ttakes,       Nothing)
           , ("then",        Tthen,        Nothing)
           , ("times",       Ttimes,       Nothing)
           , ("true",        Ttrue,        Nothing)
           , ("uint",        Tuint,        Nothing)
           , ("uint8",       Tuint8,       Nothing)
           , ("uint16",      Tuint16,      Nothing)
           , ("uint32",      Tuint32,      Nothing)
           , ("uint64",      Tuint64,      Nothing)
           , ("unroll",      Tunroll,      Nothing)
           , ("until",       Tuntil,       Nothing)
           , ("var",         Tvar,         Just Classic)
           , ("while",       Twhile,       Nothing)
           , ("write",       Twrite,       Nothing)

           -- Tokens for the new dialect
           , ("bitcast", Tbitcast, Just Kyllini)
           , ("cast",    Tcast,    Just Kyllini)
           , ("mut",     Tmut,     Just Kyllini)
           -- We allow the 'nat' keyword in the classic dialect, but it's only
           -- legal in the lenient parser.
           , ("nat",     Tnat,     Nothing)
           , ("type",    Ttype,    Just Kyllini)

           , ("Eq",         TEq,         Just Kyllini)
           , ("Ord",        TOrd,        Just Kyllini)
           , ("Bool",       TBool,       Just Kyllini)
           , ("Num",        TNum,        Just Kyllini)
           , ("Integral",   TIntegral,   Just Kyllini)
           , ("Fractional", TFractional, Just Kyllini)
           , ("Bits",       TBits,       Just Kyllini)
           ]

keywordMap :: Map.Map Symbol (Token, Maybe Dialect)
keywordMap = Map.fromList (map f keywords)
  where
    f  ::  (Symbol, Token, Maybe Dialect)
       ->  (Symbol, (Token, Maybe Dialect))
    f (s, t, d) = (s, (t, d))

-- | Unary functions that are written using function call syntax.
unopFuns :: [(Symbol, Unop)]
unopFuns = [ ("abs",   Abs)
           , ("exp",   Exp)
           , ("log",   Log)
           , ("sqrt",  Sqrt)
           , ("sin",   Sin)
           , ("cos",   Cos)
           , ("tan",   Tan)
           , ("asin",  Asin)
           , ("acos",  Acos)
           , ("atan",  Atan)
           , ("sinh",  Sinh)
           , ("cosh",  Cosh)
           , ("tanh",  Tanh)
           , ("asinh", Asinh)
           , ("acosh", Acosh)
           , ("atanh", Atanh)
           ]

-- | Map unary functions that are written using function call syntax to the
-- appropriate 'Unop'.
unopFunMap :: Map.Map Symbol Unop
unopFunMap = Map.fromList unopFuns
