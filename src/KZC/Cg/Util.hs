-- |
-- Module      :  KZC.Cg.Util
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Cg.Util (
    zencode
  ) where

import Data.Char (ord)
import Numeric (showHex)

-- | Z-encode a string. This converts a string with special characters into a
-- form that is guaranteed to be usable as an identifier by a C compiler or
-- assembler. See
-- <https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
-- Z-Encoding>
zencode :: String -> String
zencode = concatMap zenc
  where
    -- | Implementation of Z-encoding. See:
    -- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
    zenc :: Char -> [Char]
    zenc c | 'a' <= c && c <= 'y' = [c]
           | 'A' <= c && c <= 'Y' = [c]
           | '0' <= c && c <= '9' = [c]
    zenc 'z'  = "zz"
    zenc 'Z'  = "ZZ"
    zenc '('  = "ZL"
    zenc ')'  = "ZR"
    zenc '['  = "ZM"
    zenc ']'  = "ZN"
    zenc ':'  = "ZC"
    zenc '&'  = "za"
    zenc '|'  = "zb"
    zenc '^'  = "zc"
    zenc '$'  = "zd"
    zenc '='  = "ze"
    zenc '>'  = "zg"
    zenc '#'  = "zh"
    zenc '.'  = "zi"
    zenc '<'  = "zl"
    zenc '-'  = "zm"
    zenc '!'  = "zn"
    zenc '+'  = "zp"
    zenc '\'' = "zq"
    zenc '\\' = "zr"
    zenc '/'  = "zs"
    zenc '*'  = "zt"
    zenc '_'  = "zu"
    zenc '%'  = "zv"
    zenc c    = "z" ++ hexOf c ++ "U"

    hexOf :: Char -> String
    hexOf c =
        case showHex (ord c) "" of
          [] -> []
          h@(c : _) | 'a' <= c && c <= 'f' -> '0' : h
                    | otherwise            -> h
