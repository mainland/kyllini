-- |
-- Module      :  KZC.Quote.C
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cdrexel.edu

module KZC.Quote.C (
    ToIdent(..),
    ToConst(..),
    ToExp(..),
    cexp,
    cedecl,
    cdecl,
    csdecl,
    cenum,
    ctyquals,
    cty,
    cparam,
    cparams,
    cinit,
    cstm,
    cstms,
    citem,
    citems,
    cunit,
    cfun
  ) where

import Control.Monad ((>=>))
import qualified Data.ByteString.Char8 as B
import Data.Data (Data)
import qualified Language.C.Parser as P
import qualified Language.C.Syntax as C
import Language.C.Quote.Base (ToIdent(..), ToConst(..), ToExp(..), qqExp, qqPat)
import Language.Haskell.TH (Q)
import Language.Haskell.TH.Quote (QuasiQuoter(..), dataToExpQ, dataToPatQ)

exts :: [C.Extensions]
exts = []

typenames :: [String]
typenames = []

cdecl, cedecl, cenum, cexp, cfun, cinit, cparam, cparams, csdecl, cstm, cstms :: QuasiQuoter
citem, citems, ctyquals, cty, cunit :: QuasiQuoter
cdecl    = quasiquote exts typenames P.parseDecl
cedecl   = quasiquote exts typenames P.parseEdecl
cenum    = quasiquote exts typenames P.parseEnum
cexp     = quasiquote exts typenames P.parseExp
cfun     = quasiquote exts typenames P.parseFunc
cinit    = quasiquote exts typenames P.parseInit
cparam   = quasiquote exts typenames P.parseParam
cparams  = quasiquote exts typenames P.parseParams
csdecl   = quasiquote exts typenames P.parseStructDecl
cstm     = quasiquote exts typenames P.parseStm
cstms    = quasiquote exts typenames P.parseStms
citem    = quasiquote exts typenames P.parseBlockItem
citems   = quasiquote exts typenames P.parseBlockItems
ctyquals = quasiquote exts typenames P.parseTypeQuals
cty      = quasiquote exts typenames P.parseType
cunit    = quasiquote exts typenames P.parseUnit

parse :: [C.Extensions]
      -> [String]
      -> P.P a
      -> String
      -> Q a
parse exts typenames p s = do
    case P.parse (C.Antiquotation : exts) typenames p (B.pack s) Nothing of
      Left err -> fail (show err)
      Right x  -> return x

quasiquote :: Data a
           => [C.Extensions]
           -> [String]
           -> P.P a
           -> QuasiQuoter
quasiquote exts typenames p =
    QuasiQuoter { quoteExp  = parse exts typenames p >=> dataToExpQ qqExp
                , quotePat  = parse exts typenames p >=> dataToPatQ qqPat
                , quoteType = fail "C type quasiquoter undefined"
                , quoteDec  = fail "C declaration quasiquoter undefined"
                }
