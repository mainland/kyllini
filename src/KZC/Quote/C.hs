{-# LANGUAGE CPP #-}
-- Need this for haddock. See 7e88adcc.
{-# LANGUAGE TemplateHaskell #-}

{-|
Module      :  KZC.Quote.C
Copyright   :  (c) 2015-2016 Drexel University
License     :  BSD-style
Maintainer  :  mainland@cs.drexel.edu

This module recreates the standard C quasiquoters, but location information is
only included when the @DEBUG@is defined. By not including location information
when parsing a quasiquote, all location information in an expression comes from
whatever the quasioquote consumer attaches to the expressions in
constructs. This makes it easier to take generated code with, e.g., locations
from a source code file.

When debugging, sometimes often /do/ want location information to come from the
source code file where the quasioquote was written. Defining @DEBUG@ enables this.
-}

module KZC.Quote.C (
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
#if defined(DEBUG)
import Data.Loc (Pos(..))
#endif /* defined(DEBUG) */
import qualified Language.C.Parser as P
import qualified Language.C.Syntax as C
import Language.C.Quote.Base (qqExp, qqPat)
import Language.Haskell.TH (Q)
#if defined(DEBUG)
import Language.Haskell.TH (Loc(..), location)
#endif /* defined(DEBUG) */
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
#if defined(DEBUG)
    loc <- fmap (Just . locToPos) location
#else /* !defined(DEBUG) */
    let loc = Nothing
#endif /* !defined(DEBUG) */
    case P.parse (C.Antiquotation : exts) typenames p (B.pack s) loc of
      Left err -> fail (show err)
      Right x  -> return x
#if defined(DEBUG)
  where
    locToPos :: Language.Haskell.TH.Loc -> Pos
    locToPos loc = Pos (loc_filename loc)
                       ((fst . loc_start) loc)
                       ((snd . loc_start) loc)
                       0
#endif /* defined(DEBUG) */

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
