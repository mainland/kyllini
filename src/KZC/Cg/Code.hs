{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Cg.Code
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Cg.Code (
    Code(..)
  ) where

import Data.Foldable (toList)
import Data.Monoid
import Data.Sequence (Seq,
                      ViewL((:<)),
                      ViewR((:>)),
                      (<|),
                      viewl,
                      viewr)
import Language.C.Pretty ()
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Quote.C

-- | Contains generated code.
data Code = Code
    { -- | Top-level definitions
      codeDefs :: !(Seq C.Definition)
    , -- | Thread-level declarations
      codeThreadDecls :: !(Seq C.InitGroup)
    , -- | Initialization
      codeThreadInitStms :: !(Seq C.Stm)
    , -- | Cleanup
      codeThreadCleanupStms :: !(Seq C.Stm)
    , -- | Local declarations
      codeDecls :: !(Seq C.InitGroup)
    , -- | Local statements
      codeStms :: !(Seq C.Stm)
    }
  deriving (Eq, Ord, Show)

instance Pretty Code where
    ppr c = stack $
            (map ppr . toList . codeDefs) c ++
            (map ppr . toList . codeThreadDecls) c ++
            (map ppr . toList . codeThreadInitStms) c ++
            (map ppr . toList . codeThreadCleanupStms) c ++
            (map ppr . toList . codeDecls) c ++
            (map ppr . toList . codeStms) c

instance Monoid Code where
    mempty = Code { codeDefs              = mempty
                  , codeThreadDecls       = mempty
                  , codeThreadInitStms    = mempty
                  , codeThreadCleanupStms = mempty
                  , codeDecls             = mempty
                  , codeStms              = mempty
                  }

    a `mappend` b =
        Code { codeDefs              = codeDefs a <> codeDefs b
             , codeThreadDecls       = codeThreadDecls a <> codeThreadDecls b
             , codeThreadInitStms    = codeThreadInitStms a <> codeThreadInitStms b
             , codeThreadCleanupStms = codeThreadCleanupStms a <> codeThreadCleanupStms b
             , codeDecls             = codeDecls a <> codeDecls b
             , codeStms              = case (viewr (codeStms a), viewl (codeStms b)) of
                                         (stms1 :> [cstm|$id:lbl: ;|], stm :< stms2) ->
                                              stms1 <> ([cstm|$id:lbl: $stm:stm|] <| stms2)
                                         _ -> codeStms a <> codeStms b
             }
