{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Backend.C.Code
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Backend.C.Code (
    CodeBlock(..),
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

import KZC.Backend.C.Util
import KZC.Quote.C

data CodeBlock = CodeBlock
    { -- | Block-level declarations
      blockDecls :: !(Seq C.InitGroup)
    , -- | Initialization
      blockInitStms :: !(Seq C.Stm)
    , -- | Cleanup
      blockCleanupStms :: !(Seq C.Stm)
    , -- | Local statements
      blockStms :: !(Seq C.Stm)
    }
  deriving (Eq, Ord, Show)

instance Pretty CodeBlock where
    ppr c = stack $
            (map ppr . toList . blockDecls) c ++
            (map ppr . toList . blockInitStms) c ++
            (map ppr . toList . blockCleanupStms) c ++
            (map ppr . toList . blockStms) c

instance Monoid CodeBlock where
    mempty = CodeBlock
        { blockDecls       = mempty
        , blockInitStms    = mempty
        , blockCleanupStms = mempty
        , blockStms        = mempty
        }

    a `mappend` b = CodeBlock
        { blockDecls       = blockDecls a <> blockDecls b
        , blockInitStms    = blockInitStms a <> blockInitStms b
        , blockCleanupStms = blockCleanupStms a <> blockCleanupStms b
        , blockStms        = case (viewr (blockStms a), viewl (blockStms b)) of
                               (stms1 :> [cstm|$id:lbl: ;|], stm :< stms2) ->
                                    stms1 <> ([cstm|$id:lbl: $stm:stm|] <| stms2)
                               _ -> blockStms a <> blockStms b
        }

instance ToBlockItems CodeBlock where
    toBlockItems b =
        toBlockItems (blockDecls b) ++
        toBlockItems (blockInitStms b) ++
        toBlockItems (blockStms b) ++
        toBlockItems (blockCleanupStms b)

-- | Contains generated code.
data Code = Code
    { -- | Top-level definitions
      codeDefs :: !(Seq C.Definition)
    , -- | Top-level function definitions
      codeFunDefs :: !(Seq C.Definition)
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
            (map ppr . toList . codeFunDefs) c ++
            (map ppr . toList . codeThreadDecls) c ++
            (map ppr . toList . codeThreadInitStms) c ++
            (map ppr . toList . codeThreadCleanupStms) c ++
            (map ppr . toList . codeDecls) c ++
            (map ppr . toList . codeStms) c

instance Monoid Code where
    mempty = Code
        { codeDefs              = mempty
        , codeFunDefs           = mempty
        , codeThreadDecls       = mempty
        , codeThreadInitStms    = mempty
        , codeThreadCleanupStms = mempty
        , codeDecls             = mempty
        , codeStms              = mempty
        }

    a `mappend` b = Code
        { codeDefs              = codeDefs a <> codeDefs b
        , codeFunDefs           = codeFunDefs a <> codeFunDefs b
        , codeThreadDecls       = codeThreadDecls a <> codeThreadDecls b
        , codeThreadInitStms    = codeThreadInitStms a <> codeThreadInitStms b
        , codeThreadCleanupStms = codeThreadCleanupStms a <> codeThreadCleanupStms b
        , codeDecls             = codeDecls a <> codeDecls b
        , codeStms              = case (viewr (codeStms a), viewl (codeStms b)) of
                                    (stms1 :> [cstm|$id:lbl: ;|], stm :< stms2) ->
                                         stms1 <> ([cstm|$id:lbl: $stm:stm|] <| stms2)
                                    _ -> codeStms a <> codeStms b
        }
