-- |
-- Module      :  KZC.Cg.Code
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Cg.Code (
    Code(..)
  ) where

import Data.Foldable (toList)
import Data.Monoid
import Data.Sequence (Seq)
import Language.C.Pretty ()
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

-- | Contains generated code.
data Code = Code
    { -- | Top-level definitions
      codeDefs :: !(Seq C.Definition)
      -- | Thread-level declarations
    , codeThreadDecls :: !(Seq C.InitGroup)
      -- | Local declarations
    , codeDecls :: !(Seq C.InitGroup)
      -- | Local statements
    , codeStms :: !(Seq C.Stm)
    }
  deriving (Eq, Ord, Show)

instance Pretty Code where
    ppr c = stack $
            (map ppr . toList . codeDefs) c ++
            (map ppr . toList . codeThreadDecls) c ++
            (map ppr . toList . codeDecls) c ++
            (map ppr . toList . codeStms) c

instance Monoid Code where
    mempty = Code { codeDefs        = mempty
                  , codeThreadDecls = mempty
                  , codeDecls       = mempty
                  , codeStms        = mempty
                  }

    a `mappend` b = Code { codeDefs  = codeDefs a <> codeDefs b
                         , codeThreadDecls = codeThreadDecls a <> codeThreadDecls b
                         , codeDecls = codeDecls a <> codeDecls b
                         , codeStms  = codeStms a <> codeStms b
                         }
