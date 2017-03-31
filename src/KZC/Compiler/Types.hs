{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      :  KZC.Compiler.Types
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Compiler.Types (
    ModuleInfo(..)
  ) where

import KZC.Name

data ModuleInfo = ModuleInfo
    { modSourcePath :: FilePath
    , modImports    :: [ModuleName]
    }
  deriving (Eq, Ord, Show)
