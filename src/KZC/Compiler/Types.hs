{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      :  KZC.Compiler.Types
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Compiler.Types (
    Dialect(..),
    dialectExts,

    ModuleInfo(..)
  ) where

import KZC.Name

data Dialect = Classic
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

dialectExts :: [(String, Dialect)]
dialectExts = [ (".wpl", Classic)
              , (".blk", Classic)
              ]

data ModuleInfo = ModuleInfo
    { modSourcePath :: FilePath
    , modImports    :: [ModuleName]
    }
  deriving (Eq, Ord, Show)
