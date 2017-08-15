{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      :  KZC.Compiler.Types
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Compiler.Types (
    ModuleInfo(..)
  ) where

import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Util.Summary

data ModuleInfo = ModuleInfo
    { modName       :: Maybe ModuleName
    , modSourcePath :: FilePath
    , modImports    :: [ModuleName]
    }
  deriving (Show)

-- Only compare 'modSourcePath' since we may not have a 'modName' and
-- 'modImports' may be unordered. We should really compare full paths.

instance Eq ModuleInfo where
    x == y = modSourcePath x == modSourcePath y

instance Ord ModuleInfo where
    compare x y = compare (modSourcePath x) (modSourcePath y)

instance Pretty ModuleInfo where
    ppr ModuleInfo { modName = Just n }     = ppr n
    ppr ModuleInfo { modSourcePath = path } = dquotes (text path)

instance Summary ModuleInfo where
    summary ModuleInfo { modName = Just n }     = ppr n
    summary ModuleInfo { modSourcePath = path } = dquotes (text path)
