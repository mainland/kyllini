{-# LANGUAGE CPP #-}

-- |
-- Module      :  KZC.Rename.State
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Rename.State (
    RnEnv(..),
    defaultRnEnv
  ) where

import Data.Map (Map)
import qualified Data.Map as Map

import Language.Ziria.Syntax

data RnEnv = RnEnv
    { vars      :: Map Var Var
    , compVars  :: Map Var Var
    , compScope :: Bool
    }

defaultRnEnv :: RnEnv
defaultRnEnv = RnEnv
    { vars       = Map.empty
    , compVars   = Map.empty
    , compScope  = False
    }
