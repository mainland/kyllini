-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    Cg,
    CgEnv
  ) where

import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)

import KZC.Auto.Lint (Tc)
import KZC.Monad.SEFKT (SEFKT)

type Cg a = SEFKT (ReaderT CgEnv (StateT CgState Tc)) a

data CgEnv

instance Show CgEnv where

data CgState
