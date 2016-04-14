{-# LANGUAGE RoleAnnotations #-}

-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2015-2016 Drexel University
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

type Cg l a = SEFKT (ReaderT (CgEnv l) (StateT (CgState l) Tc)) a

type role CgEnv nominal

data CgEnv l

data CgState l
