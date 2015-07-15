-- |
-- Module      :  KZC.Flags
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Flags where

import Data.Monoid

data Flags = Flags
    { pprintF    :: Bool
    , checkF     :: Bool
    , lintF      :: Bool
    , warnErrorF :: Bool
    , traceTcF   :: Bool
    , traceLintF :: Bool
    , dumpTcF    :: Bool
    , includesF  :: [String]
    , inputF     :: Maybe String
    , outputF    :: Maybe String
    }

instance Monoid Flags where
    mempty =
        Flags { pprintF    = False
              , checkF     = False
              , lintF      = False
              , warnErrorF = False
              , traceTcF   = False
              , traceLintF = False
              , dumpTcF    = False
              , includesF  = []
              , inputF     = Nothing
              , outputF    = Nothing
              }

    mappend f1 f2 =
        Flags { pprintF    = pprintF f1 || pprintF f2
              , checkF     = checkF f1 || checkF f2
              , lintF      = lintF f1 || lintF f2
              , warnErrorF = warnErrorF f1 || warnErrorF f2
              , traceTcF   = traceTcF f1 || traceTcF f2
              , traceLintF = traceLintF f1 || traceLintF f2
              , dumpTcF    = dumpTcF f1 || dumpTcF f2
              , includesF  = includesF f1 <> includesF f2
              , inputF     = inputF f1 <> inputF f2
              , outputF    = outputF f1 <> outputF f2
              }
