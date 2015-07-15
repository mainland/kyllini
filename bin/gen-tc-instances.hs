{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Derive
import KZC.Name
import KZC.Check.Types
import KZC.Uniq

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Uniq)
DERIVE(Name)
DERIVE(IVar)
DERIVE(Struct)
DERIVE(TyVar)
DERIVE(W)
DERIVE(Type)
DERIVE(MetaTv)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Type)
