{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import qualified Language.Ziria.Syntax as Z

import KZC.Name
import KZC.Check.Types
import KZC.Traits
import KZC.Util.Derive
import KZC.Util.Uniq

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Z.Field)
DERIVE(Z.Struct)
DERIVE(Uniq)
DERIVE(Name)
DERIVE(NameSort)
DERIVE(TyVar)
DERIVE(IP)
DERIVE(FP)
DERIVE(Type)
DERIVE(MetaTv)
DERIVE(Trait)
DERIVE(Kind)
DERIVE(R)
DERIVE(MetaRv)
DERIVE(MetaKv)
DERIVE(StructDef)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(TyVar)
    DERIVE(Type)
    DERIVE(StructDef)
