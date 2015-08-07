{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Derive
import KZC.Name
import KZC.Uniq
import Language.Core.Syntax

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Uniq)
DERIVE(Name)
DERIVE(NameSort)
DERIVE(Var)
DERIVE(Field)
DERIVE(Struct)
DERIVE(TyVar)
DERIVE(IVar)
DERIVE(W)
DERIVE(Const)
DERIVE(Exp)
DERIVE(BindVar)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(StructDef)
DERIVE(Type)
DERIVE(Omega)
DERIVE(Iota)
DERIVE(Stm)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Var)
    DERIVE(Field)
    DERIVE(Struct)
    DERIVE(TyVar)
    DERIVE(IVar)
    DERIVE(Exp)
    DERIVE(StructDef)
    DERIVE(Type)
    DERIVE(Omega)
    DERIVE(Iota)
    DERIVE(Stm)
