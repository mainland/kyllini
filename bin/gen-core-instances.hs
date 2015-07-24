{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Derive
import KZC.Name
import Language.Core.Syntax

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Name)
DERIVE(Var)
DERIVE(Field)
DERIVE(Struct)
DERIVE(IVar)
DERIVE(W)
DERIVE(Const)
DERIVE(Exp)
DERIVE(IVarBind)
DERIVE(VarBind)
DERIVE(BindVar)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(Type)
DERIVE(Omega)
DERIVE(Iota)
DERIVE(Ind)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Exp)
    DERIVE(Type)
