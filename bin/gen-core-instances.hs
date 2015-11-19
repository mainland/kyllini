{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Core.Syntax
import KZC.Derive
import KZC.Name
import KZC.Uniq

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
DERIVE(Scale)
DERIVE(Signedness)
DERIVE(W)
DERIVE(BP)
DERIVE(FP)
DERIVE(Const)
DERIVE(Decl)
DERIVE(Exp)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE(VectAnn)
DERIVE(BindVar)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(StructDef)
DERIVE(Type)
DERIVE(Omega)
DERIVE(Iota)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Var)
    DERIVE(Field)
    DERIVE(Struct)
    DERIVE(TyVar)
    DERIVE(IVar)
    DERIVE(Decl)
    DERIVE(Exp)
    DERIVE(StructDef)
    DERIVE(Type)
    DERIVE(Omega)
    DERIVE(Iota)
