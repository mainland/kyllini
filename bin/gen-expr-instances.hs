{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Expr.Syntax
import KZC.Name
import KZC.Util.Derive
import KZC.Util.Uniq

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

#define DERIVE1(f) \
deriving instance Typeable f; \
deriving instance Data a => Data (f a)

DERIVE(Uniq)
DERIVE(Name)
DERIVE(NameSort)
DERIVE(Var)
DERIVE(WildVar)
DERIVE(Field)
DERIVE(Struct)
DERIVE(TyVar)
DERIVE(IP)
DERIVE(FP)
DERIVE(Const)
DERIVE(Decl)
DERIVE(Exp)
DERIVE1(GenInterval)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE(VectAnn)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(StructDef)
DERIVE(Type)
DERIVE(Trait)
DERIVE(Kind)
DERIVE(Omega)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Var)
    DERIVE(Field)
    DERIVE(Struct)
    DERIVE(TyVar)
    DERIVE(Decl)
    DERIVE(Exp)
    DERIVE(GenInterval ())
    DERIVE(StructDef)
    DERIVE(Type)
    DERIVE(Omega)
