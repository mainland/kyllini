{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics (Data, Typeable)

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
DERIVE(QP)
DERIVE(FP)
DERIVE(Decl)
DERIVE(StructDef)
DERIVE(Const)
DERIVE(Exp)
DERIVE1(GenInterval)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE1(VectAnn)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(Type)
DERIVE(Omega)
DERIVE(Trait)
DERIVE(Kind)

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
