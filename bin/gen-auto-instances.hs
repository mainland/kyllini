{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Auto.Syntax
import KZC.Derive
import KZC.Name
import KZC.Uniq

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
DERIVE(LocalDecl)
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

DERIVE1(Decl)
DERIVE1(Step)
DERIVE1(Comp)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Decl ())
    DERIVE(Step ())
    DERIVE(LocalDecl)
    DERIVE(Exp)
