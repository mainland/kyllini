{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Core.Syntax
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
DERIVE(Const)
DERIVE(View)
DERIVE(LocalDecl)
DERIVE(BoundVar)
DERIVE(OccInfo)
DERIVE(Exp)
DERIVE1(GenInterval)
DERIVE(Gen)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE1(VectAnn)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(StructDef)
DERIVE(Type)
DERIVE(Omega)
DERIVE(Trait)
DERIVE(Kind)

DERIVE1(Decl)
DERIVE1(Arg)
DERIVE1(Step)
DERIVE(Tag)
DERIVE1(Comp)
DERIVE1(Rate)
DERIVE(M)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Decl ())
    DERIVE(Step ())
    DERIVE(View)
    DERIVE(LocalDecl)
    DERIVE(Exp)
    DERIVE(Gen)
