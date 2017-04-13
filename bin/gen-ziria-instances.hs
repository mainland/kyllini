{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Name
import KZC.Traits
import KZC.Util.Derive
import KZC.Util.Uniq
import Language.Ziria.Syntax

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Uniq)
DERIVE(Name)
DERIVE(NameSort)
DERIVE(TyVar)
DERIVE(Var)
DERIVE(Struct)
DERIVE(Field)
DERIVE(IP)
DERIVE(QP)
DERIVE(FP)
DERIVE(Decl)
DERIVE(Const)
DERIVE(Exp)
DERIVE(GenInterval)
DERIVE(VarBind)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE(VectAnn)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(Stm)
DERIVE(Type)
DERIVE(Trait)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(TyVar)
    DERIVE(Var)
    DERIVE(Struct)
    DERIVE(Field)
    DERIVE(Decl)
    DERIVE(Exp)
    DERIVE(GenInterval)
    DERIVE(VarBind)
    DERIVE(Stm)
    DERIVE(Type)
