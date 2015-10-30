{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Control.Monad.Free
import Data.Generics

import KZC.Auto.Syntax
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
DERIVE(W)
DERIVE(Signedness)
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

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(LocalDecl)
    DERIVE(Exp)
