{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Generics

import KZC.Derive
import KZC.Name
import Language.Ziria.Syntax

#define DERIVE(a) \
deriving instance Typeable a; \
deriving instance Data a

DERIVE(Name)
DERIVE(W)
DERIVE(Const)
DERIVE(Exp)
DERIVE(UnrollAnn)
DERIVE(InlineAnn)
DERIVE(PipelineAnn)
DERIVE(VectAnn)
DERIVE(Unop)
DERIVE(Binop)
DERIVE(CompLet)
DERIVE(Stm)
DERIVE(Cmd)
DERIVE(StructDef)
DERIVE(Type)
DERIVE(Ind)

main :: IO ()
main = do
#undef DERIVE
#define DERIVE(a) deriveM deriveLocated (undefined::a)
    DERIVE(Exp)
    DERIVE(CompLet)
    DERIVE(Stm)
    DERIVE(Cmd)
    DERIVE(StructDef)
    DERIVE(Type)
