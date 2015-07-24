{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  KZC.Check.Types
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.Types where

import Control.Monad.Ref
import Data.IORef
import Data.Loc
import Data.List ((\\))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

newtype Struct = Struct Name
  deriving (Eq, Ord, Show)

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Show)

data W = W8
       | W16
       | W32
       | W64
  deriving (Eq, Ord, Read, Show)

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | BitT !SrcLoc
          | IntT W !SrcLoc
          | FloatT W !SrcLoc
          | ComplexT W !SrcLoc
          | StringT !SrcLoc
          | RefT Type !SrcLoc
          | ArrT Type Type !SrcLoc
          | StructT Struct !SrcLoc
          | ST Type Type Type !SrcLoc
          | FunT [Type] Type !SrcLoc
          -- nat kind
          | NatI !SrcLoc
          -- omega
          | C Type !SrcLoc
          | T !SrcLoc
          -- array type indices
          | ConstI Integer !SrcLoc

          | TyVarT TyVar !SrcLoc
          | MetaT MetaTv !SrcLoc
  deriving (Eq, Ord, Show)

data Kind = BaseK
  deriving (Eq, Ord, Show)

data MetaTv = MetaTv Uniq TyRef
  deriving (Show)

instance Eq MetaTv where
    (MetaTv u1 _) == (MetaTv u2 _) = u1 == u2

instance Ord MetaTv where
    compare (MetaTv u1 _) (MetaTv u2 _) = compare u1 u2

type TyRef = IORef (Maybe Type)

instance Named TyVar where
    namedString (TyVar n) = namedString n

{------------------------------------------------------------------------------
 -
 - Smart constructors
 -
 ------------------------------------------------------------------------------}

tyVarT :: TyVar -> Type
tyVarT tv@(TyVar n) = TyVarT tv (srclocOf n)

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Type TyVar where
    fvs (UnitT {})             = mempty
    fvs (BoolT {})             = mempty
    fvs (BitT {})              = mempty
    fvs (IntT {})              = mempty
    fvs (FloatT {})            = mempty
    fvs (ComplexT {})          = mempty
    fvs (StringT {})           = mempty
    fvs (RefT tau _)           = fvs tau
    fvs (ArrT tau1 tau2 _)     = fvs tau1 <> fvs tau2
    fvs (StructT _ _)          = mempty
    fvs (ST omega tau1 tau2 _) = fvs omega <> fvs tau1 <> fvs tau2
    fvs (FunT taus tau _)      = fvs taus <> fvs tau
    fvs (NatI _)               = mempty
    fvs (C tau _)              = fvs tau
    fvs (T _)                  = mempty
    fvs (ConstI _ _)           = mempty
    fvs (TyVarT tv _)          = singleton tv
    fvs (MetaT _ _)            = mempty

instance Fvs Type MetaTv where
    fvs (UnitT {})             = mempty
    fvs (BoolT {})             = mempty
    fvs (BitT {})              = mempty
    fvs (IntT {})              = mempty
    fvs (FloatT {})            = mempty
    fvs (ComplexT {})          = mempty
    fvs (StringT {})           = mempty
    fvs (RefT tau _)           = fvs tau
    fvs (ArrT tau1 tau2 _)     = fvs tau1 <> fvs tau2
    fvs (StructT _ _)          = mempty
    fvs (ST omega tau1 tau2 _) = fvs omega <> fvs tau1 <> fvs tau2
    fvs (FunT taus tau _)      = fvs taus <> fvs tau
    fvs (NatI _)               = mempty
    fvs (C tau _)              = fvs tau
    fvs (T _)                  = mempty
    fvs (ConstI _ _)           = mempty
    fvs (TyVarT _ _)           = mempty
    fvs (MetaT mtv _)          = singleton mtv

instance HasVars Type TyVar where
    allVars (UnitT {})             = mempty
    allVars (BoolT {})             = mempty
    allVars (BitT {})              = mempty
    allVars (IntT {})              = mempty
    allVars (FloatT {})            = mempty
    allVars (ComplexT {})          = mempty
    allVars (StringT {})           = mempty
    allVars (RefT tau _)           = allVars tau
    allVars (ArrT tau1 tau2 _)     = allVars tau1 <> allVars tau2
    allVars (StructT _ _)          = mempty
    allVars (ST omega tau1 tau2 _) = allVars omega <> allVars tau1 <> allVars tau2
    allVars (FunT taus tau _)      = allVars taus <> allVars tau
    allVars (NatI _)               = mempty
    allVars (C tau _)              = allVars tau
    allVars (T _)                  = mempty
    allVars (ConstI _ _)           = mempty
    allVars (TyVarT tv _)          = singleton tv
    allVars (MetaT _ _)            = mempty

instance HasVars Type MetaTv where
    allVars (UnitT {})             = mempty
    allVars (BoolT {})             = mempty
    allVars (BitT {})              = mempty
    allVars (IntT {})              = mempty
    allVars (FloatT {})            = mempty
    allVars (ComplexT {})          = mempty
    allVars (StringT {})           = mempty
    allVars (RefT tau _)           = allVars tau
    allVars (ArrT tau1 tau2 _)     = allVars tau1 <> allVars tau2
    allVars (StructT _ _)          = mempty
    allVars (ST omega tau1 tau2 _) = allVars omega <> allVars tau1 <> allVars tau2
    allVars (FunT taus tau _)      = allVars taus <> allVars tau
    allVars (NatI _)               = mempty
    allVars (C tau _)              = allVars tau
    allVars (T _)                  = mempty
    allVars (ConstI _ _)           = mempty
    allVars (TyVarT _ _)           = mempty
    allVars (MetaT mtv _)          = singleton mtv

instance Subst Type MetaTv Type where
    subst _ _ tau@(UnitT {}) =
        tau

    subst _ _ tau@(BoolT {}) =
        tau

    subst _ _ tau@(BitT {}) =
        tau

    subst _ _ tau@(IntT {}) =
        tau

    subst _ _ tau@(FloatT {}) =
        tau

    subst _ _ tau@(ComplexT {}) =
        tau

    subst _ _ tau@(StringT {}) =
        tau

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (ArrT tau1 tau2 l) =
        ArrT (subst theta phi tau1) (subst theta phi tau2) l

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ST tau1 tau2 tau3 l) =
        ST (subst theta phi tau1) (subst theta phi tau2) (subst theta phi tau3) l

    subst theta phi (FunT taus tau l) =
        FunT (subst theta phi taus) (subst theta phi tau) l

    subst _ _ tau@(NatI {}) =
        tau

    subst theta phi (C tau l) =
        C (subst theta phi tau) l

    subst _ _ tau@(T {}) =
        tau

    subst _ _ tau@(ConstI {}) =
        tau

    subst _ _ tau@(TyVarT {}) =
        tau

    subst theta _ tau@(MetaT mtv _) =
        fromMaybe tau (Map.lookup mtv theta)

instance FreshVars TyVar where
    freshVars n used =
        return $ map (\a -> TyVar (mkName a noLoc)) freshTvs
      where
        freshTvs :: [String]
        freshTvs = take n (allTvs \\ map namedString used)

        allTvs :: [String]
        allTvs =  [[x] | x <- ['a'..'z']] ++
                  [x : show i |  i <- [1 :: Integer ..],
                                 x <- ['a'..'z']]

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Show a => Show (IORef a) where
    showsPrec d ref =
        showParen (d > appPrec) $
        showString "(unsafePerformIO . newRef)" .
        showsPrec (appPrec+1) ((unsafePerformIO . readRef) ref)

appPrec :: Int
appPrec = 10

appPrec1 :: Int
appPrec1 = appPrec + 1

arrowPrec :: Int
arrowPrec = 0

arrowPrec1 :: Int
arrowPrec1 = arrowPrec + 1

tyappPrec :: Int
tyappPrec = 1

tyappPrec1 :: Int
tyappPrec1 = tyappPrec + 1

instance Pretty Struct where
    ppr (Struct n) = ppr n

instance Pretty TyVar where
    ppr (TyVar n) = ppr n

instance Pretty W where
    ppr W8  = text "8"
    ppr W16 = text "16"
    ppr W32 = text "32"
    ppr W64 = text "64"

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (BitT _) =
        text "bit"

    pprPrec _ (IntT w _) =
        text "int" <> ppr w

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec _ (ComplexT w _) =
        text "complex" <> ppr w

    pprPrec _ (StringT _) =
        text "string"

    pprPrec p (RefT tau _) =
        parensIf (p > tyappPrec) $
        text "ref" <+> ppr tau

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)

    pprPrec _ (StructT s _) =
        text "struct" <+> ppr s

    pprPrec p (ST w tau1 tau2 _) =
        parensIf (p > tyappPrec) $
        text "ST" <+> ppr w <+> pprPrec tyappPrec1 tau1 <+> pprPrec tyappPrec1 tau2

    pprPrec p (FunT taus tau _) =
        parensIf (p > arrowPrec) $
        parens (commasep (map ppr taus)) <+>
        text "->" <+>
        pprPrec arrowPrec1 tau

    pprPrec _ (NatI _) =
        text "nat"

    pprPrec p (C tau _) =
        parensIf (p > tyappPrec) $
        text "C" <+> ppr tau

    pprPrec _ (T _) =
        text "T"

    pprPrec _ (ConstI i _) =
        ppr i

    pprPrec _ (MetaT mtv _) =
        (text . show) mtv

    pprPrec _ (TyVarT tv _) =
        ppr tv

#include "KZC/Check/Types-instances.hs"
