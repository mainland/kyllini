{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  KZC.Check.Types
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check.Types (
    module KZC.Traits,

    TyVar(..),
    IP(..),
    ipWidth,
    ipIsSigned,
    ipIsIntegral,
    FP(..),
    StructDef(..),
    structDefTvks,
    Type(..),
    Kind(..),
    Tvk,
    MetaTv(..),
    MetaKv(..),
    R(..),
    MetaRv(..)
  ) where

import Control.Monad.Reader
import Control.Monad.Ref
import Data.IORef
import Data.Loc
import Data.List ((\\), sort)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.String
import Data.Symbol
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland

import qualified Language.Ziria.Syntax as Z

import KZC.Expr.Syntax (IP(..),
                        ipWidth,
                        ipIsSigned,
                        ipIsIntegral,
                        FP(..))
import KZC.Globals
import KZC.Name
import KZC.Traits
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Uniq
import KZC.Vars

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Show)

data StructDef = StructDef Z.Struct [Tvk] [(Z.Field, Type)] !SrcLoc
               | TypeDef Z.Struct [Tvk] Type !SrcLoc
  deriving (Eq, Ord, Show)

structDefTvks :: StructDef -> [Tvk]
structDefTvks (StructDef _ tvks _ _) = tvks
structDefTvks (TypeDef _ tvks _ _)   = tvks

data Type -- Base Types
          = UnitT !SrcLoc
          | BoolT !SrcLoc
          | FixT IP !SrcLoc
          | FloatT FP !SrcLoc
          | StringT !SrcLoc
          | StructT Z.Struct [Type] !SrcLoc
          | SynT Type Type !SrcLoc
          | ArrT Type Type !SrcLoc

          -- omega types
          | C Type !SrcLoc
          | T !SrcLoc

          -- mu types
          | ST Type Type Type Type !SrcLoc

          -- rho types
          | RefT Type !SrcLoc

          -- phi types
          | FunT [Type] Type !SrcLoc

          -- Natural number types
          | NatT Int !SrcLoc

          -- forall type
          | ForallT [Tvk] Type !SrcLoc

          -- Type variables
          | TyVarT TyVar !SrcLoc
          | MetaT MetaTv !SrcLoc
  deriving (Eq, Ord, Show)

-- | Type meta-variable
data MetaTv = MetaTv Uniq Kind TyRef
  deriving (Show)

instance Eq MetaTv where
    (MetaTv u1 _ _) == (MetaTv u2 _ _) = u1 == u2

instance Ord MetaTv where
    compare (MetaTv u1 _ _) (MetaTv u2 _ _) = compare u1 u2

type TyRef = IORef (Maybe Type)

-- | Kinds
data Kind = TauK R -- ^ Base types, including arrays of base types
          | OmegaK -- ^ @C tau@ or @T@
          | MuK    -- ^ @ST omega tau tau@ types
          | RhoK   -- ^ Reference types
          | PhiK   -- ^ Function types
          | NatK   -- ^ Type-level natural number
          | MetaK MetaKv
  deriving (Eq, Ord, Show)

data R = R Traits
       | MetaR MetaRv
  deriving (Eq, Ord, Show)

type Tvk = (TyVar, Kind)

-- | Traits meta-variable
data MetaRv = MetaRv Uniq Traits TraitsRef
  deriving (Show)

instance Eq MetaRv where
    (MetaRv u1 _ _) == (MetaRv u2 _ _) = u1 == u2

instance Ord MetaRv where
    compare (MetaRv u1 _ _) (MetaRv u2 _ _) = compare u1 u2

type TraitsRef = IORef (Maybe R)

data MetaKv = MetaKv Uniq KindRef
  deriving (Show)

instance Eq MetaKv where
    (MetaKv u1 _) == (MetaKv u2 _) = u1 == u2

instance Ord MetaKv where
    compare (MetaKv u1 _) (MetaKv u2 _) = compare u1 u2

type KindRef = IORef (Maybe Kind)

instance Show a => Show (IORef a) where
    showsPrec d ref =
        showParen (d > appPrec) $
        showString "(unsafePerformIO . newRef) " .
        showsPrec appPrec1 ((unsafePerformIO . readRef) ref)

{------------------------------------------------------------------------------
 -
 - IsString and Named instances
 -
 ------------------------------------------------------------------------------}

instance IsString TyVar where
    fromString s = TyVar $ fromString s

instance Named TyVar where
    namedSymbol (TyVar n) = namedSymbol n

    mapName f (TyVar n) = TyVar (f n)

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

#if !defined(ONLY_TYPEDEFS)
instance Pretty TyVar where
    ppr (TyVar n) = ppr n

instance Pretty StructDef where
    ppr (StructDef s [] fields _) | classicDialect =
        text "struct" <+> ppr s <+> text "=" <+> pprStruct semi colon fields

    ppr (StructDef s tvks fields _) =
        text "struct" <+> ppr s <> pprForall tvks <+> pprStruct semi colon fields

    ppr (TypeDef s tvks tau _) =
        text "type" <+> ppr s <> pprForall tvks <+> text "=" <+> ppr tau

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (FixT (U 1) _) =
        text "bit"

    pprPrec _ (FixT IDefault _) =
        text "int"

    pprPrec _ (FixT (I w) _) =
        text "int" <> ppr w

    pprPrec _ (FixT UDefault _) =
        text "uint"

    pprPrec _ (FixT (U w) _) =
        text "uint" <> ppr w

    pprPrec _ (FloatT FP32 _) =
        text "float"

    pprPrec _ (FloatT FP64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec _ (StringT _) =
        text "string"

    pprPrec p (StructT s taus _) =
        parensIf (p > tyappPrec) $
        text "struct" <+> ppr s <> pprTyApp taus

    pprPrec p (SynT _ tau' _) =
        pprPrec p tau'

    pprPrec p (ArrT ind tau@StructT{} _) =
        parensIf (p > tyappPrec) $
        ppr tau <> brackets (ppr ind)

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)

    pprPrec p (C tau _) =
        parensIf (p > tyappPrec) $
        text "C" <+> pprPrec tyappPrec1 tau

    pprPrec _ (T _) =
        text "T"

    pprPrec p (ST omega tau1 tau2 tau3 _) | expertTypes =
        parensIf (p > tyappPrec) $
        text "ST" <+> pprPrec tyappPrec1 omega
                  <+> pprPrec tyappPrec1 tau1
                  <+> pprPrec tyappPrec1 tau2
                  <+> pprPrec tyappPrec1 tau3

    pprPrec p (ST omega _ tau2 tau3 _) =
        parensIf (p > tyappPrec) $
        text "ST" <+> pprPrec tyappPrec1 omega
                  <+> pprPrec tyappPrec1 tau2
                  <+> pprPrec tyappPrec1 tau3

    pprPrec p (RefT tau _) | expertTypes =
        parensIf (p > tyappPrec) $
        text "ref" <+> pprPrec tyappPrec1 tau

    pprPrec p (RefT tau _) =
        parensIf (p > tyappPrec) $
        text "var" <+> pprPrec tyappPrec1 tau

    pprPrec p (FunT taus tau _) =
        parensIf (p > tyappPrec) $
        group $
        parens (commasep (map ppr taus)) <+>
        text "->" </>
        pprPrec arrowPrec1 tau

    pprPrec _ (NatT i _) =
        ppr i

    pprPrec p (ForallT tvks (ST (C tau _) (TyVarT s _) (TyVarT a _) (TyVarT b _) _) _) | not expertTypes && alphas' == alphas =
        pprPrec p tau
      where
        alphas, alphas' :: [TyVar]
        alphas  = sort $ map fst tvks
        alphas' = sort [s, a, b]

    pprPrec p (ForallT tvks (ST omega tau1 tau2 tau3 _) _) =
        parensIf (p > tyappPrec) $
        text "ST" <> pprForall tvks
                  <+> pprPrec tyappPrec1 omega
                  <+> pprPrec tyappPrec1 tau1
                  <+> pprPrec tyappPrec1 tau2
                  <+> pprPrec tyappPrec1 tau3

    pprPrec _ (ForallT tvks tau _) =
        pprForall tvks <> ppr tau

    pprPrec p (MetaT mtv _) =
        text (showsPrec p mtv "")

    pprPrec _ (TyVarT tv _) =
        ppr tv

instance Pretty Kind where
    pprPrec p (TauK ts)   = pprPrec p ts
    pprPrec _ OmegaK      = text "omega"
    pprPrec _ MuK         = text "mu"
    pprPrec _ RhoK        = text "rho"
    pprPrec _ PhiK        = text "phi"
    pprPrec _ NatK        = text "N"
    pprPrec p (MetaK mkv) = text (showsPrec p mkv "")

instance Pretty R where
    pprPrec p (R ts)      = pprPrec p ts
    pprPrec p (MetaR mrv) = text (showsPrec p mrv "")

-- | Pretty-print a forall quantifier
pprForall :: [Tvk] -> Doc
pprForall []   = empty
pprForall tvks = angles $ commasep (map pprKindSig tvks)

-- | Pretty-print a type application. This is used for struct instantiation.
pprTyApp :: [Type] -> Doc
pprTyApp []   = empty
pprTyApp taus = angles $ commasep (map ppr taus)

-- | Pretty-print a thing with a kind signature
pprKindSig :: Pretty a => (a, Kind) -> Doc
pprKindSig (tau, TauK (R ts)) | nullTraits ts =
    ppr tau

pprKindSig (tau, TauK traits) =
    ppr tau <+> colon <+> ppr traits

pprKindSig (tau, kappa) =
    ppr tau <+> colon <+> ppr kappa

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Type TyVar where
    fvs UnitT{}                     = mempty
    fvs BoolT{}                     = mempty
    fvs FixT{}                      = mempty
    fvs FloatT{}                    = mempty
    fvs StringT{}                   = mempty
    fvs (StructT _ taus _)          = fvs taus
    fvs (SynT _ tau' _)             = fvs tau'
    fvs (ArrT tau1 tau2 _)          = fvs tau1 <> fvs tau2
    fvs (C tau _)                   = fvs tau
    fvs (T _)                       = mempty
    fvs (ST omega tau1 tau2 tau3 _) = fvs omega <>
                                      (fvs tau1 <> fvs tau2 <> fvs tau3)
    fvs (RefT tau _)                = fvs tau
    fvs (FunT taus tau _)           = fvs taus <> fvs tau
    fvs (NatT _ _)                  = mempty
    fvs (ForallT tvks tau _)        = fvs tau <\\> fromList (map fst tvks)
    fvs (TyVarT tv _)               = singleton tv
    fvs (MetaT _ _)                 = mempty

instance Fvs Type MetaTv where
    fvs UnitT{}                     = mempty
    fvs BoolT{}                     = mempty
    fvs FixT{}                      = mempty
    fvs FloatT{}                    = mempty
    fvs StringT{}                   = mempty
    fvs (StructT _ taus _)          = fvs taus
    fvs (SynT _ tau' _)             = fvs tau'
    fvs (ArrT tau1 tau2 _)          = fvs tau1 <> fvs tau2
    fvs (C tau _)                   = fvs tau
    fvs (T _)                       = mempty
    fvs (ST omega tau1 tau2 tau3 _) = fvs omega <>
                                      fvs tau1 <> fvs tau2 <> fvs tau3
    fvs (RefT tau _)                = fvs tau
    fvs (FunT taus tau _)           = fvs taus <> fvs tau
    fvs (NatT _ _)                  = mempty
    fvs (ForallT _ tau _)           = fvs tau
    fvs (TyVarT _ _)                = mempty
    fvs (MetaT mtv _)               = singleton mtv

instance Fvs Type n => Fvs [Type] n where
    fvs = foldMap fvs

instance Fvs Kind MetaRv where
    fvs (TauK (MetaR mrv)) = singleton mrv
    fvs _                  = mempty

instance Fvs Kind n => Fvs [Kind] n where
    fvs = foldMap fvs

instance HasVars Type TyVar where
    allVars UnitT{}                     = mempty
    allVars BoolT{}                     = mempty
    allVars FixT{}                      = mempty
    allVars FloatT{}                    = mempty
    allVars StringT{}                   = mempty
    allVars (StructT _ taus _)          = allVars taus
    allVars (SynT _ tau' _)             = allVars tau'
    allVars (ArrT tau1 tau2 _)          = allVars tau1 <> allVars tau2
    allVars (C tau _)                   = allVars tau
    allVars (T _)                       = mempty
    allVars (ST omega tau1 tau2 tau3 _) = allVars omega <>
                                          allVars tau1 <>
                                          allVars tau2 <>
                                          allVars tau3
    allVars (RefT tau _)                = allVars tau
    allVars (FunT taus tau _)           = allVars taus <> allVars tau
    allVars (NatT _ _)                  = mempty
    allVars (ForallT tvks tau _)        = fvs tau <> fromList (map fst tvks)
    allVars (TyVarT tv _)               = singleton tv
    allVars (MetaT _ _)                 = mempty

instance HasVars Type MetaTv where
    allVars UnitT{}                     = mempty
    allVars BoolT{}                     = mempty
    allVars FixT{}                      = mempty
    allVars FloatT{}                    = mempty
    allVars StringT{}                   = mempty
    allVars (StructT _ taus _)          = allVars taus
    allVars (SynT _ tau' _)             = allVars tau'
    allVars (ArrT tau1 tau2 _)          = allVars tau1 <> allVars tau2
    allVars (C tau _)                   = allVars tau
    allVars (T _)                       = mempty
    allVars (ST omega tau1 tau2 tau3 _) = allVars omega <>
                                          allVars tau1 <>
                                          allVars tau2 <> allVars tau3
    allVars (RefT tau _)                = allVars tau
    allVars (FunT taus tau _)           = allVars taus <> allVars tau
    allVars (NatT _ _)                  = mempty
    allVars (ForallT _ tau _)           = allVars tau
    allVars (TyVarT _ _)                = mempty
    allVars (MetaT mtv _)               = singleton mtv

instance Subst Type MetaTv Type where
    substM tau@UnitT{} =
        pure tau

    substM tau@BoolT{} =
        pure tau

    substM tau@FixT{} =
        pure tau

    substM tau@FloatT{} =
        pure tau

    substM tau@StringT{} =
        pure tau

    substM (StructT s taus l) =
        StructT s <$> substM taus <*> pure l

    substM (SynT tau tau' l) =
        SynT <$> substM tau <*> substM tau' <*> pure l

    substM (ArrT tau1 tau2 l) =
        ArrT <$> substM tau1 <*> substM tau2 <*> pure l

    substM (C tau l) =
        C <$> substM tau <*> pure l

    substM tau@T{} =
        pure tau

    substM (ST omega tau1 tau2 tau3 l) =
        ST <$> substM omega <*> substM tau1 <*> substM tau2 <*> substM tau3 <*> pure l

    substM (RefT tau l) =
        RefT <$> substM tau <*> pure l

    substM (FunT taus tau l) =
        FunT <$> substM taus <*> substM tau <*> pure l

    substM tau@NatT{} =
        pure tau

    substM tau@TyVarT{} =
        pure tau

    substM (ForallT tvks tau l) =
        ForallT tvks <$> substM tau <*> pure l

    substM tau@(MetaT mtv _) = do
        (theta, _) <- ask
        return $ fromMaybe tau (Map.lookup mtv theta)

instance Subst Type TyVar Type where
    substM tau@UnitT{} =
        pure tau

    substM tau@BoolT{} =
        pure tau

    substM tau@FixT{} =
        pure tau

    substM tau@FloatT{} =
        pure tau

    substM tau@StringT{} =
        pure tau

    substM (StructT s taus l) =
        StructT s <$> substM taus <*> pure l

    substM (SynT tau tau' l) =
        SynT <$> substM tau <*> substM tau' <*> pure l

    substM (ArrT tau1 tau2 l) =
        ArrT <$> substM  tau1 <*> substM tau2 <*> pure l

    substM (C tau l) =
        C <$> substM tau <*> pure l

    substM tau@T{} =
        pure tau

    substM (ST omega tau1 tau2 tau3 l) =
        ST <$> substM omega <*> substM tau1 <*> substM tau2 <*> substM tau3 <*> pure l

    substM (RefT tau l) =
        RefT <$> substM tau <*> pure l

    substM (FunT taus tau l) =
        FunT <$> substM taus <*> substM tau <*> pure l

    substM tau@NatT{} =
        pure tau

    substM (ForallT tvks tau l) =
        freshen tvks $ \tvks' ->
        ForallT tvks' <$> substM tau <*> pure l

    substM tau@(TyVarT alpha _) = do
        (theta, _) <- ask
        return $ fromMaybe tau (Map.lookup alpha theta)

    substM tau@MetaT{} =
        pure tau

instance FreshVars TyVar where
    freshVars n used =
        return $ map (\a -> TyVar (mkName a noLoc)) freshTvs
      where
        freshTvs :: [String]
        freshTvs = take n (allTvs \\ map namedString used)

        allTvs :: [String]
        allTvs =  [[x] | x <- simpleTvs] ++
                  [x : show i |  i <- [1 :: Integer ..],
                                 x <- simpleTvs]

        simpleTvs :: [Char]
        simpleTvs = ['a'..'z']

instance Freshen TyVar Type TyVar where
    freshen alpha@(TyVar n) =
        freshenV (namedString n) mkV mkE alpha
      where
        mkV :: String -> TyVar
        mkV s = TyVar n { nameSym = intern s }

        mkE :: TyVar -> Type
        mkE alpha = TyVarT alpha (srclocOf alpha)

instance Freshen (TyVar, Kind) Type TyVar where
    freshen (alpha, kappa) k =
        freshen alpha $ \alpha' -> k (alpha', kappa)

#include "KZC/Check/Types-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
