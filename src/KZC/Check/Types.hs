{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  KZC.Check.Types
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.Types (
    TyVar(..),
    IVar(..),
    IP(..),
    ipWidth,
    ipIsSigned,
    ipIsIntegral,
    FP(..),
    StructDef(..),
    Type(..),
    Kind(..),
    MetaTv(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader
import Control.Monad.Ref
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.IORef
import Data.Loc
import Data.List ((\\))
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
import KZC.Platform
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Uniq
import KZC.Vars

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Show)

newtype IVar = IVar Name
  deriving (Eq, Ord, Show)

data StructDef = StructDef Z.Struct [(Z.Field, Type)] !SrcLoc
  deriving (Eq, Ord, Show)

data Type -- Base Types
          = UnitT !SrcLoc
          | BoolT !SrcLoc
          | FixT IP !SrcLoc
          | FloatT FP !SrcLoc
          | StringT !SrcLoc
          | StructT Z.Struct !SrcLoc
          | ArrT Type Type !SrcLoc

          -- omega types
          | C Type !SrcLoc
          | T !SrcLoc

          -- mu types
          | ST [TyVar] Type Type Type Type !SrcLoc

          -- rho types
          | RefT Type !SrcLoc

          -- phi types
          | FunT [IVar] [Type] Type !SrcLoc

          -- iota types
          | ConstI Int !SrcLoc
          | VarI IVar !SrcLoc

          -- Type variables
          | TyVarT TyVar !SrcLoc
          | MetaT MetaTv !SrcLoc
  deriving (Eq, Ord, Show)

data Kind = TauK   -- ^ Base types, including arrays of base types
          | OmegaK -- ^ @C tau@ or @T@
          | MuK    -- ^ @ST omega tau tau@ types
          | RhoK   -- ^ Reference types
          | PhiK   -- ^ Function types
          | IotaK  -- ^ Array index types
  deriving (Eq, Ord, Show)

data MetaTv = MetaTv Uniq Kind TyRef
  deriving (Show)

instance Eq MetaTv where
    (MetaTv u1 _ _) == (MetaTv u2 _ _) = u1 == u2

instance Ord MetaTv where
    compare (MetaTv u1 _ _) (MetaTv u2 _ _) = compare u1 u2

type TyRef = IORef (Maybe Type)

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

instance IsString IVar where
    fromString s = IVar $ fromString s

instance IsString TyVar where
    fromString s = TyVar $ fromString s

instance Named TyVar where
    namedSymbol (TyVar n) = namedSymbol n

    mapName f (TyVar n) = TyVar (f n)

instance Named IVar where
    namedSymbol (IVar n) = namedSymbol n

    mapName f (IVar n) = IVar (f n)

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

appPrec :: Int
appPrec = 10

appPrec1 :: Int
appPrec1 = appPrec + 1

#if !defined(ONLY_TYPEDEFS)
arrowPrec :: Int
arrowPrec = 0

arrowPrec1 :: Int
arrowPrec1 = arrowPrec + 1

instance Pretty TyVar where
    ppr (TyVar n) = ppr n

instance Pretty IVar where
    ppr (IVar n) = ppr n

instance Pretty StructDef where
    ppr (StructDef s fields _) =
        text "struct" <+> ppr s <+> text "=" <+> pprStruct colon fields

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (FixT (U 1) _) =
        text "bit"

    pprPrec _ (FixT (I w) _)
      | w == dEFAULT_INT_WIDTH = text "int"
      | otherwise              = text "int" <> ppr w

    pprPrec _ (FixT (U w) _)
      | w == dEFAULT_INT_WIDTH = text "uint"
      | otherwise              = text "uint" <> ppr w

    pprPrec _ (FloatT FP32 _) =
        text "float"

    pprPrec _ (FloatT FP64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec _ (StringT _) =
        text "string"

    pprPrec _ (StructT s _) =
        ppr s

    pprPrec _ (ArrT ind tau _) =
        pprPrec appPrec1 tau <> brackets (ppr ind)

    pprPrec p (C tau _) =
        parensIf (p > appPrec) $
        text "C" <+> pprPrec appPrec1 tau

    pprPrec _ (T _) =
        text "T"

    pprPrec p (ST alphas omega tau1 tau2 tau3 _) | expertTypes =
        parensIf (p > appPrec) $
        pprForall alphas <+>
        text "ST" <+>
        align (sep [pprPrec appPrec1 omega
                   ,pprPrec appPrec1 tau1
                   ,pprPrec appPrec1 tau2
                   ,pprPrec appPrec1 tau3])
      where
        pprForall :: [TyVar] -> Doc
        pprForall []     = empty
        pprForall alphas = text "forall" <+> commasep (map ppr alphas) <+> dot

    pprPrec p (ST [_,_,_] (C tau _) _ _ _ _) =
        pprPrec p tau

    pprPrec p (ST _ omega _ tau2 tau3 _) =
        parensIf (p > appPrec) $
        text "ST" <+>
        align (sep [pprPrec appPrec1 omega
                   ,pprPrec appPrec1 tau2
                   ,pprPrec appPrec1 tau3])

    pprPrec p (RefT tau _) | expertTypes =
        parensIf (p > appPrec) $
        text "ref" <+> ppr tau

    pprPrec p (RefT tau _) =
        parensIf (p > appPrec) $
        text "var" <+> ppr tau

    pprPrec p (FunT iotas taus tau _) | expertTypes =
        parensIf (p > arrowPrec) $
        pprArgs iotas taus <+>
        text "->" <+>
        pprPrec arrowPrec1 tau
      where
        pprArgs :: [IVar] -> [Type] -> Doc
        pprArgs [] [tau1] =
            ppr tau1

        pprArgs [] taus =
            parens (commasep (map ppr taus))

        pprArgs iotas taus =
            parens (commasep (map ppr iotas) <> text ";" <+> commasep (map ppr taus))

    pprPrec p (FunT _ taus tau _) =
        parensIf (p > arrowPrec) $
        pprArgs taus <+>
        text "->" <+>
        pprPrec arrowPrec1 tau
      where
        pprArgs :: [Type] -> Doc
        pprArgs [tau1] =
            ppr tau1

        pprArgs taus =
            parens (commasep (map ppr taus))

    pprPrec _ (ConstI i _) =
        ppr i

    pprPrec _ (VarI v _) =
        ppr v

    pprPrec p (MetaT mtv _) =
        text (showsPrec p mtv "")

    pprPrec _ (TyVarT tv _) =
        ppr tv

instance Pretty Kind where
    ppr TauK   = text "tau"
    ppr OmegaK = text "omega"
    ppr MuK    = text "mu"
    ppr RhoK   = text "rho"
    ppr PhiK   = text "phi"
    ppr IotaK  = text "iota"

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Type TyVar where
    fvs UnitT{}                            = mempty
    fvs BoolT{}                            = mempty
    fvs FixT{}                             = mempty
    fvs FloatT{}                           = mempty
    fvs StringT{}                          = mempty
    fvs (StructT _ _)                      = mempty
    fvs (ArrT tau1 tau2 _)                 = fvs tau1 <> fvs tau2
    fvs (C tau _)                          = fvs tau
    fvs (T _)                              = mempty
    fvs (ST alphas omega tau1 tau2 tau3 _) = fvs omega <>
                                             (fvs tau1 <> fvs tau2 <> fvs tau3)
                                             <\\> fromList alphas
    fvs (RefT tau _)                       = fvs tau
    fvs (FunT _ taus tau _)                = fvs taus <> fvs tau
    fvs (ConstI _ _)                       = mempty
    fvs (VarI _ _)                         = mempty
    fvs (TyVarT tv _)                      = singleton tv
    fvs (MetaT _ _)                        = mempty

instance Fvs Type IVar where
    fvs UnitT{}                       = mempty
    fvs BoolT{}                       = mempty
    fvs FixT{}                        = mempty
    fvs FloatT{}                      = mempty
    fvs StringT{}                     = mempty
    fvs (StructT _ _)                 = mempty
    fvs (ArrT tau1 tau2 _)            = fvs tau1 <> fvs tau2
    fvs (C tau _)                     = fvs tau
    fvs (T _)                         = mempty
    fvs (ST _ omega tau1 tau2 tau3 _) = fvs omega <>
                                        fvs tau1 <> fvs tau2 <> fvs tau3
    fvs (RefT tau _)                  = fvs tau
    fvs (FunT iotas taus tau _)       = (fvs taus <> fvs tau) <\\>
                                        fromList iotas
    fvs (ConstI _ _)                  = mempty
    fvs (VarI iv _)                   = singleton iv
    fvs (TyVarT _ _)                  = mempty
    fvs (MetaT _ _)                   = mempty

instance Fvs Type MetaTv where
    fvs UnitT{}                       = mempty
    fvs BoolT{}                       = mempty
    fvs FixT{}                        = mempty
    fvs FloatT{}                      = mempty
    fvs StringT{}                     = mempty
    fvs (StructT _ _)                 = mempty
    fvs (ArrT tau1 tau2 _)            = fvs tau1 <> fvs tau2
    fvs (C tau _)                     = fvs tau
    fvs (T _)                         = mempty
    fvs (ST _ omega tau1 tau2 tau3 _) = fvs omega <>
                                        fvs tau1 <> fvs tau2 <> fvs tau3
    fvs (RefT tau _)                  = fvs tau
    fvs (FunT _ taus tau _)           = fvs taus <> fvs tau
    fvs (ConstI _ _)                  = mempty
    fvs (VarI _ _)                    = mempty
    fvs (TyVarT _ _)                  = mempty
    fvs (MetaT mtv _)                 = singleton mtv

instance Fvs Type n => Fvs [Type] n where
    fvs = foldMap fvs

instance HasVars Type TyVar where
    allVars UnitT{}                            = mempty
    allVars BoolT{}                            = mempty
    allVars FixT{}                             = mempty
    allVars FloatT{}                           = mempty
    allVars StringT{}                          = mempty
    allVars (StructT _ _)                      = mempty
    allVars (ArrT tau1 tau2 _)                 = allVars tau1 <> allVars tau2
    allVars (C tau _)                          = allVars tau
    allVars (T _)                              = mempty
    allVars (ST alphas omega tau1 tau2 tau3 _) = fromList alphas <>
                                                 allVars omega <>
                                                 allVars tau1 <>
                                                 allVars tau2 <>
                                                 allVars tau3
    allVars (RefT tau _)                       = allVars tau
    allVars (FunT _ taus tau _)                = allVars taus <> allVars tau
    allVars (ConstI _ _)                       = mempty
    allVars (VarI _ _)                         = mempty
    allVars (TyVarT tv _)                      = singleton tv
    allVars (MetaT _ _)                        = mempty

instance HasVars Type IVar where
    allVars UnitT{}                       = mempty
    allVars BoolT{}                       = mempty
    allVars FixT{}                        = mempty
    allVars FloatT{}                      = mempty
    allVars StringT{}                     = mempty
    allVars (StructT _ _)                 = mempty
    allVars (ArrT tau1 tau2 _)            = allVars tau1 <> allVars tau2
    allVars (C tau _)                     = allVars tau
    allVars (T _)                         = mempty
    allVars (ST _ omega tau1 tau2 tau3 _) = allVars omega <> allVars tau1 <>
                                            allVars tau2 <> allVars tau3
    allVars (RefT tau _)                  = allVars tau
    allVars (FunT iotas taus tau _)       = fromList iotas <>
                                            allVars taus <> allVars tau
    allVars (ConstI _ _)                  = mempty
    allVars (VarI iv _)                   = singleton iv
    allVars (TyVarT _ _)                  = mempty
    allVars (MetaT _ _)                   = mempty

instance HasVars Type MetaTv where
    allVars UnitT{}                       = mempty
    allVars BoolT{}                       = mempty
    allVars FixT{}                        = mempty
    allVars FloatT{}                      = mempty
    allVars StringT{}                     = mempty
    allVars (StructT _ _)                 = mempty
    allVars (ArrT tau1 tau2 _)            = allVars tau1 <> allVars tau2
    allVars (C tau _)                     = allVars tau
    allVars (T _)                         = mempty
    allVars (ST _ omega tau1 tau2 tau3 _) = allVars omega <>
                                            allVars tau1 <>
                                            allVars tau2 <> allVars tau3
    allVars (RefT tau _)                  = allVars tau
    allVars (FunT _ taus tau _)           = allVars taus <> allVars tau
    allVars (ConstI _ _)                  = mempty
    allVars (VarI _ _)                    = mempty
    allVars (TyVarT _ _)                  = mempty
    allVars (MetaT mtv _)                 = singleton mtv

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

    substM tau@StructT{} =
        pure tau

    substM (ArrT tau1 tau2 l) =
        ArrT <$> substM tau1 <*> substM tau2 <*> pure l

    substM (C tau l) =
        C <$> substM tau <*> pure l

    substM tau@T{} =
        pure tau

    substM (ST alphas omega tau1 tau2 tau3 l) =
        ST alphas <$> substM omega <*> substM tau1 <*> substM tau2 <*> substM tau3 <*> pure l

    substM (RefT tau l) =
        RefT <$> substM tau <*> pure l

    substM (FunT iotas taus tau l) =
        FunT iotas <$> substM taus <*> substM tau <*> pure l

    substM tau@ConstI{} =
        pure tau

    substM tau@VarI{} =
        pure tau

    substM tau@TyVarT{} =
        pure tau

    substM tau@(MetaT mtv _) = do
        (theta, _) <- ask
        return $ fromMaybe tau (Map.lookup mtv theta)

instance Subst Type IVar Type where
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

    substM tau@StructT{} =
        pure tau

    substM (ArrT tau1 tau2 l) =
        ArrT <$> substM tau1 <*> substM tau2 <*> pure l

    substM (C tau l) =
        C <$> substM tau <*> pure l

    substM tau@T{} =
        pure tau

    substM (ST alphas omega tau1 tau2 tau3 l) =
        ST alphas <$> substM omega <*> substM tau1 <*> substM tau2 <*> substM tau3 <*> pure l

    substM (RefT tau l) =
        RefT <$> substM tau <*> pure l

    substM (FunT iotas taus tau l) =
        freshen iotas $ \iotas' ->
        FunT iotas' <$> substM taus <*> substM tau <*> pure l

    substM tau@ConstI{} =
        pure tau

    substM tau@(VarI v _) = do
        (theta, _) <- ask
        return $ fromMaybe tau (Map.lookup v theta)

    substM tau@TyVarT{} =
        pure tau

    substM tau@MetaT{} =
        pure tau

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

    substM tau@StructT{} =
        pure tau

    substM (ArrT tau1 tau2 l) =
        ArrT <$> substM  tau1 <*> substM tau2 <*> pure l

    substM (C tau l) =
        C <$> substM tau <*> pure l

    substM tau@T{} =
        pure tau

    substM (ST alphas omega tau1 tau2 tau3 l) =
        freshen alphas $ \alphas' ->
        ST alphas' <$> substM omega <*> substM tau1 <*> substM tau2 <*> substM tau3 <*> pure l

    substM (RefT tau l) =
        RefT <$> substM tau <*> pure l

    substM (FunT iotas taus tau l) =
        FunT iotas <$> substM taus <*> substM tau <*> pure l

    substM tau@ConstI{} =
        pure tau

    substM tau@VarI{} =
        pure tau

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

instance FreshVars IVar where
    freshVars n used =
        return $ map (\a -> IVar (mkName a noLoc)) freshTvs
      where
        freshTvs :: [String]
        freshTvs = take n (allTvs \\ map namedString used)

        allTvs :: [String]
        allTvs =  [[x] | x <- simpleTvs] ++
                  [x : show i |  i <- [1 :: Integer ..],
                                 x <- simpleTvs]

        simpleTvs :: [Char]
        simpleTvs = reverse ['l'..'n']

instance Freshen TyVar Type TyVar where
    freshen alpha@(TyVar n) =
        freshenV (namedString n) mkV mkE alpha
      where
        mkV :: String -> TyVar
        mkV s = TyVar n { nameSym = intern s }

        mkE :: TyVar -> Type
        mkE alpha = TyVarT alpha (srclocOf alpha)

instance Freshen IVar Type IVar where
    freshen alpha@(IVar n) =
        freshenV (namedString n) mkV mkE alpha
      where
        mkV :: String -> IVar
        mkV s = IVar n { nameSym = intern s }

        mkE :: IVar -> Type
        mkE alpha = VarI alpha (srclocOf alpha)

#include "KZC/Check/Types-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
