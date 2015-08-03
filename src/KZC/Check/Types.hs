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
import qualified Data.Set as Set
import Data.Symbol
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

newtype IVar = IVar Name
  deriving (Eq, Ord, Show)

data W = W8
       | W16
       | W32
       | W64
  deriving (Eq, Ord, Read, Show)

dEFAULT_INT_WIDTH :: W
dEFAULT_INT_WIDTH = W32

data Type -- Base Types
          = UnitT !SrcLoc
          | BoolT !SrcLoc
          | BitT !SrcLoc
          | IntT W !SrcLoc
          | FloatT W !SrcLoc
          | ComplexT W !SrcLoc
          | StringT !SrcLoc
          | StructT Struct !SrcLoc
          | ArrT Type Type !SrcLoc

          -- omega types
          | C Type !SrcLoc
          | T !SrcLoc

          -- mu types
          | ST Type Type Type !SrcLoc

          -- rho types
          | RefT Type !SrcLoc

          -- phi types
          | FunT [TyVar] [IVar] [Type] Type !SrcLoc

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

instance Named TyVar where
    namedSymbol (TyVar n) = namedSymbol n

instance Named IVar where
    namedSymbol (IVar n) = namedSymbol n

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Show a => Show (IORef a) where
    showsPrec d ref =
        showParen (d > appPrec) $
        showString "(unsafePerformIO . newRef) " .
        showsPrec (appPrec1) ((unsafePerformIO . readRef) ref)

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

instance Pretty IVar where
    ppr (IVar n) = ppr n

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

    pprPrec _ (IntT w _) | w == dEFAULT_INT_WIDTH =
        text "int"

    pprPrec _ (IntT w _) =
        text "int" <> ppr w

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec _ (ComplexT w _) =
        text "complex" <> ppr w

    pprPrec _ (StringT _) =
        text "string"

    pprPrec _ (StructT s _) =
        text "struct" <+> ppr s

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)

    pprPrec p (C tau _) =
        parensIf (p > appPrec) $
        text "C" <+> pprPrec appPrec1 tau

    pprPrec _ (T _) =
        text "T"

    pprPrec p (ST w tau1 tau2 _) =
        parensIf (p > appPrec) $
        text "ST" <+> align (pprPrec appPrec1 w <+/> pprPrec appPrec1 tau1 <+/> pprPrec appPrec1 tau2)

    pprPrec p (RefT tau _) =
        parensIf (p > appPrec) $
        text "ref" <+> ppr tau

    pprPrec p (FunT alphas iotas taus tau _) =
        parensIf (p > arrowPrec) $
        pprForall alphas <+>
        pprArgs iotas taus <+>
        text "->" <+>
        pprPrec arrowPrec1 tau
      where
        pprForall :: [TyVar] -> Doc
        pprForall []     = empty
        pprForall alphas = text "forall" <+> commasep (map ppr alphas) <+> dot

        pprArgs :: [IVar] -> [Type] -> Doc
        pprArgs [] [tau1] =
            ppr tau1

        pprArgs [] taus =
            parens (commasep (map ppr taus))

        pprArgs iotas taus =
            parens (commasep (map ppr iotas) <> text ";" <+> commasep (map ppr taus))

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

#if !defined(ONLY_TYPEDEFS)
{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Type TyVar where
    fvs (UnitT {})              = mempty
    fvs (BoolT {})              = mempty
    fvs (BitT {})               = mempty
    fvs (IntT {})               = mempty
    fvs (FloatT {})             = mempty
    fvs (ComplexT {})           = mempty
    fvs (StringT {})            = mempty
    fvs (StructT _ _)           = mempty
    fvs (ArrT tau1 tau2 _)      = fvs tau1 <> fvs tau2
    fvs (C tau _)               = fvs tau
    fvs (T _)                   = mempty
    fvs (ST omega tau1 tau2 _)  = fvs omega <> fvs tau1 <> fvs tau2
    fvs (RefT tau _)            = fvs tau
    fvs (FunT tvs _ taus tau _) = (fvs taus <> fvs tau) <\\> fromList tvs
    fvs (ConstI _ _)            = mempty
    fvs (VarI _ _)              = mempty
    fvs (TyVarT tv _)           = singleton tv
    fvs (MetaT _ _)             = mempty

instance Fvs Type IVar where
    fvs (UnitT {})                = mempty
    fvs (BoolT {})                = mempty
    fvs (BitT {})                 = mempty
    fvs (IntT {})                 = mempty
    fvs (FloatT {})               = mempty
    fvs (ComplexT {})             = mempty
    fvs (StringT {})              = mempty
    fvs (StructT _ _)             = mempty
    fvs (ArrT tau1 tau2 _)        = fvs tau1 <> fvs tau2
    fvs (C tau _)                 = fvs tau
    fvs (T _)                     = mempty
    fvs (ST omega tau1 tau2 _)    = fvs omega <> fvs tau1 <> fvs tau2
    fvs (RefT tau _)              = fvs tau
    fvs (FunT _ iotas taus tau _) = (fvs taus <> fvs tau) <\\> fromList iotas
    fvs (ConstI _ _)              = mempty
    fvs (VarI iv _)               = singleton iv
    fvs (TyVarT _ _)              = mempty
    fvs (MetaT _ _)               = mempty

instance Fvs Type MetaTv where
    fvs (UnitT {})             = mempty
    fvs (BoolT {})             = mempty
    fvs (BitT {})              = mempty
    fvs (IntT {})              = mempty
    fvs (FloatT {})            = mempty
    fvs (ComplexT {})          = mempty
    fvs (StringT {})           = mempty
    fvs (StructT _ _)          = mempty
    fvs (ArrT tau1 tau2 _)     = fvs tau1 <> fvs tau2
    fvs (C tau _)              = fvs tau
    fvs (T _)                  = mempty
    fvs (ST omega tau1 tau2 _) = fvs omega <> fvs tau1 <> fvs tau2
    fvs (RefT tau _)           = fvs tau
    fvs (FunT _ _ taus tau _)  = fvs taus <> fvs tau
    fvs (ConstI _ _)           = mempty
    fvs (VarI _ _)             = mempty
    fvs (TyVarT _ _)           = mempty
    fvs (MetaT mtv _)          = singleton mtv

instance HasVars Type TyVar where
    allVars (UnitT {})              = mempty
    allVars (BoolT {})              = mempty
    allVars (BitT {})               = mempty
    allVars (IntT {})               = mempty
    allVars (FloatT {})             = mempty
    allVars (ComplexT {})           = mempty
    allVars (StringT {})            = mempty
    allVars (StructT _ _)           = mempty
    allVars (ArrT tau1 tau2 _)      = allVars tau1 <> allVars tau2
    allVars (C tau _)               = allVars tau
    allVars (T _)                   = mempty
    allVars (ST omega tau1 tau2 _)  = allVars omega <> allVars tau1 <> allVars tau2
    allVars (RefT tau _)            = allVars tau
    allVars (FunT tvs _ taus tau _) = fromList tvs <> allVars taus <> allVars tau
    allVars (ConstI _ _)            = mempty
    allVars (VarI _ _)              = mempty
    allVars (TyVarT tv _)           = singleton tv
    allVars (MetaT _ _)             = mempty

instance HasVars Type IVar where
    allVars (UnitT {})                = mempty
    allVars (BoolT {})                = mempty
    allVars (BitT {})                 = mempty
    allVars (IntT {})                 = mempty
    allVars (FloatT {})               = mempty
    allVars (ComplexT {})             = mempty
    allVars (StringT {})              = mempty
    allVars (StructT _ _)             = mempty
    allVars (ArrT tau1 tau2 _)        = allVars tau1 <> allVars tau2
    allVars (C tau _)                 = allVars tau
    allVars (T _)                     = mempty
    allVars (ST omega tau1 tau2 _)    = allVars omega <> allVars tau1 <> allVars tau2
    allVars (RefT tau _)              = allVars tau
    allVars (FunT _ iotas taus tau _) = fromList iotas <> allVars taus <> allVars tau
    allVars (ConstI _ _)              = mempty
    allVars (VarI iv _)               = singleton iv
    allVars (TyVarT _ _)              = mempty
    allVars (MetaT _ _)               = mempty

instance HasVars Type MetaTv where
    allVars (UnitT {})             = mempty
    allVars (BoolT {})             = mempty
    allVars (BitT {})              = mempty
    allVars (IntT {})              = mempty
    allVars (FloatT {})            = mempty
    allVars (ComplexT {})          = mempty
    allVars (StringT {})           = mempty
    allVars (StructT _ _)          = mempty
    allVars (ArrT tau1 tau2 _)     = allVars tau1 <> allVars tau2
    allVars (C tau _)              = allVars tau
    allVars (T _)                  = mempty
    allVars (ST omega tau1 tau2 _) = allVars omega <> allVars tau1 <> allVars tau2
    allVars (RefT tau _)           = allVars tau
    allVars (FunT _ _ taus tau _)  = allVars taus <> allVars tau
    allVars (ConstI _ _)           = mempty
    allVars (VarI _ _)             = mempty
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

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ArrT tau1 tau2 l) =
        ArrT (subst theta phi tau1) (subst theta phi tau2) l

    subst theta phi (C tau l) =
        C (subst theta phi tau) l

    subst _ _ tau@(T {}) =
        tau

    subst theta phi (ST tau1 tau2 tau3 l) =
        ST (subst theta phi tau1) (subst theta phi tau2) (subst theta phi tau3) l

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (FunT alphas iotas taus tau l) =
        FunT alphas iotas (subst theta phi taus) (subst theta phi tau) l

    subst _ _ tau@(ConstI {}) =
        tau

    subst _ _ tau@(VarI {}) =
        tau

    subst _ _ tau@(TyVarT {}) =
        tau

    subst theta _ tau@(MetaT mtv _) =
        fromMaybe tau (Map.lookup mtv theta)

instance Subst Type IVar Type where
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

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ArrT tau1 tau2 l) =
        ArrT (subst theta phi tau1) (subst theta phi tau2) l

    subst theta phi (C tau l) =
        C (subst theta phi tau) l

    subst _ _ tau@(T {}) =
        tau

    subst theta phi (ST tau1 tau2 tau3 l) =
        ST (subst theta phi tau1) (subst theta phi tau2) (subst theta phi tau3) l

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (FunT alphas iotas taus tau l) =
        FunT alphas iotas' (subst theta' phi' taus) (subst theta' phi' tau) l
      where
        (iotas', theta', phi') = freshen iotas theta phi

    subst _ _ tau@(ConstI {}) =
        tau

    subst theta _ tau@(VarI v _) =
        fromMaybe tau (Map.lookup v theta)

    subst _ _ tau@(TyVarT {}) =
        tau

    subst _ _ tau@(MetaT {}) =
        tau

instance Subst Type TyVar Type where
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

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ArrT tau1 tau2 l) =
        ArrT (subst theta phi tau1) (subst theta phi tau2) l

    subst theta phi (C tau l) =
        C (subst theta phi tau) l

    subst _ _ tau@(T {}) =
        tau

    subst theta phi (ST tau1 tau2 tau3 l) =
        ST (subst theta phi tau1) (subst theta phi tau2) (subst theta phi tau3) l

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (FunT alphas iotas taus tau l) =
        FunT alphas' iotas (subst theta' phi' taus) (subst theta' phi' tau) l
      where
        (alphas', theta', phi') = freshen alphas theta phi

    subst _ _ tau@(ConstI {}) =
        tau

    subst _ _ tau@(VarI {}) =
        tau

    subst theta _ tau@(TyVarT alpha _) =
        fromMaybe tau (Map.lookup alpha theta)

    subst _ _ tau@(MetaT {}) =
        tau

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

instance Freshen TyVar TyVar Type where
    freshen alpha@(TyVar n) theta phi | alpha `Set.member` phi =
        (alpha', theta', phi')
      where
        phi'    = Set.insert alpha' phi
        theta'  = Map.insert alpha (tyVarT alpha') theta
        alpha'  = head [alpha  | i <- [show i | i <- [1..]]
                               , let alpha' = TyVar n { nameSym = intern (s ++ i) }
                               , alpha' `Set.notMember` phi]
          where
            s :: String
            s = namedString n

        tyVarT :: TyVar -> Type
        tyVarT tv = TyVarT tv (srclocOf tv)

    freshen alpha theta phi =
        (alpha, theta', phi')
      where
        phi'    = Set.insert alpha phi
        theta'  = Map.delete alpha theta

instance Freshen IVar IVar Type where
    freshen alpha@(IVar n) theta phi | alpha `Set.member` phi =
        (alpha', theta', phi')
      where
        phi'    = Set.insert alpha' phi
        theta'  = Map.insert alpha (ivarT alpha') theta
        alpha'  = head [alpha  | i <- [show i | i <- [1..] :: [Int]]
                               , let alpha' = IVar n { nameSym = intern (s ++ i) }
                               , alpha' `Set.notMember` phi]
          where
            s :: String
            s = namedString n

        ivarT :: IVar -> Type
        ivarT v = VarI v (srclocOf v)

    freshen alpha theta phi =
        (alpha, theta', phi')
      where
        phi'    = Set.insert alpha phi
        theta'  = Map.delete alpha theta

#include "KZC/Check/Types-instances.hs"

#endif /*!defined(ONLY_TYPEDEFS) */
