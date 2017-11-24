{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Core.Syntax
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Core.Syntax (
    Var(..),
    WildVar(..),
    Field(..),
    Struct(..),
    TyVar(..),

    IP(..),
    ipBitSize,
    ipIsSigned,
    ipRange,

    QP(..),
    qpBitSize,
    qpIsSigned,
    qpIntBits,
    qpFracBits,
    qpRange,
    qpResolution,
    qpToFractional,
    qpFromFractional,

    FP(..),
    fpBitSize,

    Const(..),
    Program(..),
    Import(..),
    Main(..),
    Decl(..),
    View(..),
    LocalDecl(..),
    BoundVar(..),
    OccInfo(..),
    Exp(..),
    GenInterval(..),
    LutSize,
    Gen(..),
    ToExp(..),
    UnrollAnn(..),
    InlineAnn(..),
    mayUnroll,
    PipelineAnn(..),
    VectAnn(..),
    Unop(..),
    isFunUnop,
    Binop(..),
    StructDef(..),
    Type(..),
    Nat,
    Omega(..),
    Trait(..),
    Kind(..),
    Tvk,

    mkBoundVar,

    Arg(..),
    Step(..),
    Tag(..),
    Comp(..),
    Rate(..),
    M(..),

    mkComp,
#if !defined(ONLY_TYPEDEFS)
    compLabel,
    setCompLabel,
    rewriteStepsLabel,
    compUsedLabels,
    stepLabel,
    setStepLabel,

    Size(..),
    LUTSize(..),
#endif /* !defined(ONLY_TYPEDEFS) */

    isComplexStruct,

    Stm(..),

#if !defined(ONLY_TYPEDEFS)
    LiftedBool(..),
    LiftedEq(..),
    LiftedOrd(..),
    LiftedNum(..),
    LiftedIntegral(..),
    LiftedFloating(..),
    LiftedBits(..),
    LiftedCast(..),
#endif /* !defined(ONLY_TYPEDEFS) */
  ) where

import Prelude hiding ((<=))

import Control.Monad.Reader
import Data.Loc
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Data.Symbol
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Lattice
import KZC.Expr.Syntax (Var(..),
                        Field(..),
                        Struct(..),
                        TyVar(..),

                        IP(..),
                        ipBitSize,
                        ipIsSigned,
                        ipRange,

                        QP(..),
                        qpBitSize,
                        qpIsSigned,
                        qpIntBits,
                        qpFracBits,
                        qpRange,
                        qpResolution,
                        qpToFractional,
                        qpFromFractional,

                        FP(..),
                        fpBitSize,

                        GenInterval(..),

                        Const(..),
                        UnrollAnn(..),
                        mayUnroll,
                        InlineAnn(..),
                        PipelineAnn(..),
                        VectAnn(..),
                        Unop(..),
                        isFunUnop,
                        Binop(..),
                        StructDef(..),
                        Type(..),
                        Nat,
                        Omega(..),
                        Trait(..),
                        Kind(..),
                        Tvk,

                        isComplexStruct,

                        Stm(..),

#if !defined(ONLY_TYPEDEFS)
                        LiftedBool(..),
                        LiftedEq(..),
                        LiftedOrd(..),
                        LiftedNum(..),
                        LiftedIntegral(..),
                        LiftedFloating(..),
                        LiftedBits(..),
                        LiftedCast(..),

                        pprForall,
                        pprTyApp,
                        pprTypeSig,
                        pprFunDecl
#endif /* !defined(ONLY_TYPEDEFS) */
                       )
import KZC.Label
import KZC.Name
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Staged
import KZC.Util.Summary
import KZC.Util.Uniq
import KZC.Vars

data BoundVar = BoundV
    { bVar         :: Var
    , bOccInfo     :: Maybe OccInfo
    , bTainted     :: Maybe Bool
    , bNeedDefault :: Maybe Bool
    , bStaticRef   :: Maybe Bool
    }
  deriving (Eq, Ord, Read, Show)

instance IsString BoundVar where
    fromString s = mkBoundVar (fromString s)

instance Named BoundVar where
    namedSymbol bv = namedSymbol (bVar bv)

    mapName f bv = bv { bVar = mapName f (bVar bv) }

instance Gensym BoundVar where
    gensymAt s l =
        BoundV <$> gensymAt s l
               <*> pure Nothing
               <*> pure Nothing
               <*> pure Nothing
               <*> pure Nothing

    uniquify bv = do
        u <- newUnique
        return $ mapName (\n -> n { nameSort = Internal u }) bv

mkBoundVar :: Var -> BoundVar
mkBoundVar v = BoundV v Nothing Nothing Nothing Nothing

data WildVar = WildV
             | TameV BoundVar
  deriving (Eq, Ord, Read, Show)

data Program l = Program [Import] [Decl l] (Maybe (Main l))
  deriving (Eq, Ord, Read, Show)

data Import = Import ModuleName
  deriving (Eq, Ord, Read, Show)

data Main l = Main (Comp l) Type
  deriving (Eq, Ord, Read, Show)

data Decl l = StructD StructDef !SrcLoc
            | LetD LocalDecl !SrcLoc
            | LetFunD BoundVar [Tvk] [(Var, Type)] Type Exp !SrcLoc
            | LetExtFunD BoundVar [Tvk] [(Var, Type)] Type !SrcLoc
            | LetCompD BoundVar Type (Comp l) !SrcLoc
            | LetFunCompD BoundVar [Tvk] [(Var, Type)] Type (Comp l) !SrcLoc
  deriving (Eq, Ord, Read, Show)

data View = IdxVW Var Exp (Maybe Nat) !SrcLoc
  deriving (Eq, Ord, Read, Show)

data LocalDecl -- | Standard let binding
               = LetLD BoundVar Type Exp !SrcLoc
               -- | Ref binding
               | LetRefLD BoundVar Type (Maybe Exp) !SrcLoc
               -- | Type variable binding
               | LetTypeLD TyVar Kind Type !SrcLoc
               -- | An array view binding
               | LetViewLD BoundVar Type View !SrcLoc
  deriving (Eq, Ord, Read, Show)

data OccInfo = Dead
             | Once
             | OnceInFun
             | ManyBranch
             | Many
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp Exp !SrcLoc
         | LetE LocalDecl Exp !SrcLoc
         -- Functions
         | CallE Var [Type] [Exp] !SrcLoc
         -- References
         | DerefE Exp !SrcLoc
         | AssignE Exp Exp !SrcLoc
         -- Lower a (singleton) type to a term. Right now this only works for
         -- types of kind nat.
         | LowerE Type !SrcLoc
         -- Loops
         | WhileE Exp Exp !SrcLoc
         | ForE UnrollAnn Var Type (GenInterval Exp) Exp !SrcLoc
         -- Arrays
         | ArrayE [Exp] !SrcLoc
         | IdxE Exp Exp (Maybe Nat) !SrcLoc
         -- Structs
         | StructE StructDef [Type] [(Field, Exp)] !SrcLoc
         | ProjE Exp Field !SrcLoc
         -- Casts
         | CastE Type Exp !SrcLoc
         | BitcastE Type Exp !SrcLoc
         -- Print
         | PrintE Bool [Exp] !SrcLoc
         | ErrorE Type String !SrcLoc
         -- Monadic operations
         | ReturnE InlineAnn Exp !SrcLoc
         | BindE WildVar Type Exp Exp !SrcLoc
         -- LUT
         | LutE !LutSize Exp
         -- Generator expression
         | GenE Exp [Gen] !SrcLoc
  deriving (Eq, Ord, Read, Show)

-- | LUT size in bytes
type LutSize = Integer

data Gen = GenG    Var Type Const !SrcLoc
         | GenRefG Var Type Const !SrcLoc
  deriving (Eq, Ord, Read, Show)

class ToExp a where
    toExp :: a -> Exp

instance ToExp View where
    toExp (IdxVW v e len l) = IdxE (VarE v l) e len l

-- | An argument to a call to a computation function. Arguments may be
-- expressions or computations.
data Arg l = ExpA  Exp
           | CompA (Comp l)
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data Step l = VarC l Var !SrcLoc
            | CallC l Var [Type] [Arg l] !SrcLoc
            | IfC l Exp (Comp l) (Comp l) !SrcLoc
            | LetC l LocalDecl !SrcLoc

            | WhileC l Exp (Comp l) !SrcLoc
            | ForC l UnrollAnn Var Type (GenInterval Exp) (Comp l) !SrcLoc

            -- | Lift an expression of type
            -- @forall s a b . ST (C tau) s a b@ into the monad. 'LiftC' and
            -- 'ReturnC' differ only for the purpose of type checking.
            | LiftC l Exp !SrcLoc
            | ReturnC l Exp !SrcLoc
            | BindC l WildVar Type !SrcLoc

            | TakeC l Type !SrcLoc
            | TakesC l Nat Type !SrcLoc
            | EmitC l Exp !SrcLoc
            | EmitsC l Exp !SrcLoc
            | RepeatC l (VectAnn Nat) (Comp l) !SrcLoc
            | ParC PipelineAnn Type (Comp l) (Comp l) !SrcLoc
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data Tag -- | Computation is the identity with given rate
             = IdT !Int
  deriving (Eq, Ord, Read, Show)

data Comp l = Comp { unComp   :: [Step l]
                   , compRate :: !(Maybe (Rate M))
                   -- | True if this computation is the identity
                   , compTag  :: Maybe Tag
                   }
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

instance Monoid (Comp l) where
    mempty = Comp mempty Nothing Nothing

    -- Appending steps tosses out rate information
    x `mappend` y = Comp { unComp   = unComp x <> unComp y
                         , compRate = Nothing
                         , compTag  = Nothing
                         }

mkComp :: [Step l] -> Comp l
mkComp steps = mempty { unComp = steps }

-- See Note [Rates] in KZC.Analysis.Rate for the full explanation of what the
-- next two data types mean.

data Rate m = CompR  { inMult :: !m, outMult :: !m }
            | TransR { inMult :: !m, outMult :: !m }
  deriving (Eq, Ord, Read, Show)

data M -- | Multiplicity is fixed constant, which may be zero
       = N !Int
       -- | Multiplicity is a multiple (zero or more) of a fixed, /non-zero/,
       -- constant
       | Z !Int
       -- | Multiplicity is a multiple (one or more) of a fixed, /non-zero/,
       -- constant
       | P !Int
  deriving (Eq, Ord, Read, Show)

#if !defined(ONLY_TYPEDEFS)
{------------------------------------------------------------------------------
 -
 - Occurrence info lattice
 -
 ------------------------------------------------------------------------------}
instance Poset OccInfo where
    Dead       <= _          = True
    Once       <= Once       = True
    OnceInFun  <= OnceInFun  = True
    ManyBranch <= ManyBranch = True
    _          <= Many       = True
    _          <= _          = False

instance Lattice OccInfo where
    Dead `lub` x    = x
    x    `lub` Dead = x
    _    `lub` _    = Many

    Dead `glb` _    = Dead
    _    `glb` Dead = Dead
    Many `glb` x    = x
    x    `glb` Many = x
    x    `glb` y
        | x <= y    = x
        | y <= x    = y
        | otherwise = Dead

instance BottomLattice OccInfo where
    bot = Dead

instance TopLattice OccInfo where
    top = Many

instance BoundedLattice OccInfo where

instance BranchLattice OccInfo where
    Dead       `bub` x          = x
    x          `bub` Dead       = x
    Once       `bub` Once       = ManyBranch
    Once       `bub` ManyBranch = ManyBranch
    ManyBranch `bub` Once       = ManyBranch
    ManyBranch `bub` ManyBranch = ManyBranch
    _          `bub` _          = Many

{------------------------------------------------------------------------------
 -
 - Computation labels
 -
 ------------------------------------------------------------------------------}
compLabel :: Monad m => Comp l -> m l
compLabel Comp{ unComp = [] }     = fail "compLabel: empty computation"
compLabel Comp{ unComp = step:_ } = stepLabel step

setCompLabel :: l -> Comp l -> Comp l
setCompLabel _ comp@Comp{ unComp = [] } =
    comp

setCompLabel l comp@Comp{ unComp = step:steps } =
    comp{ unComp = setStepLabel l step:steps }

-- | Rewrite the label of the first step in a computation and ensure that any
-- references to the old label are rewritten to refer to the new label.
rewriteStepsLabel :: (IsLabel l, Monad m) => l -> [Step l] -> m [Step l]
rewriteStepsLabel _ steps@[] =
    return steps

rewriteStepsLabel l_new (step:steps) = do
    l_old <- stepLabel step
    return $ subst1 (l_old /-> l_new) (step:steps)

compUsedLabels :: forall l . Ord l => Comp l -> Set l
compUsedLabels comp =
    go (unComp comp)
  where
    go :: [Step l] -> Set l
    go []                         = Set.empty
    go (IfC _ _ l r _:steps)      = compUsedLabels l <> compUsedLabels r <> go steps
    go (WhileC _ _ c _:steps)     = compUsedLabels c <> go steps
    go (ForC _ _ _ _ _ c _:steps) = compUsedLabels c <> go steps
    go (RepeatC _ _ c _:steps)    = compUsedLabels c <> go steps
    go (ParC _ _ l r _:steps)     = compUsedLabels l <> compUsedLabels r <> go steps
    go (_:steps)                  = go steps

stepLabel :: Monad m => Step l -> m l
stepLabel (VarC l _ _)         = return l
stepLabel (CallC l _ _ _ _)    = return l
stepLabel (IfC l _ _ _ _)      = return l
stepLabel (LetC l _ _)         = return l
stepLabel (WhileC l _ _ _)     = return l
stepLabel (ForC l _ _ _ _ _ _) = return l
stepLabel (LiftC l _ _)        = return l
stepLabel (ReturnC l _ _)      = return l
stepLabel (BindC l _ _ _)      = return l
stepLabel (TakeC l _ _)        = return l
stepLabel (TakesC l _ _ _)     = return l
stepLabel (EmitC l _ _)        = return l
stepLabel (EmitsC l _ _)       = return l
stepLabel (RepeatC l _ _ _)    = return l
stepLabel (ParC _ _ _ right _) = compLabel right

setStepLabel :: l -> Step l -> Step l
setStepLabel l (VarC _ v s)                = VarC l v s
setStepLabel l (CallC _ v taus es s)       = CallC l v taus es s
setStepLabel l (IfC _ e c1 c2 s)           = IfC l e c1 c2 s
setStepLabel l (LetC _ decl s)             = LetC l decl s
setStepLabel l (WhileC _ e c s)            = WhileC l e c s
setStepLabel l (ForC _ ann v tau gint c s) = ForC l ann v tau gint c s
setStepLabel l (LiftC _ e s)               = LiftC l e s
setStepLabel l (ReturnC _ e s)             = ReturnC l e s
setStepLabel l (BindC _ wv tau s)          = BindC l wv tau s
setStepLabel l (TakeC _ tau s)             = TakeC l tau s
setStepLabel l (TakesC _ i tau s)          = TakesC l i tau s
setStepLabel l (EmitC _ e s)               = EmitC l e s
setStepLabel l (EmitsC _ e s)              = EmitsC l e s
setStepLabel l (RepeatC _ ann c s)         = RepeatC l ann c s
setStepLabel l (ParC ann tau left right s) = ParC ann tau left (setCompLabel l right) s

{------------------------------------------------------------------------------
 -
 - Computation size
 -
 ------------------------------------------------------------------------------}

class Size a where
    size :: a -> Int

    sizeList :: [a] -> Int
    sizeList = sum . map size

instance Size a => Size [a] where
    size = sizeList

instance Size Const where
    size UnitC{}            = 0
    size BoolC{}            = 1
    size IntC{}             = 1
    size FixC{}             = 1
    size FloatC{}           = 1
    size StringC{}          = 1
    size (ArrayC cs)        = if V.null cs then 0 else V.length cs * size (V.head cs)
    size (ReplicateC n c)   = n * size c
    size EnumC{}            = 0
    size (StructC _ _ flds) = size (map snd flds)

instance Size LocalDecl where
    size (LetLD _ _ e _)           = 1 + size e
    size (LetRefLD _ _ Nothing _)  = 1
    size (LetRefLD _ _ (Just e) _) = 1 + size e
    size LetTypeLD{}               = 0
    size LetViewLD{}               = 0

instance Size Exp where
    size (ConstE c _)           = size c
    size VarE{}                 = 1
    size (UnopE _ e _)          = 1 + size e
    size (BinopE _ e1 e2 _)     = 1 + size e1 + size e2
    size (IfE e1 e2 e3 _)       = 1 + size e1 + size e2 + size e3
    size (LetE decl e _)        = size decl + size e
    size (CallE _ _ es _)       = 1 + size es
    size (DerefE e _)           = 1 + size e
    size (AssignE e1 e2 _)      = 1 + size e1 + size e2
    size (WhileE e1 e2 _)       = 1 + size e1 + size e2
    size (ForE _ _ _ gint e3 _) = 1 + size gint + size e3
    size (ArrayE es _)          = 1 + size es
    size LowerE{}               = 1
    size (IdxE e1 e2 _ _)       = 1 + size e1 + size e2
    size (StructE _ _ flds _)   = size (map snd flds)
    size (ProjE e _ _)          = 1 + size e
    size (CastE _ e _)          = size e
    size (BitcastE _ e _)       = size e
    size (PrintE _ es _)        = 1 + size es
    size ErrorE{}               = 1
    size (ReturnE _ e _)        = size e
    size (BindE _ _ e1 e2 _)    = size e1 + size e2
    size LutE{}                 = 1
    size GenE{}                 = 0

instance Size e => Size (GenInterval e) where
    size int = sum (fmap size int)

instance Size (Arg l) where
    size (ExpA e)  = size e
    size (CompA c) = size c

instance Size (Step l) where
    size VarC{}                  = 1
    size CallC{}                 = 1
    size (IfC _ e c1 c2 _)       = 1 + size e + size c1 + size c2
    size (LetC _ decl _)         = size decl
    size (WhileC _ e c _)        = 1 + size e + size c
    size (ForC _ _ _ _ gint c _) = 1 + size gint + size c
    size (LiftC _ e _)           = size e
    size (ReturnC _ e _)         = size e
    size BindC{}                 = 0
    size TakeC{}                 = 1
    size TakesC{}                = 1
    size (EmitC _ e _)           = 1 + size e
    size (EmitsC _ e _)          = 1 + size e
    size (RepeatC _ _ c _)       = size c
    size (ParC _ _ c1 c2 _)      = size c1 + size c2

instance Size (Comp l) where
    size = size . unComp

{------------------------------------------------------------------------------
 -
 - LUT size
 -
 ------------------------------------------------------------------------------}

class LUTSize a where
    lutSize :: a -> Integer

    lutSizeList :: [a] -> Integer
    lutSizeList = sum . map lutSize

instance LUTSize a => LUTSize [a] where
    lutSize = lutSizeList

instance LUTSize LocalDecl where
    lutSize (LetLD _ _ e _)           = lutSize e
    lutSize (LetRefLD _ _ Nothing _)  = 0
    lutSize (LetRefLD _ _ (Just e) _) = lutSize e
    lutSize LetTypeLD{}               = 0
    lutSize LetViewLD{}               = 0

instance LUTSize Exp where
    lutSize ConstE{}              = 0
    lutSize VarE{}                = 0
    lutSize (UnopE _ e _)         = lutSize e
    lutSize (BinopE _ e1 e2 _)    = lutSize e1 + lutSize e2
    lutSize (IfE e1 e2 e3 _)      = lutSize e1 + lutSize e2 + lutSize e3
    lutSize (LetE decl e _)       = lutSize decl + lutSize e
    lutSize (CallE _ _ es _)      = lutSize es
    lutSize (DerefE e _)          = lutSize e
    lutSize (AssignE e1 e2 _)     = lutSize e1 + lutSize e2
    lutSize (WhileE e1 e2 _)      = lutSize e1 + lutSize e2
    lutSize (ForE _ _ _ gint e _) = lutSize gint + lutSize e
    lutSize (ArrayE es _)         = lutSize es
    lutSize LowerE{}              = 0
    lutSize (IdxE e1 e2 _ _)      = lutSize e1 + lutSize e2
    lutSize (StructE _ _ flds _)  = lutSize (map snd flds)
    lutSize (ProjE e _ _)         = lutSize e
    lutSize (CastE _ e _)         = lutSize e
    lutSize (BitcastE _ e _)      = lutSize e
    lutSize (PrintE _ es _)       = lutSize es
    lutSize ErrorE{}              = 0
    lutSize (ReturnE _ e _)       = lutSize e
    lutSize (BindE _ _ e1 e2 _)   = lutSize e1 + lutSize e2
    lutSize (LutE sz _)           = sz
    lutSize GenE{}                = 0

instance LUTSize e => LUTSize (GenInterval e) where
    lutSize int = sum (fmap lutSize int)

instance LUTSize (Arg l) where
    lutSize (ExpA e)  = lutSize e
    lutSize (CompA c) = lutSize c

instance LUTSize (Step l) where
    lutSize VarC{}                  = 0
    lutSize (CallC _ _ _ args _)    = lutSize args
    lutSize (IfC _ e c1 c2 _)       = lutSize e + lutSize c1 + lutSize c2
    lutSize (LetC _ decl _)         = lutSize decl
    lutSize (WhileC _ e c _)        = lutSize e + lutSize c
    lutSize (ForC _ _ _ _ gint c _) = lutSize gint + lutSize c
    lutSize (LiftC _ e _)           = lutSize e
    lutSize (ReturnC _ e _)         = lutSize e
    lutSize BindC{}                 = 0
    lutSize TakeC{}                 = 0
    lutSize TakesC{}                = 0
    lutSize (EmitC _ e _)           = lutSize e
    lutSize (EmitsC _ e _)          = lutSize e
    lutSize (RepeatC _ _ c _)       = lutSize c
    lutSize (ParC _ _ c1 c2 _)      = lutSize c1 + lutSize c2

instance LUTSize (Comp l) where
    lutSize = lutSize . unComp

{------------------------------------------------------------------------------
 -
 - Statements
 -
 ------------------------------------------------------------------------------}

expToStms :: Exp -> [Stm LocalDecl BoundVar Exp]
expToStms (LetE decl e l)               = LetS decl l : expToStms e
expToStms (ReturnE ann e l)             = [ReturnS ann e l]
expToStms (BindE WildV tau e1 e2 l)     = ExpS e1 (srclocOf e1) : BindS Nothing tau l : expToStms e2
expToStms (BindE (TameV v) tau e1 e2 l) = ExpS e1 (srclocOf e1) : BindS (Just v) tau l : expToStms e2
expToStms e                             = [ExpS e (srclocOf e)]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary (Decl l) where
    summary (StructD struct _)           = text "definition of" <+> summary struct
    summary (LetD decl _)                = summary decl
    summary (LetFunD f tvks _ _ _ _)     = text "definition of" <+> ppr f <> pprForall tvks
    summary (LetExtFunD f tvks _ _ _)    = text "definition of" <+> ppr f <> pprForall tvks
    summary (LetCompD v _ _ _)           = text "definition of" <+> ppr v
    summary (LetFunCompD f tvks _ _ _ _) = text "definition of" <+> ppr f <> pprForall tvks

instance Summary LocalDecl where
    summary (LetLD v _ _ _)         = text "definition of" <+> ppr v
    summary (LetRefLD v _ _ _)      = text "definition of" <+> ppr v
    summary (LetTypeLD alpha _ _ _) = text "definition of" <+> ppr alpha
    summary (LetViewLD v _ _ _)     = text "definition of" <+> ppr v

instance Summary Exp where
    summary e = text "expression:" <+> align (ppr e)

instance IsLabel l => Summary (Comp l) where
    summary c = text "computation:" <+> align (ppr c)

instance IsLabel l => Summary (Step l) where
    summary s = text "computation:" <+> ppr s

instance IsLabel l => Summary [Step l] where
    summary s = text "computation:" <+> ppr s

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty WildVar where
    ppr WildV     = text "_"
    ppr (TameV v) = ppr v

instance Pretty BoundVar where
    ppr bv = ppr (bVar bv) <> occdoc <> taintdoc <> dfltdoc <> staticdoc
      where
        occdoc, taintdoc :: Doc
        occdoc = case bOccInfo bv of
                   Nothing  -> empty
                   Just occ -> braces (ppr occ)

        taintdoc = case bTainted bv of
                     Nothing    -> empty
                     Just False -> empty
                     Just True  -> braces (text "tainted")

        dfltdoc = case bNeedDefault bv of
                     Nothing    -> empty
                     Just False -> empty
                     Just True  -> braces (text "default")

        staticdoc = case bStaticRef bv of
                      Nothing    -> empty
                      Just False -> empty
                      Just True  -> braces (text "static")

instance Pretty OccInfo where
    ppr Dead       = text "0"
    ppr Once       = text "1"
    ppr OnceInFun  = text "1fun"
    ppr ManyBranch = text "*branch"
    ppr Many       = text "*"

instance IsLabel l => Pretty (Main l) where
    ppr (Main comp tau) = ppr (LetCompD "main" tau comp noLoc)

instance IsLabel l => Pretty (Program l) where
    ppr (Program imports decls main) =
        ppr imports </>
        ppr decls </>
        ppr main

instance Pretty Import where
    ppr (Import mod) = text "import" <+> ppr mod

    pprList []      = empty
    pprList imports = semisep (map ppr imports)

instance IsLabel l => Pretty (Decl l) where
    pprPrec p (StructD struct _) =
        pprPrec p struct

    pprPrec p (LetD decl _) =
        pprPrec p decl

    pprPrec p (LetFunD f tvks vbs tau e _) =
        parensIf (p > appPrec) $
        align $
        text "fun" <+> pprFunDecl (bVar f) tvks vbs tau <> pprBody e

    pprPrec p (LetExtFunD f tvks vbs tau _) =
        parensIf (p > appPrec) $
        text "fun external" <+> pprFunDecl (bVar f) tvks vbs tau

    pprPrec p (LetCompD v tau c _) =
        parensIf (p > appPrec) $
        text "let comp" <+> ppr v <+> text ":" <+> ppr tau <+> text "=" <+/> ppr c

    pprPrec p (LetFunCompD f tvks vbs tau c _) =
        parensIf (p > appPrec) $
        text "fun comp" <+> pprFunDecl (bVar f) tvks vbs tau <+> ppr c

    pprList decls = stack (map ppr decls)

instance Pretty View where
    pprPrec _ (IdxVW v e Nothing _) =
        ppr v <> brackets (ppr e)

    pprPrec _ (IdxVW v e (Just i) _) =
        ppr v <> brackets (commasep [ppr e, ppr i])

instance Pretty LocalDecl where
    pprPrec p (LetLD v tau e _) =
        parensIf (p > appPrec) $
        text "let" <+> ppr v <+> text ":" <+> ppr tau <+> text "=" <+/> ppr e

    pprPrec p (LetRefLD v tau Nothing _) =
        parensIf (p > appPrec) $
        text "let ref" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetRefLD v tau (Just e) _) =
        parensIf (p > appPrec) $
        text "let ref" <+> ppr v <+> text ":" <+> ppr tau <+> text "=" <+/> ppr e

    pprPrec p (LetTypeLD alpha kappa tau _) =
        parensIf (p > appPrec) $
        text "let type" <+> ppr alpha <+> colon <+> ppr kappa <+> text "=" <+/> ppr tau

    pprPrec p (LetViewLD v tau vw _) =
        parensIf (p > appPrec) $
        text "let view" <+> ppr v <+> text ":" <+> ppr tau <+> text "=" <+/> ppr vw

    pprList decls = stack (map ppr decls)

instance Pretty Exp where
    pprPrec _ (ConstE c _) =
        ppr c

    pprPrec _ (VarE v _) =
        ppr v

    pprPrec _ (UnopE op e _) | isFunUnop op =
        ppr op <> parens (ppr e)

    pprPrec p (UnopE op e _) =
        unop p op e

    pprPrec p (BinopE op e1 e2 _) =
        infixop p op e1 e2

    pprPrec p (IfE e1 e2 e3 _) =
        parensIf (p >= appPrec) $
        text "if"   <+> pprPrec ifPrec1 e1 <+/>
        text "then" <+> pprPrec ifPrec1 e2 <+/>
        text "else" <+> pprPrec ifPrec1 e3

    pprPrec p (LetE decl body _) =
        parensIf (p > appPrec) $
        case body of
          LetE{} -> ppr decl <+> text "in" </> pprPrec doPrec1 body
          _      -> ppr decl </> text "in" <> pprBody body

    pprPrec _ (CallE f taus es _) =
        ppr f <> pprTyApp taus <> parens (commasep (map ppr es))

    pprPrec _ (DerefE v _) =
        text "!" <> pprPrec appPrec1 v

    pprPrec p (AssignE v e _) =
        parensIf (p > appPrec) $
        nest 2 $ ppr v <+> text ":=" <+/> pprPrec appPrec1 e

    pprPrec p (LowerE tau _) =
        pprPrec p tau

    pprPrec _ (WhileE e1 e2 _) =
        text "while" <+>
        group (pprPrec appPrec1 e1) <>
        pprBody e2

    pprPrec _ (ForE ann v tau gint e _) =
        ppr ann <+> text "for" <+> pprTypeSig v tau <+>
        text "in" <+> ppr gint <>
        pprBody e

    pprPrec _ (ArrayE es _) =
        text "arr" <+> enclosesep lbrace rbrace comma (map ppr es)

    pprPrec _ (IdxE e1 e2 Nothing _) =
        pprPrec appPrec1 e1 <> brackets (ppr e2)

    pprPrec _ (IdxE e1 e2 (Just len) _) =
        pprPrec appPrec1 e1 <> brackets (commasep [ppr e2, ppr len])

    pprPrec _ (StructE (StructDef struct _ _ _) taus fields _) =
        ppr struct <> pprTyApp taus <+> pprStruct comma equals fields

    pprPrec _ (ProjE e f _) =
        pprPrec appPrec1 e <> text "." <> ppr f

    pprPrec _ (CastE tau e _) =
        text "cast" <> angles (ppr tau) <> parens (ppr e)

    pprPrec _ (BitcastE tau e _) =
        text "bitcast" <> angles (ppr tau) <> parens (ppr e)

    pprPrec _ (PrintE True es _) =
        text "println" <> parens (commasep (map (pprPrec appPrec1) es))

    pprPrec _ (PrintE False es _) =
        text "print" <> parens (commasep (map (pprPrec appPrec1) es))

    pprPrec p (ErrorE tau s _) =
        parensIf (p > appPrec) $
        text "error" <+> text "@" <> pprPrec appPrec1 tau <+> (text . show) s

    pprPrec p (ReturnE ann e _) =
        parensIf (p > appPrec) $
        ppr ann <+> text "return" <+> pprPrec appPrec1 e

    pprPrec _ e@BindE{} =
        ppr (expToStms e)

    pprPrec p (LutE _ e) =
        parensIf (p > appPrec) $
        text "lut" <+> pprPrec appPrec1 e

    pprPrec _ (GenE e gs _) =
        lbracket <+>
        align (ppr e <+> char '|' <+>
               align (commasep (map ppr gs))) <+/>
        rbracket

instance Pretty Gen where
    ppr (GenG v tau c _) =
        ppr v <+> text ":" <+> ppr tau <+> text "<-" <+> ppr c

    ppr (GenRefG v tau c _) =
        ppr v <+> text ":" <+> ppr (RefT tau noLoc) <+> text "<-" <+> ppr c

instance IsLabel l => Pretty (Arg l) where
    pprPrec p (ExpA e)  = pprPrec p e
    pprPrec p (CompA c) = pprPrec p c

instance IsLabel l => Pretty (Step l) where
    ppr step = ppr (mkComp [step])

    pprList steps = ppr (mkComp steps)

instance IsLabel l => Pretty (Comp l) where
    pprPrec p comp =
        pprRate comp <+>
        case pprComp comp of
          [stm] -> parensIf (p > appPrec) stm
          stms  -> embrace stms
      where
        pprRate :: Comp l -> Doc
        pprRate Comp{ unComp = [ParC{}] }    = empty
        pprRate Comp{ unComp = [RepeatC{}] } = empty
        pprRate comp                         = ppr (compRate comp)

instance Pretty m => Pretty (Rate m) where
    ppr (CompR i o)  = brackets $ commasep [ppr i, ppr o]
    ppr (TransR i o) = ppr (CompR i o) <> char '*'

instance Pretty M where
    ppr (N i) = ppr i
    ppr (Z i) = ppr i <> char '*'
    ppr (P i) = ppr i <> char '+'

pprBody :: Exp -> Doc
pprBody e = softline <> ppr (expToStms e)

pprComp :: forall l . IsLabel l
        => Comp l
        -> [Doc]
pprComp comp =
    pprSteps (unComp comp)
  where
    pprSteps :: [Step l] -> [Doc]
    pprSteps [] =
        []

    pprSteps (VarC _ v _ : k) =
        pprBind k $
        ppr v

    pprSteps (CallC _ f taus es _ : k) =
        pprBind k $
        ppr f <> pprTyApp taus <> parens (commasep (map ppr es))

    pprSteps (IfC _ e1 e2 e3 _ : k) =
        pprBind k $
        text "if"   <+> pprPrec ifPrec1 e1 <+/>
        text "then" <+> pprPrec ifPrec1 e2 <+/>
        text "else" <+> pprPrec ifPrec1 e3

    pprSteps (LetC _ decl _ : k) =
        pprBind k $
        ppr decl

    pprSteps (WhileC _ e c _ : k) =
        pprBind k $
        text "while" <+>
        group (pprPrec appPrec1 e) <+>
        ppr c

    pprSteps (ForC _ ann v tau gint c@Comp{unComp=[_]} _ : k) =
        pprBind k $
        nest 2 $
        ppr ann <+> text "for" <+>
        group (parens (ppr v <+> colon <+> ppr tau) <+>
               text "in" <+> ppr gint) </>
        ppr c

    pprSteps (ForC _ ann v tau gint c _ : k) =
        pprBind k $
        ppr ann <+> text "for" <+>
        group (parens (ppr v <+> colon <+> ppr tau) <+>
               text "in" <+> ppr gint) <+/>
        ppr c

    pprSteps (LiftC _ e _ : k) =
        pprBind k $
        text "lift" <+> pprPrec appPrec1 e

    pprSteps (ReturnC _ e _ : k) =
        pprBind k $
        text "return" <+> pprPrec appPrec1 e

    pprSteps (BindC _ WildV _ _  : k) =
        text "_ <- _" : pprSteps k

    pprSteps (BindC _ (TameV v) tau _ : k) =
        bindDoc : pprSteps k
      where
        bindDoc :: Doc
        bindDoc = parens (ppr v <+> colon <+> ppr tau) <+>
                  text "<- _"

    pprSteps (TakeC _ tau _ : k) =
        pprBind k $
        text "take" <+> text "@" <> pprPrec tyappPrec1 tau

    pprSteps (TakesC _ i tau _ : k) =
        pprBind k $
        text "takes" <+> pprPrec appPrec1 i <+> text "@" <> pprPrec appPrec1 tau

    pprSteps (EmitC _ e _ : k) =
        pprBind k $
        text "emit" <+> pprPrec appPrec1 e

    pprSteps (EmitsC _ e _ : k) =
        pprBind k $
        text "emits" <+> pprPrec appPrec1 e

    pprSteps (RepeatC _ ann c _ : k) =
        pprBind k $
        ppr ann <+> text "repeat" <+> ppr c

    pprSteps (ParC ann tau e1 e2 _ : k) =
        pprBind k $
        group $
        pprPrec parrPrec e1 </>
        ppr ann <> text "@" <> pprPrec appPrec1 tau </>
        pprPrec parrPrec1 e2

    pprBind :: [Step l] -> Doc -> [Doc]
    pprBind [bind@BindC{}] step =
        step : pprSteps [bind]

    pprBind (BindC _ WildV _ _  : k) step =
        step : pprSteps k

    pprBind (BindC _ (TameV v) tau _ : k) step =
        step' : pprSteps k
      where
        step' :: Doc
        step' = parens (ppr v <+> colon <+> ppr tau) <+>
                text "<-" <+> align step

    pprBind k step =
        step : pprSteps k

{------------------------------------------------------------------------------
 -
 - Freshening bound variables
 -
 ------------------------------------------------------------------------------}

instance Freshen BoundVar Exp Var where
    freshen bv k =
        freshen (bVar bv) $ \v' ->
        k $ bv { bVar = v' }

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Binders WildVar Var where
    binders WildV     = mempty
    binders (TameV v) = singleton (bVar v)

instance Fvs (Decl l) Var where
    fvs StructD{}                   = mempty
    fvs (LetD decl _)               = fvs decl
    fvs (LetFunD v _ vbs _ e _)     = delete (bVar v) (fvs e) <\\> fromList (map fst vbs)
    fvs LetExtFunD{}                = mempty
    fvs (LetCompD v _ ccomp _)      = delete (bVar v) (fvs ccomp)
    fvs (LetFunCompD v _ vbs _ e _) = delete (bVar v) (fvs e) <\\> fromList (map fst vbs)

instance Binders (Decl l) Var where
    binders StructD{}                 = mempty
    binders (LetD decl _)             = binders decl
    binders (LetFunD v _ _ _ _ _)     = singleton (bVar v)
    binders (LetExtFunD v _ _ _ _)    = singleton (bVar v)
    binders (LetCompD v _ _ _)        = singleton (bVar v)
    binders (LetFunCompD v _ _ _ _ _) = singleton (bVar v)

instance Fvs View Var where
    fvs (IdxVW v e _ _) = singleton v <> fvs e

instance Fvs LocalDecl Var where
    fvs (LetLD v _ e _)      = delete (bVar v) (fvs e)
    fvs (LetRefLD v _ e _)   = delete (bVar v) (fvs e)
    fvs LetTypeLD{}          = mempty
    fvs (LetViewLD v _ vw _) = delete (bVar v) (fvs vw)

instance Binders LocalDecl Var where
    binders (LetLD v _ _ _)     =  singleton (bVar v)
    binders (LetRefLD v _ _ _)  = singleton (bVar v)
    binders LetTypeLD{}         = mempty
    binders (LetViewLD v _ _ _) = singleton (bVar v)

instance Fvs Exp Var where
    fvs ConstE{}              = mempty
    fvs (VarE v _)            = singleton v
    fvs (UnopE _ e _)         = fvs e
    fvs (BinopE _ e1 e2 _)    = fvs e1 <> fvs e2
    fvs (IfE e1 e2 e3 _)      = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetE decl body _)    = fvs decl <> (fvs body <\\> binders decl)
    fvs (CallE f _ es _)      = singleton f <> fvs es
    fvs (DerefE e _)          = fvs e
    fvs (AssignE e1 e2 _)     = fvs e1 <> fvs e2
    fvs LowerE{}              = mempty
    fvs (WhileE e1 e2 _)      = fvs e1 <> fvs e2
    fvs (ForE _ v _ gint e _) = fvs gint <> delete v (fvs e)
    fvs (ArrayE es _)         = fvs es
    fvs (IdxE e1 e2 _ _)      = fvs e1 <> fvs e2
    fvs (StructE _ _ flds _)  = fvs (map snd flds)
    fvs (ProjE e _ _)         = fvs e
    fvs (CastE _ e _)         = fvs e
    fvs (BitcastE _ e _)      = fvs e
    fvs (PrintE _ es _)       = fvs es
    fvs ErrorE{}              = mempty
    fvs (ReturnE _ e _)       = fvs e
    fvs (BindE wv _ e1 e2 _)  = fvs e1 <> (fvs e2 <\\> binders wv)
    fvs (LutE _ e)            = fvs e
    fvs (GenE e gs _)         = fvs e <\\> binders gs

instance Binders Gen Var where
    binders (GenG    v _ _ _) = singleton v
    binders (GenRefG v _ _ _) = singleton v

instance Fvs (Arg l) Var where
    fvs (ExpA e)  = fvs e
    fvs (CompA c) = fvs c

instance Fvs (Step l) Var where
    fvs (VarC _ v _)            = singleton v
    fvs (CallC _ f _ es _)      = singleton f <> fvs es
    fvs (IfC _ e1 e2 e3 _)      = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetC _ decl _)         = fvs decl
    fvs (WhileC _ e c _)        = fvs e <> fvs c
    fvs (ForC _ _ v _ gint c _) = fvs gint <> delete v (fvs c)
    fvs (LiftC _ e _)           = fvs e
    fvs (ReturnC _ e _)         = fvs e
    fvs BindC{}                 = mempty
    fvs TakeC{}                 = mempty
    fvs TakesC{}                = mempty
    fvs (EmitC _ e _)           = fvs e
    fvs (EmitsC _ e _)          = fvs e
    fvs (RepeatC _ _ c _)       = fvs c
    fvs (ParC _ _ e1 e2 _)      = fvs e1 <> fvs e2

instance Binders (Step l) Var where
    binders (LetC _ decl _)  = binders decl
    binders (BindC _ wv _ _) = binders wv
    binders _                = mempty

instance Fvs (Comp l) Var where
    fvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                   = mempty
        go (BindC _ wv _ _ : k) = go k <\\> binders wv
        go (LetC _ decl _ : k)  = fvs decl <> (go k <\\> binders decl)
        go (step : k)           = fvs step <> go k

instance Binders (Comp l) Var where
    binders comp = mconcat (map binders (unComp comp))

instance Fvs Exp v => Fvs [Exp] v where
    fvs = foldMap fvs

instance Fvs (Arg l) v => Fvs [Arg l] v where
    fvs = foldMap fvs

instance Fvs (Comp l) v => Fvs [Step l] v where
    fvs steps = fvs (mkComp steps)

{------------------------------------------------------------------------------
 -
 - All variables
 -
 ------------------------------------------------------------------------------}

instance HasVars WildVar Var where
    allVars WildV     = mempty
    allVars (TameV v) = singleton (bVar v)

instance HasVars (Decl l) Var where
    allVars StructD{}                   = mempty
    allVars (LetD decl _)               = allVars decl
    allVars (LetFunD v _ vbs _ e _)     = singleton (bVar v) <> fromList (map fst vbs) <> allVars e
    allVars (LetExtFunD v _ vbs _ _)    = singleton (bVar v) <> fromList (map fst vbs)
    allVars (LetCompD v _ ccomp _)      = singleton (bVar v) <> allVars ccomp
    allVars (LetFunCompD v _ vbs _ e _) = singleton (bVar v) <> fromList (map fst vbs) <> allVars e

instance HasVars View Var where
    allVars (IdxVW v e _ _) = singleton v <> allVars e

instance HasVars LocalDecl Var where
    allVars (LetLD v _ e _)      = singleton (bVar v) <> allVars e
    allVars (LetRefLD v _ e _)   = singleton (bVar v) <> allVars e
    allVars LetTypeLD{}          = mempty
    allVars (LetViewLD v _ vw _) = singleton (bVar v) <> allVars vw

instance HasVars Exp Var where
    allVars ConstE{}              = mempty
    allVars (VarE v _)            = singleton v
    allVars (UnopE _ e _)         = allVars e
    allVars (BinopE _ e1 e2 _)    = allVars e1 <> allVars e2
    allVars (IfE e1 e2 e3 _)      = allVars e1 <> allVars e2 <> allVars e3
    allVars (LetE decl body _)    = allVars decl <> allVars body
    allVars (CallE f _ es _)      = singleton f <> allVars es
    allVars (DerefE e _)          = allVars e
    allVars (AssignE e1 e2 _)     = allVars e1 <> allVars e2
    allVars LowerE{}              = mempty
    allVars (WhileE e1 e2 _)      = allVars e1 <> allVars e2
    allVars (ForE _ v _ gint e _) = singleton v <> allVars gint <> allVars e
    allVars (ArrayE es _)         = allVars es
    allVars (IdxE e1 e2 _ _)      = allVars e1 <> allVars e2
    allVars (StructE _ _ flds _)  = allVars (map snd flds)
    allVars (ProjE e _ _)         = allVars e
    allVars (CastE _ e _)         = allVars e
    allVars (BitcastE _ e _)      = allVars e
    allVars (PrintE _ es _)       = allVars es
    allVars ErrorE{}              = mempty
    allVars (ReturnE _ e _)       = allVars e
    allVars (BindE wv _ e1 e2 _)  = allVars wv <> allVars e1 <> allVars e2
    allVars (LutE _ e)            = allVars e
    allVars (GenE e gs _)         = allVars e <> allVars gs

instance HasVars Gen Var where
    allVars (GenG    v _ _ _) = singleton v
    allVars (GenRefG v _ _ _) = singleton v

instance HasVars (Arg l) Var where
    allVars (ExpA e)  = allVars e
    allVars (CompA c) = allVars c

instance HasVars (Step l) Var where
    allVars (VarC _ v _)            = singleton v
    allVars (CallC _ f _ es _)      = singleton f <> allVars es
    allVars (IfC _ e1 e2 e3 _)      = allVars e1 <> allVars e2 <> allVars e3
    allVars (LetC _ decl _)         = allVars decl
    allVars (WhileC _ e c _)        = allVars e <> allVars c
    allVars (ForC _ _ v _ gint c _) = singleton v <> allVars gint <> allVars c
    allVars (LiftC _ e _)           = allVars e
    allVars (ReturnC _ e _)         = allVars e
    allVars BindC{}                 = mempty
    allVars TakeC{}                 = mempty
    allVars TakesC{}                = mempty
    allVars (EmitC _ e _)           = allVars e
    allVars (EmitsC _ e _)          = allVars e
    allVars (RepeatC _ _ c _)       = allVars c
    allVars (ParC _ _ e1 e2 _)      = allVars e1 <> allVars e2

instance HasVars (Comp l) Var where
    allVars comp = allVars (unComp comp)

{------------------------------------------------------------------------------
 -
 - Polymorphic substitution
 -
 ------------------------------------------------------------------------------}

instance Subst a b Exp => Subst a b (Field, Exp) where
    substM (f, e) =
        (,) <$> pure f <*> substM e

{------------------------------------------------------------------------------
 -
 - Label substitution
 -
 ------------------------------------------------------------------------------}

instance (IsLabel l, Fvs l l, Subst l l l) => Subst l l (Step l) where
    substM (VarC l v s) =
        VarC <$> substM l <*> pure v <*> pure s

    substM (CallC l v taus es s) =
        CallC <$> substM l <*> pure v <*> pure taus <*> pure es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC <$> substM l <*> pure e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC <$> substM l <*> pure decl <*> pure s

    substM (WhileC l e c s) =
        WhileC <$> substM l <*> pure e <*> substM c <*> pure s

    substM (ForC l ann v tau gint c s) =
        ForC <$> substM l <*> pure ann <*> pure v <*> pure tau <*> pure gint <*> substM c <*> pure s

    substM (LiftC l e s) =
        LiftC <$> substM l <*> pure e <*> pure s

    substM (ReturnC l e s) =
        ReturnC <$> substM l <*> pure e <*> pure s

    substM (BindC l wv tau s) =
        BindC <$> substM l <*> pure wv <*> pure tau <*> pure s

    substM (TakeC l tau s) =
        TakeC <$> substM l <*> pure tau <*> pure s

    substM (TakesC l i tau s) =
        TakesC <$> substM l <*> pure i <*> pure tau <*> pure s

    substM (EmitC l e s) =
        EmitC <$> substM l <*> pure e <*> pure s

    substM (EmitsC l e s) =
        EmitsC <$> substM l <*> pure e <*> pure s

    substM (RepeatC l ann c s) =
        RepeatC <$> substM l <*> pure ann <*> substM c <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann tau <$> substM c1 <*> substM c2 <*> pure s

instance (IsLabel l, Fvs l l, Subst l l l) => Subst l l (Comp l) where
    substM comp = do
        steps' <- substM (unComp comp)
        return comp { unComp = steps' }

{------------------------------------------------------------------------------
 -
 - Type substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Type TyVar View where
   substM (IdxVW v e i l) =
       IdxVW v <$> substM e <*> pure i <*> pure l

instance Subst Type TyVar LocalDecl where
    substM (LetLD v tau e l) =
        LetLD v <$> substM tau <*> substM e <*> pure l

    substM (LetRefLD v tau e l) =
        LetRefLD v <$> substM tau <*> substM e <*> pure l

    substM (LetTypeLD alpha kappa tau l) =
        freshen alpha $ \alpha' ->
        LetTypeLD alpha' kappa <$> substM tau <*> pure l

    substM (LetViewLD v tau vw s) =
        LetViewLD v <$> substM tau <*> substM vw <*> pure s

instance Subst Type TyVar Exp where
    substM e@ConstE{} =
        return e

    substM e@VarE{} =
        return e

    substM (UnopE op e l) =
        UnopE op <$> substM e <*> pure l

    substM (BinopE op e1 e2 l) =
        BinopE op <$> substM e1 <*> substM e2 <*> pure l

    substM (IfE e1 e2 e3 l) =
        IfE <$> substM e1 <*> substM e2 <*> substM e3 <*> pure l

    substM (LetE decl e l) =
        LetE <$> substM decl <*> substM e <*> pure l

    substM (CallE v taus es l) =
        CallE v taus <$> substM es <*> pure l

    substM (DerefE e l) =
        DerefE <$> substM e <*> pure l

    substM (AssignE e1 e2 l) =
        AssignE <$> substM e1 <*> substM e2 <*> pure l

    substM (LowerE tau l) =
        LowerE <$> substM tau <*> pure l

    substM (WhileE e1 e2 l) =
        WhileE <$> substM e1 <*> substM e2 <*> pure l

    substM (ForE ann v tau gint e l) =
        ForE ann v <$> substM tau <*> substM gint <*> substM e <*> pure l

    substM (ArrayE es l) =
        ArrayE <$> substM es <*> pure l

    substM (IdxE e1 e2 len l) =
        IdxE <$> substM e1 <*> substM e2 <*> substM len <*> pure l

    substM (StructE s taus flds l) =
        StructE s <$> substM taus <*> substM flds <*> pure l

    substM (ProjE e fld l) =
        ProjE <$> substM e <*> pure fld <*> pure l

    substM (CastE tau e l) =
        CastE <$> substM tau <*> substM e <*> pure l

    substM (BitcastE tau e l) =
        BitcastE <$> substM tau <*> substM e <*> pure l

    substM (PrintE nl es l) =
        PrintE nl <$> substM es <*> pure l

    substM (ErrorE tau str s) =
        ErrorE <$> substM tau <*> pure str <*> pure s

    substM (ReturnE ann e l) =
        ReturnE ann <$> substM e <*> pure l

    substM (BindE wv tau e1 e2 l) =
        BindE wv <$> substM tau <*> substM e1 <*> substM e2 <*> pure l

    substM (LutE sz e) =
        LutE sz <$> substM e

    substM (GenE e gs l) =
        GenE <$> substM e <*> substM gs <*> pure l

instance Subst Type TyVar Gen where
    substM (GenG    v tau c l) = GenG v    <$> substM tau <*> pure c <*> pure l
    substM (GenRefG v tau c l) = GenRefG v <$> substM tau <*> pure c <*> pure l

instance Subst Type TyVar (Arg l) where
    substM (ExpA e)  = ExpA <$> substM e
    substM (CompA c) = CompA <$> substM c

instance Subst Type TyVar (Step l) where
    substM step@VarC{} =
        pure step

    substM (CallC l v taus es s) =
        CallC l v taus <$> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC l <$> substM decl <*> pure s

    substM (WhileC l e c s) =
        WhileC l <$> substM e <*> substM c <*> pure s

    substM (ForC l ann v tau gint c s) =
        ForC l ann v <$> substM tau <*> substM gint <*> substM c <*> pure s

    substM (LiftC l e s) =
        LiftC l <$> substM e <*> pure s

    substM (ReturnC l e s) =
        ReturnC l <$> substM e <*> pure s

    substM (BindC l wv tau s) =
        BindC l wv <$> substM tau <*> pure s

    substM (TakeC l tau s) =
        TakeC l <$> substM tau <*> pure s

    substM (TakesC l i tau s) =
        TakesC l i <$> substM tau <*> pure s

    substM (EmitC l e s) =
        EmitC l <$> substM e <*> pure s

    substM (EmitsC l e s) =
        EmitsC l <$> substM e <*> pure s

    substM (RepeatC l ann c s) =
        RepeatC l ann <$> substM c <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann <$> substM tau <*> substM c1 <*> substM c2 <*> pure s

instance Subst Type TyVar (Comp l) where
    substM comp = do
        steps' <- substM (unComp comp)
        return comp { unComp = steps' }

{------------------------------------------------------------------------------
 -
 - Expression substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Exp Var Exp where
    substM e@ConstE{} =
        return e

    substM e@(VarE v _) = do
        (theta, _) <- ask
        return $ fromMaybe e (Map.lookup v theta)

    substM (UnopE op e l) =
        UnopE op <$> substM e <*> pure l

    substM (BinopE op e1 e2 l) =
        BinopE op <$> substM e1 <*> substM e2 <*> pure l

    substM (IfE e1 e2 e3 l) =
        IfE <$> substM e1 <*> substM e2 <*> substM e3 <*> pure l

    substM (LetE decl e l) =
        freshen decl $ \decl' ->
        LetE decl' <$> substM e <*> pure l

    substM (CallE v taus es l) = do
        (theta, _) <- ask
        v' <- case Map.lookup v theta of
                Nothing          -> return v
                Just (VarE v' _) -> return v'
                Just e           ->
                    faildoc $ "Cannot substitute expression" <+>
                    ppr e <+> text "for variable" <+> ppr v
        CallE v' taus <$> substM es <*> pure l

    substM (DerefE e l) =
        DerefE <$> substM e <*> pure l

    substM (AssignE e1 e2 l) =
        AssignE <$> substM e1 <*> substM e2 <*> pure l

    substM e@LowerE{} =
        pure e

    substM (WhileE e1 e2 l) =
        WhileE <$> substM e1 <*> substM e2 <*> pure l

    substM (ForE ann v tau gint e l) = do
        gint' <- substM gint
        freshen v $ \v' ->
          ForE ann v' tau gint' <$> substM e <*> pure l

    substM (ArrayE es l) =
        ArrayE <$> substM es <*> pure l

    substM (IdxE e1 e2 len l) =
        IdxE <$> substM e1 <*> substM e2 <*> pure len <*> pure l

    substM (StructE s taus flds l) =
        StructE s taus <$> substM flds <*> pure l

    substM (ProjE e fld l) =
        ProjE <$> substM e <*> pure fld <*> pure l

    substM (CastE tau e l) =
        CastE tau <$> substM e <*> pure l

    substM (BitcastE tau e l) =
        BitcastE tau <$> substM e <*> pure l

    substM (PrintE nl es l) =
        PrintE nl <$> substM es <*> pure l

    substM e@ErrorE{} =
        pure e

    substM (ReturnE ann e l) =
        ReturnE ann <$> substM e <*> pure l

    substM (BindE wv tau e1 e2 l) = do
        e1' <- substM e1
        freshen wv $ \wv' ->
          BindE wv' tau e1' <$> substM e2 <*> pure l

    substM (LutE sz e) =
        LutE sz <$> substM e

    substM (GenE e gs l) =
        GenE <$> substM e <*> pure gs <*> pure l

instance Subst Exp Var (Arg l) where
    substM (ExpA e)  = ExpA <$> substM e
    substM (CompA c) = CompA <$> substM c

instance Subst Exp Var (Step l) where
    substM step@(VarC l v s) = do
        (theta, _) <- ask
        case Map.lookup v theta of
          Nothing -> return step
          Just e  -> return $ LiftC l e s

    substM (CallC l v taus es s) = do
        (theta, _) <- ask
        v' <- case Map.lookup v theta of
                Nothing          -> return v
                Just (VarE v' _) -> return v'
                Just e           ->
                    faildoc $ "Cannot substitute expression" <+>
                    ppr e <+> text "for variable" <+> ppr v
        CallC l v' taus <$> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM LetC{} =
        faildoc $ text "Cannot substitute in a let computation step."

    substM (WhileC l e c s) =
        WhileC l <$> substM e <*> substM c <*> pure s

    substM (ForC l ann v tau gint c s) = do
        gint' <- substM gint
        freshen v $ \v' ->
          ForC l ann v' tau gint' <$> substM c <*> pure s

    substM (LiftC l e s) =
        LiftC l <$> substM e <*> pure s

    substM (ReturnC l e s) =
        ReturnC l <$> substM e <*> pure s

    substM BindC{} =
        faildoc $ text "Cannot substitute in a bind computation step."

    substM step@TakeC{} =
        return step

    substM step@TakesC{} =
        return step

    substM (EmitC l e s) =
        EmitC l <$> substM e <*> pure s

    substM (EmitsC l e s) =
        EmitsC l <$> substM e <*> pure s

    substM (RepeatC l ann c s) =
        RepeatC l ann <$> substM c <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann tau <$> substM c1 <*> substM c2 <*> pure s

instance Subst Exp Var (Comp l) where
    substM comp = do
        steps' <- go (unComp comp)
        return comp { unComp = steps' }
      where
        go :: [Step l] -> SubstM Exp Var [Step l]
        go [] =
            return []

        go (LetC l decl s : steps) =
            freshen decl $ \decl' -> do
            steps' <- go steps
            return $ LetC l decl' s : steps'

        go (step@(BindC _ WildV _ _) : steps) = do
            steps' <- go steps
            return $ step : steps'

        go (BindC l (TameV v) tau s : steps) =
            freshen v $ \v' -> do
            steps' <- go steps
            return $ BindC l (TameV v') tau s : steps'

        go (step : steps) =
            (:) <$> substM step <*> go steps

{------------------------------------------------------------------------------
 -
 - Freshening variables
 -
 ------------------------------------------------------------------------------}

instance Freshen (Decl l) Exp Var where
    freshen decl@StructD{} k =
        k decl

    freshen (LetD decl l) k =
        freshen decl $ \decl' ->
        k $ LetD decl' l

    freshen (LetFunD v tvks vbs tau e l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetFunD v' tvks vbs' tau <$> substM e <*> pure l
        k decl'

    freshen (LetExtFunD v tvks vbs tau l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetExtFunD v' tvks vbs' tau <$> pure l
        k decl'

    freshen (LetCompD v tau comp l) k = do
        comp' <- substM comp
        freshen v $ \v' ->
          k (LetCompD v' tau comp' l)

    freshen (LetFunCompD v tvks vbs tau comp l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetFunCompD v' tvks vbs' tau <$> substM comp <*> pure l
        k decl'

instance Freshen LocalDecl Exp Var where
    freshen (LetLD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' ->
          k (LetLD v' tau e' l)

    freshen (LetRefLD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' ->
          k (LetRefLD v' tau e' l)

    freshen (LetTypeLD alpha kappa tau l) k =
        k (LetTypeLD alpha kappa tau l)

    freshen (LetViewLD v tau (IdxVW v_view e len _) l) k =
        ask (Map.lookup v_view . fst) >>= go
      where
        go Nothing = do
            e' <- substM e
            freshen v $ \v' ->
              k (LetViewLD v' tau (IdxVW v_view e' len l) l)

        go (Just e_view) = do
            e' <- substM e
            freshen v $ \v' ->
              let e_idx = IdxE e_view e' len l
              in
                local (\(theta, phi) -> (Map.insert (bVar v') e_idx theta, phi)) $
                k (LetLD v' (UnitT l) (ConstE UnitC l) l)

instance Freshen Var Exp Var where
    freshen v@(Var n) =
        freshenV (namedString n) mkV mkE v
      where
        mkV :: String -> Var
        mkV s = Var n { nameSym = intern s }

        mkE :: Var -> Exp
        mkE v = VarE v (srclocOf v)

instance Freshen (Var, Type) Exp Var where
    freshen (v, tau) k =
        freshen v $ \v' ->
        k (v', tau)

instance Freshen WildVar Exp Var where
    freshen WildV     k = k WildV
    freshen (TameV v) k = freshen v $ \v' -> k (TameV v')

{------------------------------------------------------------------------------
 -
 - Staging
 -
 ------------------------------------------------------------------------------}

instance Num Exp where
    x + y = liftNum2 Add (+) x y
    x - y = liftNum2 Sub (-) x y
    x * y = liftNum2 Mul (*) x y

    negate = liftNum Neg negate

    fromInteger i = ConstE (fromInteger i) noLoc

    abs _    = error "Num Exp: abs not implemented"
    signum _ = error "Num Exp: signum not implemented"

isZero :: Exp -> Bool
isZero (ConstE (IntC _ 0) _)   = True
isZero (ConstE (FloatC _ 0) _) = True
isZero _                       = False

isOne :: Exp -> Bool
isOne (ConstE (IntC _ 1) _)   = True
isOne (ConstE (FloatC _ 1) _) = True
isOne _                       = False

instance LiftedNum Exp Exp where
    liftNum op f e@(ConstE c _) | Just c' <- liftNum op f c =
        ConstE c' (srclocOf e)

    liftNum op _f e =
        UnopE op e (srclocOf e)

    liftNum2 Add _ e1 e2 | isZero e1 = e2
                         | isZero e2 = e1

    liftNum2 Sub _ e1 e2 | isZero e1 = negate e2
                         | isZero e2 = e1

    liftNum2 Mul _ e1 e2 | isZero e1 = e1
                         | isZero e2 = e2
                         | isOne  e1 = e2
                         | isOne  e2 = e1

    liftNum2 op f e1@(ConstE c1 _) e2@(ConstE c2 _) | Just c' <- liftNum2 op f c1 c2 =
        ConstE c' (e1 `srcspan` e2)

    -- We special-case addition here to aid tests in the simplifier.
    liftNum2 Add _f (BinopE Add e1 (ConstE (IntC ip x) sloc) sloc') (ConstE (IntC _ y) _) =
        BinopE Add e1 (ConstE (IntC ip (x+y)) sloc) sloc'

    liftNum2 op _f e1 e2 =
        BinopE op e1 e2 (e1 `srcspan` e2)

instance LiftedFloating Exp Exp where
    liftFloating op f e@(ConstE c _) | Just c' <- liftFloating op f c =
        ConstE c' (srclocOf e)

    liftFloating op _f e =
        UnopE op e (srclocOf e)

    liftFloating2 op f e1@(ConstE c1 _) e2@(ConstE c2 _) | Just c' <- liftFloating2 op f c1 c2 =
        ConstE c' (e1 `srcspan` e2)

    liftFloating2 op _f e1 e2 =
        BinopE op e1 e2 (e1 `srcspan` e2)

instance IsEq Exp where
    e1 .==. e2 = BinopE Eq e1 e2 (e1 `srcspan` e2)
    e1 ./=. e2 = BinopE Ne e1 e2 (e1 `srcspan` e2)

instance IsOrd Exp where
    e1 .<.  e2 = BinopE Lt e1 e2 (e1 `srcspan` e2)
    e1 .<=. e2 = BinopE Le e1 e2 (e1 `srcspan` e2)
    e1 .>=. e2 = BinopE Ge e1 e2 (e1 `srcspan` e2)
    e1 .>.  e2 = BinopE Gt e1 e2 (e1 `srcspan` e2)

instance IsBits Exp where
    e1 ..&..  e2 = BinopE Band e1 e2 (e1 `srcspan` e2)
    e1 ..|..  e2 = BinopE Bor e1 e2 (e1 `srcspan` e2)

    e1 `shiftL'`  e2 = BinopE LshL e1 e2 (e1 `srcspan` e2)
    e1 `shiftR'`  e2 = BinopE LshR e1 e2 (e1 `srcspan` e2)

#include "KZC/Core/Syntax-instances.hs"

instance Located BoundVar where
    locOf bv = locOf (bVar bv)

instance Located (Arg l) where
    locOf (ExpA e)  = locOf e
    locOf (CompA c) = locOf c

instance Located (Comp l) where
    locOf comp = locOf (unComp comp)

#endif /* !defined(ONLY_TYPEDEFS) */
