{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Core.Syntax
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Syntax (
    Var(..),
    WildVar(..),
    Field(..),
    Struct(..),
    TyVar(..),
    IVar(..),
    Scale(..),
    Signedness(..),
    W(..),
    BP(..),
    FP(..),
    Const(..),
    Program(..),
    Decl(..),
    LocalDecl(..),
    BoundVar(..),
    OccInfo(..),
    Exp(..),
    ToExp(..),
    UnrollAnn(..),
    InlineAnn(..),
    PipelineAnn(..),
    VectAnn(..),
    Unop(..),
    Binop(..),
    StructDef(..),
    Type(..),
    Omega(..),
    Iota(..),
    Kind(..),

    mkBoundVar,

    Arg(..),
    Step(..),
    Comp(..),
#if !defined(ONLY_TYPEDEFS)
    compLabel,
    setCompLabel,
    rewriteStepsLabel,
    compUsedLabels,
    stepLabel,
    setStepLabel,
#endif /* !defined(ONLY_TYPEDEFS) */

    isComplexStruct,

    Stm(..),

#if !defined(ONLY_TYPEDEFS)
    LiftedBool(..),
    LiftedEq(..),
    LiftedOrd(..),
    LiftedNum(..),
    LiftedIntegral(..),
    LiftedBits(..),
    LiftedCast(..),

    arrPrec,
    doPrec,
    doPrec1,
    appPrec,
    appPrec1,
    arrowPrec,
    arrowPrec1,
    tyappPrec,
    tyappPrec1
#endif /* !defined(ONLY_TYPEDEFS) */
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable(..), foldMap)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Loc
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Expr.Syntax (Var(..),
                        Field(..),
                        Struct(..),
                        TyVar(..),
                        IVar(..),
                        Scale(..),
                        Signedness(..),
                        BP(..),
                        FP(..),
                        Const(..),
                        UnrollAnn(..),
                        InlineAnn(..),
                        PipelineAnn(..),
                        VectAnn(..),
                        Unop(..),
                        Binop(..),
                        StructDef(..),
                        Type(..),
                        Omega(..),
                        Iota(..),
                        Kind(..),

                        isComplexStruct,

                        Stm(..),

#if !defined(ONLY_TYPEDEFS)
                        LiftedBool(..),
                        LiftedEq(..),
                        LiftedOrd(..),
                        LiftedNum(..),
                        LiftedIntegral(..),
                        LiftedBits(..),
                        LiftedCast(..),

                        arrPrec,
                        doPrec,
                        doPrec1,
                        appPrec,
                        appPrec1,
                        arrowPrec,
                        arrowPrec1,
                        tyappPrec,
                        tyappPrec1
#endif /* !defined(ONLY_TYPEDEFS) */
                       )
import KZC.Label
import KZC.Name
import KZC.Platform
import KZC.Pretty
import KZC.Staged
import KZC.Summary
import KZC.Uniq
import KZC.Util.Lattice
import KZC.Util.SetLike
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

data Program l = Program [Decl l] (Comp l) Type
  deriving (Eq, Ord, Read, Show)

data Decl l = LetD LocalDecl !SrcLoc
            | LetFunD BoundVar [IVar] [(Var, Type)] Type Exp !SrcLoc
            | LetExtFunD BoundVar [IVar] [(Var, Type)] Type !SrcLoc
            | LetStructD Struct [(Field, Type)] !SrcLoc
            | LetCompD BoundVar Type (Comp l) !SrcLoc
            | LetFunCompD BoundVar [IVar] [(Var, Type)] Type (Comp l) !SrcLoc
  deriving (Eq, Ord, Read, Show)

data LocalDecl = LetLD BoundVar Type Exp !SrcLoc
               | LetRefLD BoundVar Type (Maybe Exp) !SrcLoc
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
         | CallE Var [Iota] [Exp] !SrcLoc
         -- References
         | DerefE Exp !SrcLoc
         | AssignE Exp Exp !SrcLoc
         -- Loops
         | WhileE Exp Exp !SrcLoc
         | ForE UnrollAnn Var Type Exp Exp Exp !SrcLoc
         -- Arrays
         | ArrayE [Exp] !SrcLoc
         | IdxE Exp Exp (Maybe Int) !SrcLoc
         -- Structs Struct
         | StructE Struct [(Field, Exp)] !SrcLoc
         | ProjE Exp Field !SrcLoc
         -- Print
         | PrintE Bool [Exp] !SrcLoc
         | ErrorE Type String !SrcLoc
         -- Monadic operations
         | ReturnE InlineAnn Exp !SrcLoc
         | BindE WildVar Type Exp Exp !SrcLoc
         -- LUT
         | LutE Exp
  deriving (Eq, Ord, Read, Show)

class ToExp a where
    toExp :: a -> Exp

-- | An argument to a call to a computation function. Arguments may be
-- expressions or computations.
data Arg l = ExpA  Exp
           | CompA (Comp l)
  deriving (Eq, Ord, Read, Show)

data Step l = VarC l Var !SrcLoc
            | CallC l Var [Iota] [Arg l] !SrcLoc
            | IfC l Exp (Comp l) (Comp l) !SrcLoc
            | LetC l LocalDecl !SrcLoc

            | WhileC l Exp (Comp l) !SrcLoc
            | ForC l UnrollAnn Var Type Exp Exp (Comp l) !SrcLoc

            -- | Lift an expression of type
            -- @forall s a b . ST (C tau) s a b@ into the monad. 'LiftC' and
            -- 'ReturnC' differ only for the purpose of type checking.
            | LiftC l Exp !SrcLoc
            | ReturnC l Exp !SrcLoc
            | BindC l WildVar Type !SrcLoc

            | TakeC l Type !SrcLoc
            | TakesC l Int Type !SrcLoc
            | EmitC l Exp !SrcLoc
            | EmitsC l Exp !SrcLoc
            | RepeatC l VectAnn (Comp l) !SrcLoc
            | ParC PipelineAnn Type (Comp l) (Comp l) !SrcLoc

            -- | This is a special "administrative" step that we use to indicate
            -- a jump to a loop header.
            | LoopC l
  deriving (Eq, Ord, Read, Show)

newtype Comp l = Comp { unComp :: [Step l] }
  deriving (Eq, Ord, Read, Show, Monoid)

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

instance BoundedLattice OccInfo where
    bot = Dead
    top = Many

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
compLabel (Comp [])       = fail "compLabel: empty computation"
compLabel (Comp (step:_)) = stepLabel step

setCompLabel :: l -> Comp l -> Comp l
setCompLabel _ comp@(Comp [])      = comp
setCompLabel l (Comp (step:steps)) = Comp (setStepLabel l step:steps)

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
    go []                           = Set.empty
    go (IfC _ _ l r _:steps)        = compUsedLabels l <> compUsedLabels r <> go steps
    go (WhileC _ _ c _:steps)       = compUsedLabels c <> go steps
    go (ForC _ _ _ _ _ _ c _:steps) = compUsedLabels c <> go steps
    go (RepeatC _ _ c _:steps)      = compUsedLabels c <> go steps
    go (ParC _ _ l r _:steps)       = compUsedLabels l <> compUsedLabels r <> go steps
    go (_:steps)                    = go steps

stepLabel :: Monad m => Step l -> m l
stepLabel (VarC l _ _)           = return l
stepLabel (CallC l _ _ _ _)      = return l
stepLabel (IfC l _ _ _ _)        = return l
stepLabel (LetC l _ _)           = return l
stepLabel (WhileC l _ _ _)       = return l
stepLabel (ForC l _ _ _ _ _ _ _) = return l
stepLabel (LiftC l _ _)          = return l
stepLabel (ReturnC l _ _)        = return l
stepLabel (BindC l _ _ _)        = return l
stepLabel (TakeC l _ _)          = return l
stepLabel (TakesC l _ _ _)       = return l
stepLabel (EmitC l _ _)          = return l
stepLabel (EmitsC l _ _)         = return l
stepLabel (RepeatC l _ _ _)      = return l
stepLabel (ParC _ _ _ right _)   = compLabel right
stepLabel (LoopC l)              = return l

setStepLabel :: l -> Step l -> Step l
setStepLabel l (VarC _ v s)                 = VarC l v s
setStepLabel l (CallC _ v iotas es s)       = CallC l v iotas es s
setStepLabel l (IfC _ e c1 c2 s)            = IfC l e c1 c2 s
setStepLabel l (LetC _ decl s)              = LetC l decl s
setStepLabel l (WhileC _ e c s)             = WhileC l e c s
setStepLabel l (ForC _ ann v tau e1 e2 c s) = ForC l ann v tau e1 e2 c s
setStepLabel l (LiftC _ e s)                = LiftC l e s
setStepLabel l (ReturnC _ e s)              = ReturnC l e s
setStepLabel l (BindC _ wv tau s)           = BindC l wv tau s
setStepLabel l (TakeC _ tau s)              = TakeC l tau s
setStepLabel l (TakesC _ i tau s)           = TakesC l i tau s
setStepLabel l (EmitC _ e s)                = EmitC l e s
setStepLabel l (EmitsC _ e s)               = EmitsC l e s
setStepLabel l (RepeatC _ ann c s)          = RepeatC l ann c s
setStepLabel l (ParC ann tau left right s)  = ParC ann tau left (setCompLabel l right) s
setStepLabel _ step@LoopC{}                 = step

{------------------------------------------------------------------------------
 -
 - Statements
 -
 ------------------------------------------------------------------------------}

expToStms :: Exp -> [Stm BoundVar Exp]
expToStms (ReturnE ann e l)             = [ReturnS ann e l]
expToStms (BindE WildV tau e1 e2 l)     = BindS Nothing tau e1 l : expToStms e2
expToStms (BindE (TameV v) tau e1 e2 l) = BindS (Just v) tau e1 l : expToStms e2
expToStms e                             = [ExpS e (srclocOf e)]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary (Decl l) where
    summary (LetD decl _)             = summary decl
    summary (LetFunD v _ _ _ _ _)     = text "definition of" <+> ppr v
    summary (LetExtFunD v _ _ _ _)    = text "definition of" <+> ppr v
    summary (LetStructD s _ _)        = text "definition of" <+> ppr s
    summary (LetCompD v _ _ _)        = text "definition of" <+> ppr v
    summary (LetFunCompD v _ _ _ _ _) = text "definition of" <+> ppr v

instance Summary LocalDecl where
    summary (LetLD v _ _ _)    = text "definition of" <+> ppr v
    summary (LetRefLD v _ _ _) = text "definition of" <+> ppr v

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

instance IsLabel l => Pretty (Program l) where
    ppr (Program decls comp tau) =
        ppr decls </>
        ppr (LetCompD "main" tau comp noLoc)

instance IsLabel l => Pretty (Decl l) where
    pprPrec p (LetD decl _) =
        pprPrec p decl

    pprPrec p (LetFunD f ibs vbs tau e _) =
        parensIf (p > appPrec) $
        text "letfun" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 (text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau) <+>
        nest 2 (text "=" </> ppr e)

    pprPrec p (LetExtFunD f ibs vbs tau _) =
        parensIf (p > appPrec) $
        text "letextfun" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 (text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau)

    pprPrec p (LetStructD s flds _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> pprStruct flds))
      where
        lhs = text "struct" <+> ppr s

    pprPrec p (LetCompD v tau ccomp _) =
        parensIf (p > appPrec) $
        nest 2 (lhs <+/> text "=" </> ppr ccomp)
      where
        lhs = text "letcomp" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetFunCompD f ibs vbs tau e _) =
        parensIf (p > appPrec) $
        text "letfuncomp" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 (text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau) <+>
        nest 2 (text "=" </> ppr e)

    pprList decls = stack (map ppr decls)

instance Pretty LocalDecl where
    pprPrec p (LetLD v tau e _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> ppr e))
      where
        lhs = text "let" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetRefLD v tau Nothing _) =
        parensIf (p > appPrec) $
        text "letref" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetRefLD v tau (Just e) _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> ppr e))
      where
        lhs = text "letref" <+> ppr v <+> text ":" <+> ppr tau

    pprList decls = stack (map ppr decls)

instance Pretty Exp where
    pprPrec _ (ConstE c _) =
        ppr c

    pprPrec _ (VarE v _) =
        ppr v

    pprPrec p (UnopE op@Cast{} e _) =
        parensIf (p > precOf op) $
        ppr op <+> pprPrec (precOf op) e

    pprPrec p (UnopE op e _) =
        parensIf (p > precOf op) $
        ppr op <> pprPrec (precOf op) e

    pprPrec p (BinopE op e1 e2 _) =
        infixop p op e1 e2

    pprPrec p (IfE e1 e2 e3 _) =
        parensIf (p >= appPrec) $
        text "if"   <+> pprPrec appPrec1 e1 <+/>
        text "then" <+> pprPrec appPrec1 e2 <+/>
        text "else" <+> pprPrec appPrec1 e3

    pprPrec p (LetE decl body _) =
        parensIf (p > appPrec) $
        case body of
          LetE{} -> ppr decl <+> text "in" </>
                    pprPrec doPrec1 body
          _      -> ppr decl </>
                    nest 2 (text "in" </> pprPrec doPrec1 body)

    pprPrec _ (CallE f is es _) =
        ppr f <> parens (commasep (map ppr is ++ map ppr es))

    pprPrec _ (DerefE v _) =
        text "!" <> pprPrec appPrec1 v

    pprPrec p (AssignE v e _) =
        parensIf (p > appPrec) $
        group $
        nest 4 $ ppr v <+> text ":=" <+/> pprPrec appPrec1 e

    pprPrec _ (WhileE e1 e2 _) =
        nest 2 $
        text "while" <+>
        group (pprPrec appPrec1 e1) <+/>
        pprBody e2

    pprPrec _ (ForE ann v tau e1 e2 e3 _) =
        nest 2 $
        ppr ann <+> text "for" <+>
        group (parens (ppr v <+> colon <+> ppr tau) <+>
               text "in" <+>
               brackets (commasep [ppr e1, ppr e2])) <+/>
        pprBody e3

    pprPrec _ (ArrayE es _) =
        text "arr" <+> embrace commasep (map ppr es)

    pprPrec _ (IdxE e1 e2 Nothing _) =
        pprPrec appPrec1 e1 <> brackets (ppr e2)

    pprPrec _ (IdxE e1 e2 (Just i) _) =
        pprPrec appPrec1 e1 <> brackets (commasep [ppr e2, ppr i])

    pprPrec _ (StructE s fields _) =
        ppr s <+> pprStruct fields

    pprPrec _ (ProjE e f _) =
        pprPrec appPrec1 e <> text "." <> ppr f

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

    pprPrec p (LutE e) =
        parensIf (p > appPrec) $
        text "lut" <+> pprPrec appPrec1 e

pprBody :: Exp -> Doc
pprBody e =
    case expToStms e of
      [_]  -> line <> align (ppr e)
      stms -> space <> semiEmbraceWrap (map ppr stms)

pprFunParams :: [IVar] -> [(Var, Type)] -> Doc
pprFunParams = go
  where
    go :: [IVar] -> [(Var, Type)] -> Doc
    go []    []   = empty
    go []    [vb] = pprArg vb
    go []    vbs  = sep (map pprArg vbs)
    go iotas vbs  = sep (map ppr iotas ++ map pprArg vbs)

    pprArg :: (Var, Type) -> Doc
    pprArg (v, tau) = parens $ ppr v <+> text ":" <+> ppr tau

instance IsLabel l => Pretty (Arg l) where
    pprPrec p (ExpA e)  = pprPrec p e
    pprPrec p (CompA c) = pprPrec p c

instance IsLabel l => Pretty (Step l) where
    ppr step = ppr (Comp [step])

    pprList steps = ppr (Comp steps)

instance IsLabel l => Pretty (Comp l) where
    pprPrec p comp =
        case pprComp comp of
          [stm] -> parensIf (p > appPrec) $ align stm
          stms  -> semiEmbraceWrap stms

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

    pprSteps (CallC _ f is es _ : k) =
        pprBind k $
        ppr f <> parens (commasep (map ppr is ++ map ppr es))

    pprSteps (IfC _ e1 e2 e3 _ : k) =
        pprBind k $
        text "if"   <+> pprPrec appPrec1 e1 <+/>
        text "then" <+> pprPrec appPrec1 e2 <+/>
        text "else" <+> pprPrec appPrec1 e3

    pprSteps (LetC _ decl _ : k) =
        pprBind k $
        ppr decl

    pprSteps (WhileC _ e c _ : k) =
        pprBind k $
        text "while" <+>
        group (pprPrec appPrec1 e) <+>
        ppr c

    pprSteps (ForC _ ann v tau e1 e2 c _ : k) =
        pprBind k $
        ppr ann <+> text "for" <+>
        group (parens (ppr v <+> colon <+> ppr tau) <+>
               text "in" <+>
               brackets (commasep [ppr e1, ppr e2])) <+/>
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
        pprPrec arrPrec e1 </>
        ppr ann <> text "@" <> pprPrec appPrec1 tau </>
        pprPrec arrPrec e2

    pprSteps (LoopC l : _) =
        [text "loop" <+> ppr l]

    pprBind :: [Step l] -> Doc -> [Doc]
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
    fvs (LetD decl _)               = fvs decl
    fvs (LetFunD v _ vbs _ e _)     = delete (bVar v) (fvs e) <\\> fromList (map fst vbs)
    fvs LetExtFunD{}                = mempty
    fvs LetStructD{}                = mempty
    fvs (LetCompD v _ ccomp _)      = delete (bVar v) (fvs ccomp)
    fvs (LetFunCompD v _ vbs _ e _) = delete (bVar v) (fvs e) <\\> fromList (map fst vbs)

instance Binders (Decl l) Var where
    binders (LetD decl _)             = binders decl
    binders (LetFunD v _ _ _ _ _)     = singleton (bVar v)
    binders (LetExtFunD v _ _ _ _)    = singleton (bVar v)
    binders LetStructD{}              = mempty
    binders (LetCompD v _ _ _)        = singleton (bVar v)
    binders (LetFunCompD v _ _ _ _ _) = singleton (bVar v)

instance Fvs LocalDecl Var where
    fvs (LetLD v _ e _)    = delete (bVar v) (fvs e)
    fvs (LetRefLD v _ e _) = delete (bVar v) (fvs e)

instance Binders LocalDecl Var where
    binders (LetLD v _ _ _)    = singleton (bVar v)
    binders (LetRefLD v _ _ _) = singleton (bVar v)

instance Fvs Exp Var where
    fvs ConstE{}                    = mempty
    fvs (VarE v _)                  = singleton v
    fvs (UnopE _ e _)               = fvs e
    fvs (BinopE _ e1 e2 _)          = fvs e1 <> fvs e2
    fvs (IfE e1 e2 e3 _)            = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetE decl body _)          = fvs decl <> (fvs body <\\> binders decl)
    fvs (CallE f _ es _)            = singleton f <> fvs es
    fvs (DerefE e _)                = fvs e
    fvs (AssignE e1 e2 _)           = fvs e1 <> fvs e2
    fvs (WhileE e1 e2 _)            = fvs e1 <> fvs e2
    fvs (ForE _ v _ e1 e2 e3 _)     = fvs e1 <> fvs e2 <> delete v (fvs e3)
    fvs (ArrayE es _)               = fvs es
    fvs (IdxE e1 e2 _ _)            = fvs e1 <> fvs e2
    fvs (StructE _ flds _)          = fvs (map snd flds)
    fvs (ProjE e _ _)               = fvs e
    fvs (PrintE _ es _)             = fvs es
    fvs ErrorE{}                    = mempty
    fvs (ReturnE _ e _)             = fvs e
    fvs (BindE wv _ e1 e2 _)        = fvs e1 <> (fvs e2 <\\> binders wv)
    fvs (LutE e)                    = fvs e

instance Fvs (Arg l) Var where
    fvs (ExpA e)  = fvs e
    fvs (CompA c) = fvs c

instance Fvs (Step l) Var where
    fvs (VarC _ v _)             = singleton v
    fvs (CallC _ f _ es _)       = singleton f <> fvs es
    fvs (IfC _ e1 e2 e3 _)       = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetC _ decl _)          = fvs decl
    fvs (WhileC _ e c _)         = fvs e <> fvs c
    fvs (ForC _ _ v _ e1 e2 c _) = fvs e1 <> fvs e2 <> delete v (fvs c)
    fvs (LiftC _ e _)            = fvs e
    fvs (ReturnC _ e _)          = fvs e
    fvs BindC{}                  = mempty
    fvs TakeC{}                  = mempty
    fvs TakesC{}                 = mempty
    fvs (EmitC _ e _)            = fvs e
    fvs (EmitsC _ e _)           = fvs e
    fvs (RepeatC _ _ c _)        = fvs c
    fvs (ParC _ _ e1 e2 _)       = fvs e1 <> fvs e2
    fvs LoopC{}                  = mempty

instance Fvs (Comp l) Var where
    fvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                          = mempty
        go (BindC _ wv _ _ : k)        = go k <\\> binders wv
        go (LetC _ decl _ : k)         = fvs decl <> (go k <\\> binders decl)
        go (step : k)                  = fvs step <> go k

instance Fvs Exp v => Fvs [Exp] v where
    fvs = foldMap fvs

instance Fvs (Arg l) v => Fvs [Arg l] v where
    fvs = foldMap fvs

instance Fvs (Comp l) v => Fvs [Step l] v where
    fvs steps = fvs (Comp steps)

{------------------------------------------------------------------------------
 -
 - All variables
 -
 ------------------------------------------------------------------------------}

instance HasVars WildVar Var where
    allVars WildV     = mempty
    allVars (TameV v) = singleton (bVar v)

instance HasVars (Decl l) Var where
    allVars (LetD decl _)               = allVars decl
    allVars (LetFunD v _ vbs _ e _)     = singleton (bVar v) <> fromList (map fst vbs) <> allVars e
    allVars (LetExtFunD v _ vbs _ _)    = singleton (bVar v) <> fromList (map fst vbs)
    allVars LetStructD{}                = mempty
    allVars (LetCompD v _ ccomp _)      = singleton (bVar v) <> allVars ccomp
    allVars (LetFunCompD v _ vbs _ e _) = singleton (bVar v) <> fromList (map fst vbs) <> allVars e

instance HasVars LocalDecl Var where
    allVars (LetLD v _ e _)    = singleton (bVar v) <> allVars e
    allVars (LetRefLD v _ e _) = singleton (bVar v) <> allVars e

instance HasVars Exp Var where
    allVars ConstE{}                    = mempty
    allVars (VarE v _)                  = singleton v
    allVars (UnopE _ e _)               = allVars e
    allVars (BinopE _ e1 e2 _)          = allVars e1 <> allVars e2
    allVars (IfE e1 e2 e3 _)            = allVars e1 <> allVars e2 <> allVars e3
    allVars (LetE decl body _)          = allVars decl <> allVars decl <> allVars body
    allVars (CallE f _ es _)            = singleton f <> allVars es
    allVars (DerefE e _)                = allVars e
    allVars (AssignE e1 e2 _)           = allVars e1 <> allVars e2
    allVars (WhileE e1 e2 _)            = allVars e1 <> allVars e2
    allVars (ForE _ v _ e1 e2 e3 _)     = singleton v <> allVars e1 <> allVars e2 <> allVars e3
    allVars (ArrayE es _)               = allVars es
    allVars (IdxE e1 e2 _ _)            = allVars e1 <> allVars e2
    allVars (StructE _ flds _)          = allVars (map snd flds)
    allVars (ProjE e _ _)               = allVars e
    allVars (PrintE _ es _)             = allVars es
    allVars ErrorE{}                    = mempty
    allVars (ReturnE _ e _)             = allVars e
    allVars (BindE wv _ e1 e2 _)        = allVars wv <> allVars e1 <> allVars e2
    allVars (LutE e)                    = allVars e

instance HasVars (Arg l) Var where
    allVars (ExpA e)  = allVars e
    allVars (CompA c) = allVars c

instance HasVars (Step l) Var where
    allVars (VarC _ v _)             = singleton v
    allVars (CallC _ f _ es _)       = singleton f <> allVars es
    allVars (IfC _ e1 e2 e3 _)       = allVars e1 <> allVars e2 <> allVars e3
    allVars (LetC _ decl _)          = allVars decl
    allVars (WhileC _ e c _)         = allVars e <> allVars c
    allVars (ForC _ _ v _ e1 e2 c _) = singleton v <> allVars e1 <> allVars e2 <> allVars c
    allVars (LiftC _ e _)            = allVars e
    allVars (ReturnC _ e _)          = allVars e
    allVars BindC{}                  = mempty
    allVars TakeC{}                  = mempty
    allVars TakesC{}                 = mempty
    allVars (EmitC _ e _)            = allVars e
    allVars (EmitsC _ e _)           = allVars e
    allVars (RepeatC _ _ c _)        = allVars c
    allVars (ParC _ _ e1 e2 _)       = allVars e1 <> allVars e2
    allVars LoopC{}                  = mempty

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

    substM (CallC l v iotas es s) =
        CallC <$> substM l <*> pure v <*> pure iotas <*> pure es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC <$> substM l <*> pure e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC <$> substM l <*> pure decl <*> pure s

    substM (WhileC l e c s) =
        WhileC <$> substM l <*> pure e <*> substM c <*> pure s

    substM (ForC l ann v tau e1 e2 c s) =
        ForC <$> substM l <*> pure ann <*> pure v <*> pure tau <*> pure e1 <*> pure e2 <*> substM c <*> pure s

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

    substM step@LoopC{} =
        return step

instance (IsLabel l, Fvs l l, Subst l l l) => Subst l l (Comp l) where
    substM comp = Comp <$> substM (unComp comp)

{------------------------------------------------------------------------------
 -
 - Iota substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Iota IVar LocalDecl where
    substM (LetLD v tau e s) =
        LetLD v <$> substM tau <*> substM e <*> pure s

    substM (LetRefLD v tau e s) =
        LetRefLD v <$> substM tau <*> substM e <*> pure s

instance Subst Iota IVar Exp where
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

    substM (CallE v iotas es l) =
        CallE v <$> substM iotas <*> substM es <*> pure l

    substM (DerefE e l) =
        DerefE <$> substM e <*> pure l

    substM (AssignE e1 e2 l) =
        AssignE <$> substM e1 <*> substM e2 <*> pure l

    substM (WhileE e1 e2 l) =
        WhileE <$> substM e1 <*> substM e2 <*> pure l

    substM (ForE ann v tau e1 e2 e3 l) =
        ForE ann v <$> substM tau <*> substM e1 <*> substM e2 <*> substM e3 <*> pure l

    substM (ArrayE es l) =
        ArrayE <$> substM es <*> pure l

    substM (IdxE e1 e2 i l) =
        IdxE <$> substM e1 <*> substM e2 <*> pure i <*> pure l

    substM (StructE s flds l) =
        StructE s <$> substM flds <*> pure l

    substM (ProjE e fld l) =
        ProjE <$> substM e <*> pure fld <*> pure l

    substM (PrintE nl es l) =
        PrintE nl <$> substM es <*> pure l

    substM (ErrorE tau str s) =
        ErrorE <$> substM tau <*> pure str <*> pure s

    substM (ReturnE ann e l) =
        ReturnE ann <$> substM e <*> pure l

    substM (BindE wv tau e1 e2 l) =
        BindE wv <$> substM tau <*> substM e1 <*> substM e2 <*> pure l

    substM (LutE e) =
        LutE <$> substM e

instance Subst Iota IVar (Arg l) where
    substM (ExpA e)  = ExpA <$> substM e
    substM (CompA c) = CompA <$> substM c

instance Subst Iota IVar (Step l) where
    substM step@VarC{} =
        pure step

    substM (CallC l v iotas es s) =
        CallC l v <$> substM iotas <*> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC l <$> substM decl <*> pure s

    substM (WhileC l e c s) =
        WhileC l <$> substM e <*> substM c <*> pure s

    substM (ForC l ann v tau e1 e2 c s) =
        ForC l ann v <$> substM tau <*> substM e1 <*> substM e2 <*> substM c <*> pure s

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

    substM step@LoopC{} =
        return step

instance Subst Iota IVar (Comp l) where
    substM (Comp steps) = Comp <$> substM steps

{------------------------------------------------------------------------------
 -
 - Type substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Type TyVar LocalDecl where
    substM (LetLD v tau e l) =
        LetLD v <$> substM tau <*> substM e <*> pure l

    substM (LetRefLD v tau e l) =
        LetRefLD v <$> substM tau <*> substM e <*> pure l

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

    substM (CallE v iotas es l) =
        CallE v iotas <$> substM es <*> pure l

    substM (DerefE e l) =
        DerefE <$> substM e <*> pure l

    substM (AssignE e1 e2 l) =
        AssignE <$> substM e1 <*> substM e2 <*> pure l

    substM (WhileE e1 e2 l) =
        WhileE <$> substM e1 <*> substM e2 <*> pure l

    substM (ForE ann v tau e1 e2 e3 l) =
        ForE ann v <$> substM tau <*> substM e1 <*> substM e2 <*> substM e3 <*> pure l

    substM (ArrayE es l) =
        ArrayE <$> substM es <*> pure l

    substM (IdxE e1 e2 i l) =
        IdxE <$> substM e1 <*> substM e2 <*> pure i <*> pure l

    substM (StructE s flds l) =
        StructE s <$> substM flds <*> pure l

    substM (ProjE e fld l) =
        ProjE <$> substM e <*> pure fld <*> pure l

    substM (PrintE nl es l) =
        PrintE nl <$> substM es <*> pure l

    substM (ErrorE tau str s) =
        ErrorE <$> substM tau <*> pure str <*> pure s

    substM (ReturnE ann e l) =
        ReturnE ann <$> substM e <*> pure l

    substM (BindE wv tau e1 e2 l) =
        BindE wv <$> substM tau <*> substM e1 <*> substM e2 <*> pure l

    substM (LutE e) =
        LutE <$> substM e

instance Subst Type TyVar (Arg l) where
    substM (ExpA e)  = ExpA <$> substM e
    substM (CompA c) = CompA <$> substM c

instance Subst Type TyVar (Step l) where
    substM step@VarC{} =
        pure step

    substM (CallC l v iotas es s) =
        CallC l v iotas <$> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC l <$> substM decl <*> pure s

    substM (WhileC l e c s) =
        WhileC l <$> substM e <*> substM c <*> pure s

    substM (ForC l ann v tau e1 e2 c s) =
        ForC l ann v <$> substM tau <*> substM e1 <*> substM e2 <*> substM c <*> pure s

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

    substM step@LoopC{} =
        return step

instance Subst Type TyVar (Comp l) where
    substM (Comp steps) = Comp <$> substM steps

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

    substM (CallE v iotas es l) = do
        (theta, _) <- ask
        v' <- case Map.lookup v theta of
                Nothing          -> return v
                Just (VarE v' _) -> return v'
                Just e           ->
                    faildoc $ "Cannot substitute expression" <+>
                    ppr e <+> text "for variable" <+> ppr v
        CallE v' iotas <$> substM es <*> pure l

    substM (DerefE e l) =
        DerefE <$> substM e <*> pure l

    substM (AssignE e1 e2 l) =
        AssignE <$> substM e1 <*> substM e2 <*> pure l

    substM (WhileE e1 e2 l) =
        WhileE <$> substM e1 <*> substM e2 <*> pure l

    substM (ForE ann v tau e1 e2 e3 l) = do
        e1' <- substM e1
        e2' <- substM e2
        freshen v $ \v' ->
          ForE ann v' tau e1' e2' <$> substM e3 <*> pure l

    substM (ArrayE es l) =
        ArrayE <$> substM es <*> pure l

    substM (IdxE e1 e2 i l) =
        IdxE <$> substM e1 <*> substM e2 <*> pure i <*> pure l

    substM (StructE s flds l) =
        StructE s <$> substM flds <*> pure l

    substM (ProjE e fld l) =
        ProjE <$> substM e <*> pure fld <*> pure l

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

    substM (LutE e) =
        LutE <$> substM e

instance Subst Exp Var (Arg l) where
    substM (ExpA e)  = ExpA <$> substM e
    substM (CompA c) = CompA <$> substM c

instance Subst Exp Var (Step l) where
    substM step@(VarC l v s) = do
        (theta, _) <- ask
        case Map.lookup v theta of
          Nothing -> return step
          Just e  -> return $ LiftC l e s

    substM (CallC l v iotas es s) = do
        (theta, _) <- ask
        v' <- case Map.lookup v theta of
                Nothing          -> return v
                Just (VarE v' _) -> return v'
                Just e           ->
                    faildoc $ "Cannot substitute expression" <+>
                    ppr e <+> text "for variable" <+> ppr v
        CallC l v' iotas <$> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM LetC{} =
        faildoc $ text "Cannot substitute in a let computation step."

    substM (WhileC l e c s) =
        WhileC l <$> substM e <*> substM c <*> pure s

    substM (ForC l ann v tau e1 e2 c s) = do
        e1' <- substM e1
        e2' <- substM e2
        freshen v $ \v' ->
          ForC l ann v' tau e1' e2' <$> substM c <*> pure s

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

    substM step@LoopC{} =
        return step

instance Subst Exp Var (Comp l) where
    substM (Comp steps) =
        Comp <$> go steps
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
 - Freshening I-variables
 -
 ------------------------------------------------------------------------------}

instance Freshen (Decl l) Iota IVar where
    freshen (LetD decl l) k =
        freshen decl $ \decl' ->
        k $ LetD decl' l

    freshen (LetFunD v ibs vbs tau e l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetFunD v ibs' <$> substM vbs <*> substM tau <*> substM e <*> pure l
        k decl'

    freshen (LetExtFunD v ibs vbs tau l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetExtFunD v ibs' <$> substM vbs <*> substM tau <*> pure l
        k decl'

    freshen decl@LetStructD{} k =
        k decl

    freshen (LetCompD v tau comp l) k = do
        decl' <- LetCompD v <$> substM tau <*> substM comp <*> pure l
        k decl'

    freshen (LetFunCompD v ibs vbs tau comp l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetFunCompD v ibs' vbs <$> substM tau <*> substM comp <*> pure l
        k decl'

instance Freshen LocalDecl Iota IVar where
    freshen (LetLD v tau e l) k = do
        decl' <- LetLD v <$> substM tau <*> substM e <*> pure l
        k decl'

    freshen (LetRefLD v tau e l) k = do
        decl' <- LetRefLD v <$> substM tau <*> substM e <*> pure l
        k decl'

{------------------------------------------------------------------------------
 -
 - Freshening variables
 -
 ------------------------------------------------------------------------------}

instance Freshen (Decl l) Exp Var where
    freshen (LetD decl l) k =
        freshen decl $ \decl' ->
        k $ LetD decl' l

    freshen (LetFunD v ibs vbs tau e l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetFunD v' ibs vbs' tau <$> substM e <*> pure l
        k decl'

    freshen (LetExtFunD v ibs vbs tau l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetExtFunD v' ibs vbs' tau <$> pure l
        k decl'

    freshen decl@LetStructD{} k =
        k decl

    freshen (LetCompD v tau comp l) k = do
        comp' <- substM comp
        freshen v $ \v' ->
          k (LetCompD v' tau comp' l)

    freshen (LetFunCompD v ibs vbs tau comp l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetFunCompD v' ibs vbs' tau <$> substM comp <*> pure l
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
isZero (ConstE (FixC _ _ _ _ 0) _) = True
isZero (ConstE (FloatC _ 0) _)     = True
isZero _                           = False

isOne :: Exp -> Bool
isOne (ConstE (FixC I _ _ (BP 0) 1) _) = True
isOne (ConstE (FloatC _ 1) _)          = True
isOne _                                = False

instance LiftedNum Exp Exp where
    liftNum op f e@(ConstE c _) | Just c' <- liftNum op f c =
        ConstE c' (srclocOf e)

    liftNum op _f e =
        UnopE op e (srclocOf e)

    liftNum2 Add _ e1 e2 | isZero e1 = e2
                         | isZero e2 = e1

    liftNum2 Sub _ e1 e2 | isZero e1 = negate e2
                         | isZero e2 = e1

    liftNum2 Mul _ e1 e2 | isZero e1 = 0
                         | isZero e2 = 0
                         | isOne  e1 = e2
                         | isOne  e2 = e1

    liftNum2 op f e1@(ConstE c1 _) e2@(ConstE c2 _) | Just c' <- liftNum2 op f c1 c2 =
        ConstE c' (e1 `srcspan` e2)

    liftNum2 op _f e1 e2 =
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
    locOf (Comp steps) = locOf steps

#endif /* !defined(ONLY_TYPEDEFS) */
