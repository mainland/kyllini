{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Auto.Syntax
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Auto.Syntax (
    Var(..),
    Field(..),
    Struct(..),
    TyVar(..),
    IVar(..),
    W(..),
    Signedness(..),
    Const(..),
    Program(..),
    Decl(..),
    LocalDecl(..),
    Exp(..),
    UnrollAnn(..),
    InlineAnn(..),
    PipelineAnn(..),
    VectAnn(..),
    BindVar(..),
    Unop(..),
    Binop(..),
    StructDef(..),
    Type(..),
    Omega(..),
    Iota(..),
    Kind(..),

    Step(..),
    Comp(..),
    IsLabel,
#if !defined(ONLY_TYPEDEFS)
    compLabel,
    compUsedLabels,
    stepLabel,
    setStepLabel,
#endif /* !defined(ONLY_TYPEDEFS) */

    Label(..),
    LProgram,
    LDecl,
    LComp,

    isComplexStruct,

    Stm(..)
  ) where

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.Reader
import Data.Foldable (Foldable(..), foldMap)
import Data.Loc
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Data.Symbol
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Core.Syntax (Var(..),
                        Field(..),
                        Struct(..),
                        TyVar(..),
                        IVar(..),
                        W(..),
                        Signedness(..),
                        Const(..),
                        UnrollAnn(..),
                        InlineAnn(..),
                        PipelineAnn(..),
                        VectAnn(..),
                        BindVar(..),
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
                        arrPrec,
                        doPrec1,
                        appPrec,
                        appPrec1,
                        tyappPrec1
#endif /* !defined(ONLY_TYPEDEFS) */
                       )
import KZC.Name
import KZC.Platform
import KZC.Pretty
import KZC.Staged
import KZC.Summary
import KZC.Util.SetLike
import KZC.Vars

data Program l = Program [Decl l] (Comp l) Type

data Decl l = LetD Var Type Exp !SrcLoc
            | LetFunD Var [IVar] [(Var, Type)] Type Exp !SrcLoc
            | LetExtFunD Var [IVar] [(Var, Type)] Type !SrcLoc
            | LetRefD Var Type (Maybe Exp) !SrcLoc
            | LetStructD Struct [(Field, Type)] !SrcLoc
            | LetCompD Var Type (Comp l) !SrcLoc
            | LetFunCompD Var [IVar] [(Var, Type)] Type (Comp l) !SrcLoc

data LocalDecl = LetLD Var Type Exp !SrcLoc
               | LetRefLD Var Type (Maybe Exp) !SrcLoc
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
         | BindE BindVar Exp Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Step l = VarC l Var !SrcLoc
            | CallC l Var [Iota] [Exp] !SrcLoc
            | IfC l Exp (Comp l) (Comp l) !SrcLoc
            | LetC l LocalDecl !SrcLoc

            -- | Lift an expression of type
            -- @forall s a b . ST (C tau) s a b@ into the monad. 'LiftC' and
            -- 'ReturnC' differ only for the purpose of type checking.
            | LiftC l Exp !SrcLoc
            -- | A return. The continuation receives the /compiled/
            -- representation of the expression.
            | ReturnC l Exp !SrcLoc
            | BindC l BindVar !SrcLoc

            | GotoC l !SrcLoc
            -- | A goto that is part of a repeat construct. This is
            -- separate from 'GotoC' only for the purpose of type checking.
            | RepeatC l !SrcLoc

            | TakeC l Type !SrcLoc
            | TakesC l Int Type !SrcLoc
            | EmitC l Exp !SrcLoc
            | EmitsC l Exp !SrcLoc
            | ParC PipelineAnn Type (Comp l) (Comp l) !SrcLoc
  deriving (Eq, Ord, Read, Show)

newtype Comp l = Comp { unComp :: [Step l] }
  deriving (Eq, Ord, Read, Show, Monoid)

newtype Label = Label { unLabel :: Symbol }
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = Label (fromString s)

instance C.ToIdent Label where
    toIdent lbl = C.Id (unintern (unLabel lbl))

type LProgram = Program Label

type LDecl = Decl Label

type LComp = Comp Label

class (Ord l, Pretty l) => IsLabel l where

#if !defined(ONLY_TYPEDEFS)
{------------------------------------------------------------------------------
 -
 - Computation labels
 -
 ------------------------------------------------------------------------------}
compLabel :: Monad m => Comp l -> m l
compLabel (Comp [])       = fail "compLabel: empty computation"
compLabel (Comp (step:_)) = stepLabel step

compUsedLabels :: forall l . Ord l => Comp l -> Set l
compUsedLabels comp =
    go (unComp comp)
  where
    go :: [Step l] -> Set l
    go []                     = Set.empty
    go (IfC _ _ l r _:steps)  = compUsedLabels l <> compUsedLabels r <> go steps
    go (ParC _ _ l r _:steps) = compUsedLabels l <> compUsedLabels r <> go steps
    go (GotoC l _:steps)      = Set.insert l (go steps)
    go (RepeatC l _:steps)    = Set.insert l (go steps)
    go (_:steps)              = go steps

stepLabel :: Monad m => Step l -> m l
stepLabel (VarC l _ _)         = return l
stepLabel (CallC l _ _ _ _)    = return l
stepLabel (IfC l _ _ _ _)      = return l
stepLabel (LetC l _ _)         = return l
stepLabel (LiftC l _ _)        = return l
stepLabel (ReturnC l _ _)      = return l
stepLabel (BindC l _ _)        = return l
stepLabel (GotoC l _)          = return l
stepLabel (RepeatC l _)        = return l
stepLabel (TakeC l _ _)        = return l
stepLabel (TakesC l _ _ _)     = return l
stepLabel (EmitC l _ _)        = return l
stepLabel (EmitsC l _ _)       = return l
stepLabel (ParC _ _ _ right _) = compLabel right

setStepLabel :: l -> Step l -> Step l
setStepLabel l (VarC _ v s)           = VarC l v s
setStepLabel l (CallC _ v iotas es s) = CallC l v iotas es s
setStepLabel l (IfC _ e c1 c2 s)      = IfC l e c1 c2 s
setStepLabel l (LetC _ decl s)        = LetC l decl s
setStepLabel l (LiftC _ e s)          = LiftC l e s
setStepLabel l (ReturnC _ e s)        = ReturnC l e s
setStepLabel l (BindC _ bv s)         = BindC l bv s
setStepLabel _ step@(GotoC {})        = step
setStepLabel _ step@(RepeatC {})      = step
setStepLabel l (TakeC _ tau s)        = TakeC l tau s
setStepLabel l (TakesC _ i tau s)     = TakesC l i tau s
setStepLabel l (EmitC _ e s)          = EmitC l e s
setStepLabel l (EmitsC _ e s)         = EmitsC l e s
setStepLabel _ step@(ParC {})         = step

{------------------------------------------------------------------------------
 -
 - Statements
 -
 ------------------------------------------------------------------------------}

expToStms :: Exp -> [Stm Exp]
expToStms (ReturnE ann e l)  = [ReturnS ann e l]
expToStms (BindE bv e1 e2 l) = BindS bv e1 l : expToStms e2
expToStms e                  = [ExpS e (srclocOf e)]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary (Decl l) where
    summary (LetD v _ _ _)            = text "definition of" <+> ppr v
    summary (LetFunD v _ _ _ _ _)     = text "definition of" <+> ppr v
    summary (LetExtFunD v _ _ _ _)    = text "definition of" <+> ppr v
    summary (LetRefD v _ _ _)         = text "definition of" <+> ppr v
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
    summary _ = text "computation step"

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty Label where
    ppr (Label s) = text (unintern s)

instance IsLabel Label where

instance IsLabel l => Pretty (Program l) where
    ppr (Program decls comp tau) =
        ppr decls </>
        ppr (LetCompD "main" tau comp noLoc)

instance IsLabel l => Pretty (Decl l) where
    pprPrec p (LetD v tau e _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> ppr e))
      where
        lhs = text "let" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetFunD f ibs vbs tau e _) =
        parensIf (p > appPrec) $
        text "letfun" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 ((text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau)) <+>
        nest 2 (text "=" </> ppr e)

    pprPrec p (LetExtFunD f ibs vbs tau _) =
        parensIf (p > appPrec) $
        text "letextfun" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 ((text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau))

    pprPrec p (LetRefD v tau Nothing _) =
        parensIf (p > appPrec) $
        text "letref" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetRefD v tau (Just e) _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> ppr e))
      where
        lhs = text "letref" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetStructD s flds _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> pprStruct flds))
      where
        lhs = text "struct" <+> ppr s

    pprPrec p (LetCompD v tau ccomp _) =
        parensIf (p > appPrec) $
        group (nest 2 (lhs <+/> text "=" </> ppr ccomp))
      where
        lhs = text "letcomp" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetFunCompD f ibs vbs tau e _) =
        parensIf (p > appPrec) $
        text "letfuncomp" <+> ppr f <+> pprFunParams ibs vbs <+>
        nest 4 ((text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau)) <+>
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

    pprPrec p (UnopE op@(Cast {}) e _) =
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
        ppr decl </>
        nest 2 (text "in" </> pprPrec doPrec1 body)

    pprPrec _ (CallE f is es _) =
        ppr f <> parens (commasep (map ppr is ++ map ppr es))

    pprPrec _ (DerefE v _) =
        text "!" <> pprPrec appPrec1 v

    pprPrec p (AssignE v e _) =
        parensIf (p > appPrec) $
        ppr v <+> text ":=" <+> pprPrec appPrec1 e

    pprPrec _ (WhileE e1 e2 _) =
        text "while" <+>
        group (pprPrec appPrec1 e1) <+>
        pprBody e2

    pprPrec _ (ForE ann v tau e1 e2 e3 _) =
        ppr ann <+> text "for" <+>
        group (parens (ppr v <+> colon <+> ppr tau) <+>
               text "in" <+>
               brackets (commasep [ppr e1, ppr e2])) <>
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

    pprPrec _ (ErrorE tau s _) =
        text "error" <+> text "@" <> pprPrec appPrec1 tau <+> (text . show) s

    pprPrec p (ReturnE ann e _) =
        parensIf (p > appPrec) $
        ppr ann <+> text "return" <+> pprPrec appPrec1 e

    pprPrec _ e@(BindE {}) =
        ppr (expToStms e)

pprBody :: Exp -> Doc
pprBody e =
    case expToStms e of
      [_]  -> line <> align (ppr e)
      stms -> space <> semiEmbraceWrap (map ppr stms)

pprFunParams :: [IVar] -> [(Var, Type)] -> Doc
pprFunParams ivs vbs =
    go ivs vbs
  where
    go :: [IVar] -> [(Var, Type)] -> Doc
    go [] [] =
        empty

    go [] [vb] =
        pprArg vb

    go [] vbs =
        sep (map pprArg vbs)

    go iotas vbs =
        sep (map ppr iotas ++ map pprArg vbs)

    pprArg :: (Var, Type) -> Doc
    pprArg (v, tau) =
        parens $ ppr v <+> text ":" <+> ppr tau

instance IsLabel l => Pretty (Step l) where
    ppr step = ppr (Comp [step])

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
    used :: Set l
    used = compUsedLabels comp

    pprWithLabel :: l -> Doc -> Doc
    pprWithLabel l d
        | l `Set.member` used = nest 2 $ ppr l <> colon <+/> d
        | otherwise           = d

    pprSteps :: Pretty l => [Step l] -> [Doc]
    pprSteps [] =
        []

    pprSteps (VarC l v _ : k) =
        pprBind k $
        pprWithLabel l $
        ppr v

    pprSteps (CallC l f is es _ : k) =
        pprBind k $
        pprWithLabel l $
        ppr f <> parens (commasep (map ppr is ++ map ppr es))

    pprSteps (IfC l e1 e2 e3 _ : k) =
        pprBind k $
        pprWithLabel l $
        text "if"   <+> pprPrec appPrec1 e1 <+/>
        text "then" <+> pprPrec appPrec1 e2 <+/>
        text "else" <+> pprPrec appPrec1 e3

    pprSteps (LetC l decl _ : k) =
        pprBind k $
        pprWithLabel l $
        ppr decl

    pprSteps (LiftC l e _ : k) =
        pprBind k $
        pprWithLabel l $
        ppr e

    pprSteps (ReturnC l e _ : k) =
        pprBind k $
        pprWithLabel l $
        text "return" <+> pprPrec appPrec1 e

    pprSteps (BindC {} : _) =
        error "bind occurred without a preceding computation."

    pprSteps (GotoC l _ : _) =
        [text "goto" <+> ppr l]

    pprSteps (RepeatC l _ : _) =
        [text "repeat" <+> ppr l]

    pprSteps (TakeC l tau _ : k) =
        pprBind k $
        pprWithLabel l $
        text "take" <+> text "@" <> pprPrec tyappPrec1 tau

    pprSteps (TakesC l i tau _ : k) =
        pprBind k $
        pprWithLabel l $
        text "takes" <+> pprPrec appPrec1 i <+> text "@" <> pprPrec appPrec1 tau

    pprSteps (EmitC l e _ : k) =
        pprBind k $
        pprWithLabel l $
        text "emit" <+> pprPrec appPrec1 e

    pprSteps (EmitsC l e _ : k) =
        pprBind k $
        pprWithLabel l $
        text "emits" <+> pprPrec appPrec1 e

    pprSteps (ParC ann tau e1 e2 _ : k) =
        pprBind k $
        pprPrec arrPrec e1 <+>
        ppr ann <> text "@" <> pprPrec appPrec1 tau <+>
        pprPrec arrPrec e2

    pprBind :: Pretty l => [Step l] -> Doc -> [Doc]
    pprBind (BindC _ WildV _  : k) step =
        step : pprSteps k

    pprBind (BindC _ (BindV v tau) _ : k) step =
        step' : pprSteps k
      where
        step' :: Doc
        step' = parens (ppr v <+> colon <+> ppr tau) <+>
                text "<-" <+> align step

    pprBind k step =
        step : pprSteps k

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs (Decl l) Var where
    fvs (LetD v _ e _)              = delete v (fvs e)
    fvs (LetFunD v _ vbs _ e _)     = delete v (fvs e) <\\> fromList (map fst vbs)
    fvs (LetExtFunD {})             = mempty
    fvs (LetRefD v _ e _)           = delete v (fvs e)
    fvs (LetStructD {})             = mempty
    fvs (LetCompD v _ ccomp _)      = delete v (fvs ccomp)
    fvs (LetFunCompD v _ vbs _ e _) = delete v (fvs e) <\\> fromList (map fst vbs)

instance Binders (Decl l) Var where
    binders (LetD v _ _ _)            = singleton v
    binders (LetFunD v _ _ _ _ _)     = singleton v
    binders (LetExtFunD v _ _ _ _)    = singleton v
    binders (LetRefD v _ _ _)         = singleton v
    binders (LetStructD {})           = mempty
    binders (LetCompD v _ _ _)        = singleton v
    binders (LetFunCompD v _ _ _ _ _) = singleton v

instance Fvs LocalDecl Var where
    fvs (LetLD v _ e _)    = delete v (fvs e)
    fvs (LetRefLD v _ e _) = delete v (fvs e)

instance Binders LocalDecl Var where
    binders (LetLD v _ _ _)    = singleton v
    binders (LetRefLD v _ _ _) = singleton v

instance Fvs Exp Var where
    fvs (ConstE {})                 = mempty
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
    fvs (ErrorE {})                 = mempty
    fvs (ReturnE _ e _)             = fvs e
    fvs (BindE bv e1 e2 _)          = fvs e1 <> (fvs e2 <\\> binders bv)

instance Fvs (Step l) Var where
    fvs (VarC _ v _)       = singleton v
    fvs (CallC _ f _ es _) = singleton f <> fvs es
    fvs (IfC _ e1 e2 e3 _) = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetC _ decl _)    = fvs decl
    fvs (LiftC _ e _)      = fvs e
    fvs (ReturnC _ e _)    = fvs e
    fvs (BindC {})         = mempty
    fvs (GotoC {})         = mempty
    fvs (RepeatC {})       = mempty
    fvs (TakeC {})         = mempty
    fvs (TakesC {})        = mempty
    fvs (EmitC _ e _)      = fvs e
    fvs (EmitsC _ e _)     = fvs e
    fvs (ParC _ _ e1 e2 _) = fvs e1 <> fvs e2

instance Fvs (Comp l) Var where
    fvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                          = mempty
        go (BindC _ bv _ : k)          = go k <\\> binders bv
        go (LetC _ decl _ : k)         = fvs decl <> (go k <\\> binders decl)
        go (step : k)                  = fvs step <> go k

instance Fvs Exp v => Fvs [Exp] v where
    fvs es = foldMap fvs es

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
 - Iota substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Iota IVar LocalDecl where
    substM (LetLD v tau e s) =
        LetLD v <$> substM tau <*> substM e <*> pure s

    substM (LetRefLD v tau e s) =
        LetRefLD v <$> substM tau <*> substM e <*> pure s

instance Subst Iota IVar Exp where
    substM e@(ConstE {}) =
        return e

    substM e@(VarE {}) =
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

    substM (BindE bv e1 e2 l) = do
        BindE <$> substM bv <*> substM e1 <*> substM e2 <*> pure l

instance Subst Iota IVar (Step l) where
    substM step@(VarC {}) =
        pure step

    substM (CallC l v iotas es s) =
        CallC l v <$> substM iotas <*> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC l <$> substM decl <*> pure s

    substM (LiftC l e s) =
        LiftC l <$> substM e <*> pure s

    substM (ReturnC l e s) =
        ReturnC l <$> substM e <*> pure s

    substM (BindC l bv s) =
        BindC l <$> substM bv <*> pure s

    substM step@(GotoC {}) =
        return step

    substM step@(RepeatC {}) =
        return step

    substM (TakeC l tau s) =
        TakeC l <$> substM tau <*> pure s

    substM (TakesC l i tau s) =
        TakesC l i <$> substM tau <*> pure s

    substM (EmitC l e s) =
        EmitC l <$> substM e <*> pure s

    substM (EmitsC l e s) =
        EmitsC l <$> substM e <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann <$> substM tau <*> substM c1 <*> substM c2 <*> pure s

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
    substM e@(ConstE {}) =
        return e

    substM e@(VarE {}) =
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

    substM (BindE bv e1 e2 l) =
        BindE <$> substM bv <*> substM e1 <*> substM e2 <*> pure l

instance Subst Type TyVar (Step l) where
    substM step@(VarC {}) =
        pure step

    substM (CallC l v iotas es s) =
        CallC l v iotas <$> substM es <*> pure s

    substM (IfC l e c1 c2 s) =
        IfC l <$> substM e <*> substM c1 <*> substM c2 <*> pure s

    substM (LetC l decl s) =
        LetC l <$> substM decl <*> pure s

    substM (LiftC l e s) =
        LiftC l <$> substM e <*> pure s

    substM (ReturnC l e s) =
        ReturnC l <$> substM e <*> pure s

    substM (BindC l bv s) =
        BindC l <$> substM bv <*> pure s

    substM step@(GotoC {}) =
        return step

    substM step@(RepeatC {}) =
        return step

    substM (TakeC l tau s) =
        TakeC l <$> substM tau <*> pure s

    substM (TakesC l i tau s) =
        TakesC l i <$> substM tau <*> pure s

    substM (EmitC l e s) =
        EmitC l <$> substM e <*> pure s

    substM (EmitsC l e s) =
        EmitsC l <$> substM e <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann <$> substM tau <*> substM c1 <*> substM c2 <*> pure s

instance Subst Type TyVar (Comp l) where
    substM (Comp steps) = Comp <$> substM steps

{------------------------------------------------------------------------------
 -
 - Expression substitution
 -
 ------------------------------------------------------------------------------}

instance Subst Exp Var Exp where
    substM e@(ConstE {}) =
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
        freshen v $ \v' -> do
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

    substM e@(ErrorE {}) =
        pure e

    substM (ReturnE ann e l) =
        ReturnE ann <$> substM e <*> pure l

    substM (BindE bv e1 e2 l) = do
        e1' <- substM e1
        freshen bv $ \bv' -> do
        BindE bv' e1' <$> substM e2 <*> pure l

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

    substM (LetC {}) =
        faildoc $ text "Cannot substitute in a let computation step."

    substM (LiftC l e s) =
        LiftC l <$> substM e <*> pure s

    substM (ReturnC l e s) =
        ReturnC l <$> substM e <*> pure s

    substM (BindC {}) =
        faildoc $ text "Cannot substitute in a bind computation step."

    substM step@(GotoC {}) =
        return step

    substM step@(RepeatC {}) =
        return step

    substM step@(TakeC {}) =
        return step

    substM step@(TakesC {}) =
        return step

    substM (EmitC l e s) =
        EmitC l <$> substM e <*> pure s

    substM (EmitsC l e s) =
        EmitsC l <$> substM e <*> pure s

    substM (ParC ann tau c1 c2 s) =
        ParC ann tau <$> substM c1 <*> substM c2 <*> pure s

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

        go (step@(BindC _ WildV _) : steps) = do
            steps' <- go steps
            return $ step : steps'

        go (BindC l (BindV v tau) s : steps) = do
            freshen v $ \v' -> do
            steps' <- go steps
            return $ BindC l (BindV v' tau) s : steps'

        go (step : steps) =
            (:) <$> substM step <*> go steps

{------------------------------------------------------------------------------
 -
 - Freshening I-variables
 -
 ------------------------------------------------------------------------------}

instance Freshen (Decl l) Iota IVar where
    freshen (LetD v tau e l) k = do
        decl' <- LetD v <$> substM tau <*> substM e <*> pure l
        k decl'

    freshen (LetFunD v ibs vbs tau e l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetFunD v ibs' <$> substM vbs <*> substM tau <*> substM e <*> pure l
        k decl'

    freshen (LetExtFunD v ibs vbs tau l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetExtFunD v ibs' <$> substM vbs <*> substM tau <*> pure l
        k decl'

    freshen (LetRefD v tau e l) k = do
        decl' <- LetRefD v <$> substM tau <*> substM e <*> pure l
        k decl'

    freshen decl@(LetStructD {}) k =
        k decl

    freshen (LetCompD v tau comp l) k = do
        decl' <- LetCompD v <$> substM tau <*> substM comp <*> pure l
        k decl'

    freshen (LetFunCompD v ibs vbs tau comp l) k =
        freshen ibs $ \ibs' -> do
        decl' <- LetFunCompD v ibs' vbs <$> substM tau <*> substM comp <*> pure l
        k decl'

{------------------------------------------------------------------------------
 -
 - Freshening variables
 -
 ------------------------------------------------------------------------------}

instance Freshen (Decl l) Exp Var where
    freshen (LetD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' -> do
        k (LetD v' tau e' l)

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

    freshen (LetRefD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' -> do
        k (LetRefD v' tau e' l)

    freshen decl@(LetStructD {}) k =
        k decl

    freshen (LetCompD v tau comp l) k = do
        comp' <- substM comp
        freshen v $ \v' -> do
        k (LetCompD v' tau comp' l)

    freshen (LetFunCompD v ibs vbs tau comp l) k =
        freshen v   $ \v'   ->
        freshen vbs $ \vbs' -> do
        decl' <- LetFunCompD v' ibs vbs' tau <$> substM comp <*> pure l
        k decl'

instance Freshen LocalDecl Exp Var where
    freshen (LetLD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' -> do
        k (LetLD v' tau e' l)

    freshen (LetRefLD v tau e l) k = do
        e' <- substM e
        freshen v $ \v' -> do
        k (LetRefLD v' tau e' l)

instance Freshen Var Exp Var where
    freshen v@(Var n) k (theta, phi) | v `Set.member` phi =
        k v' (theta', phi')
      where
        phi'    = Set.insert v' phi
        theta'  = Map.insert v (varE v') theta
        v'      = head [x | i <- [show i | i <- [(1::Integer)..]]
                          , let x = Var n { nameSym = intern (s ++ i) }
                          , x `Set.notMember` phi]
          where
            s :: String
            s = namedString n

        varE :: Var -> Exp
        varE v = VarE v (srclocOf v)

    freshen v k (theta, phi) =
        k v (theta', phi')
      where
        phi'   = Set.insert v phi
        theta' = Map.delete v theta

instance Freshen (Var, Type) Exp Var where
    freshen (v, tau) k =
        freshen v $ \v' ->
        k (v', tau)

instance Freshen BindVar Exp Var where
    freshen WildV k =
        k WildV

    freshen (BindV v tau) k =
        freshen v $ \v' ->
        k $ BindV v' tau

{------------------------------------------------------------------------------
 -
 - Staging
 -
 ------------------------------------------------------------------------------}

instance Num Exp where
    e1 + e2 = BinopE Add e1 e2 (e1 `srcspan` e2)
    e1 * e2 = BinopE Mul e1 e2 (e1 `srcspan` e2)

    negate e = UnopE Neg e (srclocOf e)

    fromInteger i = ConstE (IntC dEFAULT_INT_WIDTH Signed i) noLoc

    abs _    = error "Num Exp: abs not implemented"
    signum _ = error "Num Exp: signum not implemented"

instance IsEq Exp where
    e1 .==. e2 = BinopE Eq e1 e2 (e1 `srcspan` e2)
    e1 ./=. e2 = BinopE Ne e1 e2 (e1 `srcspan` e2)

instance IsOrd Exp where
    e1 .<.  e2 = BinopE Lt e1 e2 (e1 `srcspan` e2)
    e1 .<=. e2 = BinopE Le e1 e2 (e1 `srcspan` e2)
    e1 .>=. e2 = BinopE Ge e1 e2 (e1 `srcspan` e2)
    e1 .>.  e2 = BinopE Gt e1 e2 (e1 `srcspan` e2)

#include "KZC/Auto/Syntax-instances.hs"

instance Located (Decl l) where
    locOf (LetD _ _ _ l)            = locOf l
    locOf (LetFunD _ _ _ _ _ l)     = locOf l
    locOf (LetExtFunD _ _ _ _ l)    = locOf l
    locOf (LetRefD _ _ _ l)         = locOf l
    locOf (LetStructD _ _ l)        = locOf l
    locOf (LetCompD _ _ _ l)        = locOf l
    locOf (LetFunCompD _ _ _ _ _ l) = locOf l

instance Located (Comp l) where
    locOf (Comp [])       = NoLoc
    locOf (Comp (step:_)) = locOf step

instance Located (Step l) where
    locOf (VarC _ _ l)        = locOf l
    locOf (CallC _ _ _ _ l)   = locOf l
    locOf (IfC _ _ _ _ l)     = locOf l
    locOf (LetC _ _ l)        = locOf l
    locOf (LiftC _ _ l)       = locOf l
    locOf (ReturnC _ _ l)     = locOf l
    locOf (BindC _ _ l)       = locOf l
    locOf (GotoC _ l)         = locOf l
    locOf (RepeatC _ l)       = locOf l
    locOf (TakeC _ _ l)       = locOf l
    locOf (TakesC _ _ _ l)    = locOf l
    locOf (EmitC _ _ l)       = locOf l
    locOf (EmitsC _ _ l)      = locOf l
    locOf (ParC _ _ _ _ l)    = locOf l

#endif /* !defined(ONLY_TYPEDEFS) */
