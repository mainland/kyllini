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

    Label(..),
    LProgram,
    LDecl,
    LComp,

    isComplexStruct,

    Stm(..)
  ) where

import Data.Foldable (Foldable(..), foldMap)
import Data.Loc
import Data.Monoid
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

#if !defined(ONLY_TYPEDEFS)
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

instance Pretty l => Summary (Comp l) where
    summary c = text "computation:" <+> align (ppr c)

instance Pretty l => Summary (Step l) where
    summary _ = text "computation step"

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty Label where
    ppr (Label s) = text (unintern s)

instance Pretty l => Pretty (Program l) where
    ppr (Program decls comp tau) =
        ppr decls </>
        ppr (LetCompD "main" tau comp noLoc)

instance Pretty l => Pretty (Decl l) where
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

instance Pretty l => Pretty (Comp l) where
    pprPrec p comp =
        case pprComp comp of
          [stm] -> parensIf (p > appPrec) $ align stm
          stms  -> semiEmbraceWrap stms

pprComp :: Pretty l => Comp l -> [Doc]
pprComp comp =
    pprSteps (unComp comp)
  where
    pprSteps :: Pretty l => [Step l] -> [Doc]
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

    pprSteps (LiftC _ e _ : k) =
        pprBind k $
        ppr e

    pprSteps (ReturnC _ e _ : k) =
        pprBind k $
        text "return" <+> pprPrec appPrec1 e

    pprSteps (BindC {} : _) =
        error "bind occurred without a preceding computation."

    pprSteps (GotoC l _ : _) =
        [text "goto" <+> ppr l]

    pprSteps (RepeatC l _ : _) =
        [text "repeat" <+> ppr l]

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
    fvs (LetD v _ e _)             = delete v (fvs e)
    fvs (LetFunD v _ vbs _ e _)    = delete v (fvs e) <\\> fromList (map fst vbs)
    fvs (LetExtFunD {})            = mempty
    fvs (LetRefD v _ e _)          = delete v (fvs e)
    fvs (LetStructD {})            = mempty
    fvs (LetCompD v _ ccomp _)     = delete v (fvs ccomp)
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
    fvs (BindE (BindV v _) e1 e2 _) = fvs e1 <> delete v (fvs e2)
    fvs (BindE WildV e1 e2 _)       = fvs e1 <> fvs e2

instance Fvs (Comp l) Var where
    fvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                            = mempty
        go (BindC _ WildV _ : k)         = go k
        go (BindC _ (BindV v _) _ : k)   = delete v (go k)
        go (LetC _ decl _ : k)           = fvs decl <> (go k <\\> binders decl)
        go (step : k)                    = fvs step <> go k

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

instance Fvs Exp v => Fvs [Exp] v where
    fvs es = foldMap fvs es

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
