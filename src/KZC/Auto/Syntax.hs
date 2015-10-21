{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

    Comp0(..),
    Comp,

    Label(..),
    LProgram,
    LDecl,
    LComp,

    isComplexStruct,

    Stm(..)
  ) where

import Control.Monad.Free
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

data Program l c = Program [Decl l c] (Comp l c) Type

data Decl l c = LetD Var Type Exp !SrcLoc
              | LetFunD Var [IVar] [(Var, Type)] Type Exp !SrcLoc
              | LetExtFunD Var [IVar] [(Var, Type)] Type !SrcLoc
              | LetRefD Var Type (Maybe Exp) !SrcLoc
              | LetStructD Struct [(Field, Type)] !SrcLoc
              | LetCompD Var Type (Comp l c) !SrcLoc
              | LetFunCompD Var [IVar] [(Var, Type)] Type (Comp l c) !SrcLoc

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

-- | A 'Comp0 l c a' represents a  computation with a continuation; we tie the
-- knot to make a free monad via the 'Comp' data type. The type parameter @l@ is
-- for labels, and the type parameter @a@ is for the continuation.  The type
-- parameter @c@ represents "compiled" expressions; the idea is that binding the
-- result of a computation involves binding compiled values, /not/
-- expressions. We are agnostic to the actual representation of compiled values,
-- as indeed we should be, since different back ends may use different
-- representations. Note that the only thing one can really do with a value of
-- type @c@ is use it as an argument to either the 'BindC' or 'DoneC' data
-- constructor. That is by design!
--
-- This free monad construction is a bit funny because it contains both
-- expressions (of type 'Exp') and "compiled" expressions, of type @c@. This is
-- because although our data type needs to embed expressions, it also needs to
-- represent the flow of data through computations, and data may not be
-- represented as expressions. The 'BindC' and 'ReturnC' mediate between the
-- expression and @c@ worlds.

data Comp0 l c a = VarC l Var (c -> a) !SrcLoc
                 | CallC l Var [Iota] [Exp] (c -> a) !SrcLoc
                 | IfC l Exp a a (c -> a) !SrcLoc
                 | LetC l LocalDecl a !SrcLoc

                 -- | Lift an expression of type
                 -- @forall s a b . ST (C tau) s a b@ into the monad. 'LiftC'
                 -- and 'ReturnC' differ only for the purposes of type checking.
                 | LiftC l Exp (c -> a) !SrcLoc

                 -- | A return. The continuation receives the /compiled/
                 -- representation of the expression.
                 | ReturnC l Exp (c -> a) !SrcLoc
                 -- | A bind. This binds a variable to a /compiled/ expression
                 -- value.
                 | BindC l BindVar c a !SrcLoc

                 | GotoC l !SrcLoc
                 -- | A goto that is part of a repeat construct. This is
                 -- separate from 'GotoC' only for the purposes of type
                 -- checking.
                 | RepeatC l !SrcLoc

                 | TakeC l Type (c -> a) !SrcLoc
                 | TakesC l Int Type (c -> a) !SrcLoc
                 | EmitC l Exp a !SrcLoc
                 | EmitsC l Exp a !SrcLoc
                 | ParC PipelineAnn Type a a (c -> a) !SrcLoc

                 -- | Then end of a branch of a computation. This is used for join
                 -- points, as in the branches of an if, and in the branches of
                 -- a par. In both cases, we don't want @'(>>=)'@ to be applied
                 -- to these branches, only to the continuation.
                 | DoneC l c !SrcLoc
  deriving (Functor)

type Comp l c = Free (Comp0 l c) c

newtype Label = Label { unLabel :: Symbol }
  deriving (Eq, Ord, Read, Show)

instance IsString Label where
    fromString s = Label (fromString s)

instance C.ToIdent Label where
    toIdent lbl = C.Id (unintern (unLabel lbl))

type LProgram c = Program Label c

type LDecl c = Decl Label c

type LComp c = Comp Label c

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

instance Summary (Decl l c) where
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

instance Pretty l => Summary (Comp l c) where
    summary c = text "computation:" <+> align (ppr c)

instance Pretty l => Summary (Comp0 l c (Comp l c)) where
    summary c = summary (Free c)

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty Label where
    ppr (Label s) = text (unintern s)

instance Pretty l => Pretty (Program l c) where
    ppr (Program decls comp tau) =
        ppr decls </>
        ppr (LetCompD "main" tau comp noLoc)

instance Pretty l => Pretty (Decl l c) where
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

instance Pretty l => Pretty (Comp l c) where
    pprPrec p comp =
        case pprComp comp of
          [stm] -> parensIf (p > appPrec) $ align stm
          stms  -> semiEmbraceWrap stms

pprComp :: forall l c . Pretty l => Comp l c -> [Doc]
pprComp (Pure _) =
    []

pprComp (Free comp0) =
    pprComp0 comp0
  where
    pprComp0 :: Pretty l => Comp0 l c (Comp l c) -> [Doc]
    pprComp0 comp0 = go comp0
      where
        go :: Comp0 l c (Comp l c) -> [Doc]
        go (VarC _ v k _) =
            pprBind (k undefined) $
            ppr v

        go (CallC _ f is es k _) =
            pprBind (k undefined) $
            ppr f <> parens (commasep (map ppr is ++ map ppr es))

        go (IfC _ e1 e2 e3 k _) =
            pprBind (k undefined) $
            text "if"   <+> pprPrec appPrec1 e1 <+/>
            text "then" <+> pprPrec appPrec1 e2 <+/>
            text "else" <+> pprPrec appPrec1 e3

        go (LetC _ decl k _) =
            pprBind k $
            ppr decl

        go (LiftC _ e k _) =
            pprBind (k undefined) $
            ppr e

        go (ReturnC _ e k _) =
            pprBind (k undefined) $
            text "return" <+> pprPrec appPrec1 e

        go (BindC {}) =
            error "bind occurred without a preceding computation."

        go (GotoC l _) =
            [text "goto" <+> ppr l]

        go (RepeatC l _) =
            [text "repeat" <+> ppr l]

        go (TakeC _ tau k _) =
            pprBind (k undefined) $
            text "take" <+> text "@" <> pprPrec tyappPrec1 tau

        go (TakesC _ i tau k _) =
            pprBind (k undefined) $
            text "takes" <+> pprPrec appPrec1 i <+> text "@" <> pprPrec appPrec1 tau

        go (EmitC _ e k _) =
            pprBind k $
            text "emit" <+> pprPrec appPrec1 e

        go (EmitsC _ e k _) =
            pprBind k $
            text "emits" <+> pprPrec appPrec1 e

        go (ParC ann tau e1 e2 k _) =
            pprBind (k undefined) $
            pprPrec arrPrec e1 <+>
            ppr ann <> text "@" <> pprPrec appPrec1 tau <+>
            pprPrec arrPrec e2

        go (DoneC {}) =
            []

    pprBind :: Comp l c -> Doc -> [Doc]
    pprBind k ppe =
        case k of
          Free (BindC _ WildV _ comp' _) ->
              ppe : pprComp comp'

          Free (BindC _ (BindV v tau) _ comp' _) ->
              let stm = parens (ppr v <+> colon <+> ppr tau) <+>
                        text "<-" <+> align ppe
              in
                stm : pprComp comp'

          comp' ->
              ppe : pprComp comp'

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs (Decl l c) Var where
    fvs (LetD v _ e _)             = delete v (fvs e)
    fvs (LetFunD v _ vbs _ e _)    = delete v (fvs e) <\\> fromList (map fst vbs)
    fvs (LetExtFunD {})            = mempty
    fvs (LetRefD v _ e _)          = delete v (fvs e)
    fvs (LetStructD {})            = mempty
    fvs (LetCompD v _ ccomp _)     = delete v (fvs ccomp)
    fvs (LetFunCompD v _ vbs _ e _) = delete v (fvs e) <\\> fromList (map fst vbs)

instance Binders (Decl l c) Var where
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

instance Fvs (Comp l c) Var where
    fvs (Pure _)    = mempty
    fvs (Free comp) = fvs comp

instance Fvs (Comp0 l c (Free (Comp0 l c) c)) Var where
    fvs (VarC _ v k _)              = singleton v <> fvs (k undefined)
    fvs (CallC _ f _ es k _)        = singleton f <> fvs es <> fvs (k undefined)
    fvs (IfC _ e1 e2 e3 k _)        = fvs e1 <> fvs e2 <> fvs e3 <> fvs (k undefined)
    fvs (LetC _ decl k _)           = fvs decl <> (fvs k <\\> binders decl)
    fvs (LiftC _ e k _)             = fvs e <> fvs (k undefined)
    fvs (ReturnC _ e k _)           = fvs e <> fvs (k undefined)
    fvs (BindC _ WildV _ k _)       = fvs k
    fvs (BindC _ (BindV v _) _ k _) = delete v (fvs k)
    fvs (GotoC {})                  = mempty
    fvs (RepeatC {})                = mempty
    fvs (TakeC _ _ k _)             = fvs (k undefined)
    fvs (TakesC _ _ _ k _)          = fvs (k undefined)
    fvs (EmitC _ e k _)             = fvs e <> fvs k
    fvs (EmitsC _ e k _)            = fvs e <> fvs k
    fvs (ParC _ _ e1 e2 k _)        = fvs e1 <> fvs e2 <> fvs (k undefined)
    fvs (DoneC {})                  = mempty

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

instance Located (Decl l c) where
    locOf (LetD _ _ _ l)            = locOf l
    locOf (LetFunD _ _ _ _ _ l)     = locOf l
    locOf (LetExtFunD _ _ _ _ l)    = locOf l
    locOf (LetRefD _ _ _ l)         = locOf l
    locOf (LetStructD _ _ l)        = locOf l
    locOf (LetCompD _ _ _ l)        = locOf l
    locOf (LetFunCompD _ _ _ _ _ l) = locOf l

instance Located (Comp l c) where
    locOf (Pure _)    = NoLoc
    locOf (Free comp) = locOf comp

instance Located (Comp0 l c a) where
    locOf (VarC _ _ _ l)        = locOf l
    locOf (CallC _ _ _ _ _ l)   = locOf l
    locOf (IfC _ _ _ _ _ l)     = locOf l
    locOf (LetC _ _ _ l)        = locOf l
    locOf (LiftC _ _ _ l)       = locOf l
    locOf (ReturnC _ _ _ l)     = locOf l
    locOf (BindC _ _ _ _ l)     = locOf l
    locOf (GotoC _ l)           = locOf l
    locOf (RepeatC _ l)         = locOf l
    locOf (TakeC _ _ _ l)       = locOf l
    locOf (TakesC _ _ _ _ l)    = locOf l
    locOf (EmitC _ _ _ l)       = locOf l
    locOf (EmitsC _ _ _ l)      = locOf l
    locOf (ParC _ _ _ _ _ l)    = locOf l
    locOf (DoneC _ _ l)         = locOf l

#endif /* !defined(ONLY_TYPEDEFS) */
