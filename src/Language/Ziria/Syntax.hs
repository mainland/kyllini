{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Language.Ziria.Syntax
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Ziria.Syntax (
    Var(..),
    Field(..),
    Struct(..),
    W(..),
    Const(..),
    Exp(..),
    VarBind,

    UnrollAnn(..),
    InlineAnn(..),
    PipelineAnn(..),
    VectAnn(..),

    Unop(..),
    Binop(..),

    CompLet(..),
    Stm(..),
    Cmd(..),

    StructDef(..),
    Type(..),
    Ind(..),

    mkVar,
    mkStruct,
    mkField,

    imField,
    reField
  ) where

import Data.Loc
import Data.Monoid
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Pretty
import KZC.Summary
import KZC.Util.SetLike
import KZC.Vars

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show)

newtype Field = Field Name
  deriving (Eq, Ord, Read, Show)

newtype Struct = Struct Name
  deriving (Eq, Ord, Read, Show)

data W = W8
       | W16
       | W32
       | W64
  deriving (Eq, Ord, Read, Show)

data Const = UnitC
           | BoolC Bool
           | BitC Bool
           | IntC W Integer
           | FloatC W Double
           | ComplexC W Integer Integer
           | StringC String
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp Exp !SrcLoc
         | LetE Var (Maybe Type) Exp Exp !SrcLoc
         -- Functions
         | CallE Var [Exp] !SrcLoc
         -- References
         | LetRefE Var Type (Maybe Exp) Exp !SrcLoc
         | AssignE Exp Exp !SrcLoc
         -- Loops
         | WhileE Exp Exp !SrcLoc
         | UntilE Exp Exp !SrcLoc
         | TimesE UnrollAnn Exp Exp !SrcLoc
         | ForE UnrollAnn Var (Maybe Type) Exp Exp Exp !SrcLoc
         -- Arrays
         | ArrayE [Exp] !SrcLoc
         | IdxE Exp Exp (Maybe Integer) !SrcLoc
         -- Structs Struct
         | StructE Struct [(Field, Exp)] !SrcLoc
         | ProjE Exp Field !SrcLoc
         -- Print
         | PrintE Bool [Exp] !SrcLoc
         | ErrorE String !SrcLoc
         -- Computations
         | ReturnE InlineAnn Exp !SrcLoc
         | TakeE !SrcLoc
         | TakesE Integer !SrcLoc
         | EmitE Exp !SrcLoc
         | EmitsE Exp !SrcLoc
         | RepeatE VectAnn Exp !SrcLoc
         | ArrE PipelineAnn Exp Exp !SrcLoc

         | ReadE (Maybe Type) !SrcLoc
         | WriteE (Maybe Type) !SrcLoc
         | StandaloneE Exp !SrcLoc
         | MapE VectAnn Var (Maybe Type) !SrcLoc
         | FilterE Var (Maybe Type) !SrcLoc
         | CompLetE CompLet Exp !SrcLoc
         | StmE [Stm] !SrcLoc
         | CmdE [Cmd] !SrcLoc
  deriving (Eq, Ord, Read, Show)

type VarBind = (Var, Bool, Type)

data UnrollAnn = Unroll     -- ^ Always unroll
               | NoUnroll   -- ^ Never unroll
               | AutoUnroll -- ^ Let the compiler choose when to unroll
  deriving (Eq, Ord, Read, Show)

data InlineAnn = Inline     -- ^ Always inline
               | NoInline   -- ^ Never inline
               | AutoInline -- ^ Let the compiler decide when to inline
  deriving (Eq, Ord, Read, Show)

data PipelineAnn = Pipeline     -- ^ Always pipeline
                 | NoPipeline   -- ^ Never pipeline
                 | AutoPipeline -- ^ Let the compiler decide when to pipeline
  deriving (Eq, Ord, Read, Show)

data VectAnn = AutoVect
             | Rigid Bool Int Int  -- ^ True == allow mitigations up, False == disallow mitigations up
             | UpTo  Bool Int Int
  deriving (Eq, Ord, Read, Show)

data Unop = Lnot
          | Bnot
          | Neg
          | Cast Type
          | Len
  deriving (Eq, Ord, Read, Show)

data Binop = Lt
           | Le
           | Eq
           | Ge
           | Gt
           | Ne
           | Land
           | Lor
           | Band
           | Bor
           | Bxor
           | LshL
           | LshR
           | AshR
           | Add
           | Sub
           | Mul
           | Div
           | Rem
           | Pow
  deriving (Eq, Ord, Read, Show)

data CompLet = LetCL Var (Maybe Type) Exp !SrcLoc
             | LetRefCL Var Type (Maybe Exp) !SrcLoc
             | LetFunCL Var (Maybe Type) [VarBind] Exp !SrcLoc
             | LetFunExternalCL Var [VarBind] Type !SrcLoc
             | LetStructCL StructDef !SrcLoc
             | LetCompCL Var (Maybe Type) (Maybe (Int, Int)) Exp !SrcLoc
             | LetFunCompCL Var (Maybe Type) (Maybe (Int, Int)) [VarBind] Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Stm = LetS Var (Maybe Type) Exp !SrcLoc
         | LetRefS Var Type (Maybe Exp) !SrcLoc
         | ExpS Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Cmd = LetC CompLet !SrcLoc
         | BindC Var (Maybe Type) Exp !SrcLoc
         | ExpC Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data StructDef = StructDef Struct [(Field, Type)] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | BitT !SrcLoc
          | IntT W !SrcLoc
          | FloatT W !SrcLoc
          | ComplexT W !SrcLoc
          | ArrT Ind Type !SrcLoc
          | StructT Struct !SrcLoc
          | C Type !SrcLoc
          | T !SrcLoc
          | ST Type Type Type !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Ind = ConstI Integer !SrcLoc
         | ArrI Var !SrcLoc
         | NoneI !SrcLoc
  deriving (Eq, Ord, Read, Show)

{------------------------------------------------------------------------------
 -
 - Smart constructors
 -
 ------------------------------------------------------------------------------}

mkVar :: Name -> Var
mkVar n = Var n

mkStruct :: Name -> Struct
mkStruct n = Struct n

mkField :: Name -> Field
mkField n = Field n

imField, reField :: Field
imField = Field $ Name (intern "im") noLoc
reField = Field $ Name (intern "re") noLoc

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Exp Var where
    fvs (ConstE {})             = mempty
    fvs (VarE v _)              = singleton v
    fvs (UnopE _ e _)           = fvs e
    fvs (BinopE _ e1 e2 _)      = fvs e1 <> fvs e2
    fvs (IfE e1 e2 e3 _)        = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetE v _ e1 e2 _)      = delete v (fvs e1 <> fvs e2)
    fvs (CallE v es _)          = singleton v <> fvs es
    fvs (LetRefE v _ e1 e2 _)   = delete v (fvs e1 <> fvs e2)
    fvs (AssignE e1 e2 _)       = fvs e1 <> fvs e2
    fvs (WhileE e1 e2 _)        = fvs e1 <> fvs e2
    fvs (UntilE e1 e2 _)        = fvs e1 <> fvs e2
    fvs (TimesE _ e1 e2 _)      = fvs e1 <> fvs e2
    fvs (ForE _ v _ e1 e2 e3 _) = fvs e1 <> fvs e2 <> delete v (fvs e3)
    fvs (ArrayE es _)           = fvs es
    fvs (IdxE e1 e2 _ _)        = fvs e1 <> fvs e2
    fvs (StructE _ flds _)      = fvs (map snd flds)
    fvs (ProjE e _ _)           = fvs e
    fvs (PrintE _ es _)         = fvs es
    fvs (ErrorE {})             = mempty
    fvs (ReturnE _ e _)         = fvs e
    fvs (TakeE {})              = mempty
    fvs (TakesE {})             = mempty
    fvs (EmitE e _)             = fvs e
    fvs (EmitsE e _)            = fvs e
    fvs (RepeatE _ e _)         = fvs e
    fvs (ArrE _ e1 e2 _)        = fvs e1 <> fvs e2
    fvs (ReadE {})              = mempty
    fvs (WriteE {})             = mempty
    fvs (StandaloneE e _)       = fvs e
    fvs (MapE _ v _ _)          = singleton v
    fvs (FilterE v _ _)         = singleton v
    fvs (CompLetE cl e _)       = fvs cl <> (fvs e <\\> binders cl)

    fvs (StmE stms0 _) = go stms0
      where
        go []                       = mempty
        go (LetS v _ e _    : stms) = delete v (fvs e <> go stms)
        go (LetRefS v _ e _ : stms) = delete v (fvs e <> go stms)
        go (ExpS e _        : stms) = fvs e <> go stms

    fvs (CmdE cmds0 _) = go cmds0
      where
        go []                     = mempty
        go (LetC cl _     : cmds) = fvs cl <> (go cmds <\\> binders cl)
        go (BindC v _ e _ : cmds) = delete v (fvs e <> go cmds)
        go (ExpC e _      : cmds) = fvs e <> go cmds

instance Fvs CompLet Var where
    fvs cl@(LetCL _ _ e _)            = fvs e <\\> binders cl
    fvs cl@(LetRefCL _ _ e _)         = fvs e <\\> binders cl
    fvs cl@(LetFunCL _ _ _ e _)       = fvs e <\\> binders cl
    fvs (LetFunExternalCL {})         = mempty
    fvs (LetStructCL {})              = mempty
    fvs cl@(LetCompCL _ _ _ e _)      = fvs e <\\> binders cl
    fvs cl@(LetFunCompCL _ _ _ _ e _) = fvs e <\\> binders cl

instance Binders CompLet Var where
    binders (LetCL v _ _ _)             = singleton v
    binders (LetRefCL v _ _ _)          = singleton v
    binders (LetFunCL v _ ps _ _)       = singleton v <> fromList [pv | (pv,_,_) <- ps]
    binders (LetFunExternalCL v ps _ _) = singleton v <> fromList [pv | (pv,_,_) <- ps]
    binders (LetStructCL {})            = mempty
    binders (LetCompCL v _ _ _ _)       = singleton v
    binders (LetFunCompCL v _ _ ps _ _) = singleton v <> fromList [pv | (pv,_,_) <- ps]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary Exp where
    summary e = text "expression" <+> ppr e

instance Summary StructDef where
    summary (StructDef s _ _) = text "struct" <+> ppr s

instance Summary CompLet where
    summary (LetCL v _ _ _)            = text "definition of" <+> ppr v
    summary (LetRefCL v _ _ _)         = text "definition of" <+> ppr v
    summary (LetFunCL v _ _ _ _)       = text "definition of" <+> ppr v
    summary (LetFunExternalCL v _ _ _) = text "definition of" <+> ppr v
    summary (LetStructCL s _)          = text "definition of" <+> summary s
    summary (LetCompCL v _ _ _ _)      = text "definition of" <+> ppr v
    summary (LetFunCompCL v _ _ _ _ _) = text "definition of" <+> ppr v

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty Var where
    ppr (Var n) = ppr n

instance Pretty Field where
    ppr (Field n) = ppr n

instance Pretty Struct where
    ppr (Struct n) = ppr n

instance Pretty W where
    ppr W8  = text "8"
    ppr W16 = text "16"
    ppr W32 = text "32"
    ppr W64 = text "64"

instance Pretty Const where
    ppr UnitC            = text "()"
    ppr (BoolC True)     = text "true"
    ppr (BoolC False)    = text "false"
    ppr (BitC True)      = text "'0"
    ppr (BitC False)     = text "'1"
    ppr (IntC _ i)       = ppr i
    ppr (FloatC _ f)     = ppr f
    ppr (ComplexC w r i) = text "complex" <> ppr w <+> pprStruct [(reField, r), (imField, i)]
    ppr (StringC s)      = text (show s)

instance Pretty Exp where
    pprPrec _ (ConstE c _) =
        ppr c

    pprPrec _ (VarE v _) =
        ppr v

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

    pprPrec p (LetE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        text "let" <+> pprSig v tau <+>
        text "="   <+>
        nest 2 (ppr e1 <+/> text "in" <+> ppr e2)

    pprPrec _ (CallE f vs _) =
        ppr f <> parens (commasep (map ppr vs))

    pprPrec p (LetRefE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        text "var" <+> ppr v <+> colon <+> ppr tau <+>
        pprInitializer e1 <+/>
        text "in"  <+> pprPrec appPrec1 e2

    pprPrec _ (AssignE v e _) =
        ppr v <+> text ":=" <+> ppr e

    pprPrec _ (WhileE e1 e2 _) =
        text "while" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec _ (UntilE e1 e2 _) =
        text "until" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec _ (TimesE ann e1 e2 _) =
        ppr ann <+> text "times" <+> ppr e1 <+> ppr e2

    pprPrec _ (ForE ann v tau e1 e2 e3 _) =
        ppr ann <+> text "for" <+> pprSig v tau <+> text "in" <+>
        brackets (commasep [ppr e1, ppr e2]) <+>
        ppr e3

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
        text "println" <+> commasep (map ppr es)

    pprPrec _ (PrintE False es _) =
        text "print" <+> commasep (map ppr es)

    pprPrec _ (ErrorE s _) =
        text "error" <+> ppr s

    pprPrec _ (ReturnE AutoInline e@(StmE {}) _) =
        text "do" <+> ppr e

    pprPrec _ (ReturnE ann e _) =
        ppr ann <+> text "return" <+> ppr e

    pprPrec _ (TakeE _) =
        text "take"

    pprPrec _ (TakesE i _) =
        text "takes" <+> ppr i

    pprPrec _ (EmitE e _) =
        text "emit" <+> ppr e

    pprPrec _ (EmitsE e _) =
        text "emits" <+> ppr e

    pprPrec _ (RepeatE ann e _) =
        ppr ann <+> text "repeat" <+> ppr e

    pprPrec p (ArrE Pipeline e1 e2 _) =
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+> text "|>>>|" <+> pprPrec arrPrec e2

    pprPrec p (ArrE _ e1 e2 _) =
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+> text ">>>" <+> pprPrec arrPrec e2

    pprPrec _ (ReadE tau _) =
        text "read" <> pprTypeAnn tau

    pprPrec _ (WriteE tau _) =
        text "write" <> pprTypeAnn tau

    pprPrec _ (StandaloneE e _) =
        text "standalone" <+> ppr e

    pprPrec _ (MapE ann v tau _) =
        text "map" <+> ppr ann <+> pprSig v tau

    pprPrec _ (FilterE v tau _) =
        text "filter" <+> pprSig v tau

    pprPrec _ (CompLetE l e _) =
        ppr l <+/> nest 2 (text "in" <+/> ppr e)

    pprPrec _ (StmE stms _) =
        ppr stms

    pprPrec _ (CmdE cmds _) =
        ppr cmds

instance Pretty UnrollAnn where
    ppr Unroll     = text "unroll"
    ppr NoUnroll   = text "nounroll"
    ppr AutoUnroll = empty

instance Pretty InlineAnn where
    ppr AutoInline = empty
    ppr NoInline   = text "noinline"
    ppr Inline     = text "forceinline"

instance Pretty VectAnn where
    ppr (Rigid True from to)  = text "!" <> ppr (Rigid False from to)
    ppr (Rigid False from to) = brackets (commasep [ppr from, ppr to])
    ppr (UpTo f from to)      = text "<=" <+> ppr (Rigid f from to)
    ppr AutoVect              = empty

instance Pretty Unop where
    ppr Lnot       = text "!"
    ppr Bnot       = text "~"
    ppr Neg        = text "-"
    ppr Len        = text "length" <> space
    ppr (Cast tau) = parens (ppr tau)

instance Pretty Binop where
    ppr Lt   = text "<"
    ppr Le   = text "<="
    ppr Eq   = text "=="
    ppr Ge   = text ">="
    ppr Gt   = text ">"
    ppr Ne   = text "!="
    ppr Land = text "&&"
    ppr Lor  = text "||"
    ppr Band = text "&"
    ppr Bor  = text "|"
    ppr Bxor = text "^"
    ppr LshL = text "<<"
    ppr LshR = text ">>>"
    ppr AshR = text ">>"
    ppr Add  = text "+"
    ppr Sub  = text "-"
    ppr Mul  = text "*"
    ppr Div  = text "/"
    ppr Rem  = text "%"
    ppr Pow  = text "**"

instance Pretty CompLet where
    ppr (LetCL v tau e _) =
        text "let" <+> pprSig v tau <+> text "=" <+> ppr e

    ppr (LetRefCL v tau e _) =
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    ppr (LetFunCL f tau ps e _) =
        text "fun" <+> pprSig f tau <+> parens (commasep (map ppr ps)) <+> ppr e

    ppr (LetFunExternalCL f ps tau _) =
        text "fun" <+> text "external" <+> ppr f <+> parens (commasep (map ppr ps)) <+> colon <+> ppr tau

    ppr (LetStructCL def _) =
        ppr def

    ppr (LetCompCL v tau range e _) =
        text "let" <+> text "comp" <+> pprRange range <+>
        pprSig v tau <+> text "=" <+> ppr e

    ppr (LetFunCompCL f tau range ps e _) =
        text "fun" <+> text "comp" <+> pprRange range <+>
        pprSig f tau <+> parens (commasep (map ppr ps)) <+> text "=" <+> ppr e

    pprList cls = stack (map ppr cls)

instance Pretty Stm where
    ppr (LetS v tau e _) =
        text "let" <+> pprSig v tau <+> text "=" <+> ppr e

    ppr (LetRefS v tau e _) =
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    ppr (ExpS e _) =
        ppr e

    pprList stms =
        embrace semisep (map ppr stms)

instance Pretty Cmd where
    ppr (LetC l _) =
        ppr l

    ppr (BindC v tau e _) =
        pprSig v tau <+> text "<-" <+> ppr e

    ppr (ExpC e _) =
        ppr e

    pprList cmds =
        embrace semisep (map ppr cmds)

instance Pretty StructDef where
    ppr (StructDef s fields _) =
        text "struct" <+> ppr s <+> text "=" <+> pprStruct fields

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

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)

    pprPrec _ (StructT s _) =
        text "struct" <+> ppr s

    pprPrec p (C tau _) =
        parensIf (p > tyappPrec) $
        text "C" <+> ppr tau

    pprPrec _ (T _) =
        text "T"

    pprPrec p (ST w tau1 tau2 _) =
        parensIf (p > tyappPrec) $
        text "ST" <+> ppr w <+> ppr tau1 <+> ppr tau2

instance Pretty Ind where
    ppr (ConstI i _) = ppr i
    ppr (ArrI v _)   = ppr v
    ppr (NoneI _)    = empty

pprStruct :: forall a b . (Pretty a, Pretty b) => [(a, b)] -> Doc
pprStruct flds =
    embrace commasep $
    map pprField flds
  where
    pprField :: (a, b) -> Doc
    pprField (f, v) = ppr f <+> text "=" <+> ppr v

pprSig :: Var -> Maybe Type -> Doc
pprSig v Nothing    = ppr v
pprSig v (Just tau) = parens (ppr v <+> colon <+> ppr tau)

pprInitializer :: Maybe Exp -> Doc
pprInitializer Nothing  = empty
pprInitializer (Just e) = text ":=" <+> ppr e

pprTypeAnn :: Maybe Type -> Doc
pprTypeAnn Nothing    = empty
pprTypeAnn (Just tau) = brackets (ppr tau)

pprRange :: Maybe (Int, Int) -> Doc
pprRange Nothing           = empty
pprRange (Just (from, to)) = brackets (commasep [ppr from, ppr to])

-- %left '&&' '||'
-- %left '==' '!='
-- %left '|'
-- %left '^'
-- %left '&'
-- %left '<' '<=' '>' '>='
-- %left '<<' '>>'
-- %left '+' '-'
-- %left '*' '/' '%' '**'
-- %left NEG
-- %left '>>>'

arrPrec :: Int
arrPrec = 11

appPrec :: Int
appPrec = 12

appPrec1 :: Int
appPrec1 = 13

tyappPrec :: Int
tyappPrec = 1

instance HasFixity Binop where
    fixity Lt   = infixl_ 6
    fixity Le   = infixl_ 6
    fixity Eq   = infixl_ 2
    fixity Ge   = infixl_ 6
    fixity Gt   = infixl_ 6
    fixity Ne   = infixl_ 2
    fixity Land = infixl_ 1
    fixity Lor  = infixl_ 1
    fixity Band = infixl_ 5
    fixity Bor  = infixl_ 3
    fixity Bxor = infixl_ 4
    fixity LshL = infixl_ 7
    fixity LshR = infixl_ 7
    fixity AshR = infixl_ 7
    fixity Add  = infixl_ 8
    fixity Sub  = infixl_ 8
    fixity Mul  = infixl_ 9
    fixity Div  = infixl_ 9
    fixity Rem  = infixl_ 9
    fixity Pow  = infixl_ 9

instance HasFixity Unop where
    fixity Lnot     = infixr_ 10
    fixity Bnot     = infixr_ 10
    fixity Neg      = infixr_ 10
    fixity Len      = infixr_ 10
    fixity (Cast _) = infixr_ 10

#include "Language/Ziria/Syntax-instances.hs"
