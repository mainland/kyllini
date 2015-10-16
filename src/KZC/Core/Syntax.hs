{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : KZC.Core.Syntax
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Syntax (
    Var(..),
    Field(..),
    Struct(..),
    TyVar(..),
    IVar(..),
    W(..),
    Signedness(..),
    Const(..),
    Decl(..),
    Exp(..),
    Stm(..),
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

#if !defined(ONLY_TYPEDEFS)
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

import Data.Foldable (foldMap)
import Data.Loc
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import qualified Data.Set as Set
import Data.String
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Pretty
import KZC.Staged
import KZC.Summary
import KZC.Util.SetLike
import KZC.Vars

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show)

instance IsString Var where
    fromString s = Var (fromString s)

instance Named Var where
    namedSymbol (Var n) = namedSymbol n

newtype Field = Field Name
  deriving (Eq, Ord, Read, Show)

instance IsString Field where
    fromString s = Field (fromString s)

instance Named Field where
    namedSymbol (Field n) = namedSymbol n

newtype Struct = Struct Name
  deriving (Eq, Ord, Read, Show)

instance IsString Struct where
    fromString s = Struct (fromString s)

instance Named Struct where
    namedSymbol (Struct n) = namedSymbol n

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Read, Show)

instance IsString TyVar where
    fromString s = TyVar (fromString s)

instance Named TyVar where
    namedSymbol (TyVar n) = namedSymbol n

newtype IVar = IVar Name
  deriving (Eq, Ord, Read, Show)

instance IsString IVar where
    fromString s = IVar (fromString s)

instance Named IVar where
    namedSymbol (IVar n) = namedSymbol n

data W = W8
       | W16
       | W32
       | W64
  deriving (Eq, Ord, Read, Show)

data Signedness = Signed
                | Unsigned
  deriving (Eq, Ord, Read, Show)

data Const = UnitC
           | BoolC Bool
           | BitC Bool
           | IntC W Signedness Integer
           | FloatC W Rational
           | StringC String
           | ArrayC [Const]
  deriving (Eq, Ord, Read, Show)

data Decl = LetD Var Type Exp !SrcLoc
          | LetFunD Var [IVar] [(Var, Type)] Type Exp !SrcLoc
          | LetExtFunD Var [IVar] [(Var, Type)] Type !SrcLoc
          | LetRefD Var Type (Maybe Exp) !SrcLoc
          | LetStructD Struct [(Field, Type)] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp Exp !SrcLoc
         | LetE Decl Exp !SrcLoc
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
         -- Computations
         | ReturnE InlineAnn Exp !SrcLoc
         | BindE BindVar Exp Exp !SrcLoc
         | TakeE Type !SrcLoc
         | TakesE Int Type !SrcLoc
         | EmitE Exp !SrcLoc
         | EmitsE Exp !SrcLoc
         | RepeatE VectAnn Exp !SrcLoc
         | ParE PipelineAnn Type Exp Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Stm e = ReturnS InlineAnn e !SrcLoc
           | BindS BindVar e !SrcLoc
           | ExpS e !SrcLoc
  deriving (Eq, Ord, Read, Show)

data UnrollAnn = Unroll     -- ^ Always unroll
               | NoUnroll   -- ^ Never unroll
               | AutoUnroll -- ^ Let the compiler choose when to unroll
  deriving (Enum, Eq, Ord, Read, Show)

data InlineAnn = Inline     -- ^ Always inline
               | NoInline   -- ^ Never inline
               | AutoInline -- ^ Let the compiler decide when to inline
  deriving (Enum, Eq, Ord, Read, Show)

data PipelineAnn = Pipeline     -- ^ Always pipeline
                 | NoPipeline   -- ^ Never pipeline
                 | AutoPipeline -- ^ Let the compiler decide when to pipeline
  deriving (Enum, Eq, Ord, Read, Show)

data VectAnn = AutoVect
             | Rigid Bool Int Int  -- ^ True == allow mitigations up, False ==
                                   -- disallow mitigations up
             | UpTo  Bool Int Int
  deriving (Eq, Ord, Read, Show)

data BindVar = BindV Var Type
             | WildV
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

data StructDef = StructDef Struct [(Field, Type)] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | BitT !SrcLoc
          | IntT W Signedness !SrcLoc
          | FloatT W !SrcLoc
          | StringT !SrcLoc
          | StructT Struct !SrcLoc
          | ArrT Iota Type !SrcLoc
          | ST [TyVar] Omega Type Type Type !SrcLoc
          | RefT Type !SrcLoc
          | FunT [IVar] [Type] Type !SrcLoc
          | TyVarT TyVar !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Omega = C Type
           | T
  deriving (Eq, Ord, Read, Show)

data Iota = ConstI Int !SrcLoc
          | VarI IVar !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Kind = TauK   -- ^ Base types, including arrays of base types
          | OmegaK -- ^ @C tau@ or @T@
          | MuK    -- ^ @ST omega tau tau@ types
          | RhoK   -- ^ Reference types
          | PhiK   -- ^ Function types
          | IotaK  -- ^ Array index types
  deriving (Eq, Ord, Read, Show)

-- | @isComplexStruct s@ is @True@ if @s@ is a complex struct type.
isComplexStruct :: Struct -> Bool
isComplexStruct "complex"   = True
isComplexStruct "complex8"  = True
isComplexStruct "complex16" = True
isComplexStruct "complex32" = True
isComplexStruct "complex64" = True
isComplexStruct _           = False

#if !defined(ONLY_TYPEDEFS)
{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary Decl where
    summary (LetD v _ _ _)         = text "definition of" <+> ppr v
    summary (LetFunD v _ _ _ _ _)  = text "definition of" <+> ppr v
    summary (LetExtFunD v _ _ _ _) = text "definition of" <+> ppr v
    summary (LetRefD v _ _ _)      = text "definition of" <+> ppr v
    summary (LetStructD s _ _)     = text "definition of" <+> ppr s

instance Summary Exp where
    summary e = text "expression:" <+> align (ppr e)

instance Summary StructDef where
    summary (StructDef s _ _) = text "struct" <+> ppr s

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

instance Pretty TyVar where
    ppr (TyVar n) = ppr n

instance Pretty IVar where
    ppr (IVar n) = ppr n

instance Pretty W where
    ppr W8  = text "8"
    ppr W16 = text "16"
    ppr W32 = text "32"
    ppr W64 = text "64"

instance Pretty Const where
    ppr UnitC               = text "()"
    ppr (BoolC False)       = text "false"
    ppr (BoolC True)        = text "true"
    ppr (BitC False)        = text "'0"
    ppr (BitC True)         = text "'1"
    ppr (IntC _ Signed i)   = ppr i
    ppr (IntC _ Unsigned i) = ppr i <> char 'u'
    ppr (FloatC _ f)        = ppr (fromRational f :: Double)
    ppr (StringC s)         = text (show s)
    ppr (ArrayC cs)         = braces $ commasep $ map ppr cs

instance Pretty Decl where
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

    pprPrec _ (TakeE tau _) =
        text "take" <+> text "@" <> pprPrec tyappPrec1 tau

    pprPrec p (TakesE i tau _) =
        parensIf (p > appPrec) $
        text "takes" <+> pprPrec appPrec1 i <+> text "@" <> pprPrec appPrec1 tau

    pprPrec p (EmitE e _) =
        parensIf (p > appPrec) $
        text "emit" <+> pprPrec appPrec1 e

    pprPrec p (EmitsE e _) =
        parensIf (p > appPrec) $
        text "emits" <+> pprPrec appPrec1 e

    pprPrec p (RepeatE ann e _) =
        parensIf (p > appPrec) $
        ppr ann <+> text "repeat" <> pprBody e

    pprPrec p (ParE ann tau e1 e2 _) =
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+>
        ppr ann <> text "@" <> pprPrec appPrec1 tau <+>
        pprPrec arrPrec e2

instance Pretty PipelineAnn where
    ppr Pipeline = text "|>>>|"
    ppr _        = text ">>>"

expToStms :: Exp -> [Stm Exp]
expToStms (ReturnE ann e l)  = [ReturnS ann e l]
expToStms (BindE bv e1 e2 l) = BindS bv e1 l : expToStms e2
expToStms e                  = [ExpS e (srclocOf e)]

pprBody :: Exp -> Doc
pprBody e =
    case expToStms e of
      [_]  -> line <> align (ppr e)
      stms -> space <> semiEmbraceWrap (map ppr stms)

instance Pretty e => Pretty (Stm e) where
    pprPrec p (ReturnS ann e _) =
        parensIf (p > appPrec) $
        ppr ann <+> text "return" <+> ppr e

    pprPrec _ (BindS (BindV v tau) e _) =
        parens (ppr v <+> colon <+> ppr tau) <+>
        text "<-" <+> align (ppr e)

    pprPrec _ (BindS WildV e _) =
        ppr e

    pprPrec p (ExpS e _) =
        pprPrec p e

    pprList stms =
        semiEmbrace (map ppr stms)

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

instance Pretty BindVar where
    ppr (BindV v tau) = parens $ ppr v <+> colon <+> ppr tau
    ppr WildV         = text "_"

instance Pretty Unop where
    ppr Lnot       = text "not" <> space
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

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (BitT _) =
        text "bit"

    pprPrec _ (IntT w Signed _) =
        text "int" <> ppr w

    pprPrec _ (IntT w Unsigned _) =
        text "uint" <> ppr w

    pprPrec _ (FloatT W32 _) =
        text "float"

    pprPrec _ (FloatT W64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec _ (StringT _) =
        text "string"

    pprPrec p (RefT tau _) =
        parensIf (p > tyappPrec) $
        text "ref" <+> pprPrec tyappPrec1 tau

    pprPrec p (StructT s _) =
        parensIf (p > tyappPrec) $
        text "struct" <+> ppr s

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)

    pprPrec p (ST alphas omega tau1 tau2 tau3 _) =
        parensIf (p > tyappPrec) $
        pprForall alphas <+>
        text "ST" <+>
        align (sep [pprPrec tyappPrec1 omega
                   ,pprPrec tyappPrec1 tau1
                   ,pprPrec tyappPrec1 tau2
                   ,pprPrec tyappPrec1 tau3])
      where
        pprForall :: [TyVar] -> Doc
        pprForall []     = empty
        pprForall alphas = text "forall" <+> sep (map ppr alphas) <+> dot

    pprPrec p (FunT iotas taus tau _) =
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

    pprPrec _ (TyVarT tv _) =
        ppr tv

instance Pretty Omega where
    pprPrec p (C tau) =
        parensIf (p > tyappPrec) $
        text "C" <+> ppr tau

    pprPrec _ T =
        text "T"

instance Pretty Iota where
    ppr (ConstI i _) = ppr i
    ppr (VarI v _)   = ppr v

instance Pretty Kind where
    ppr TauK   = text "tau"
    ppr OmegaK = text "omega"
    ppr MuK    = text "mu"
    ppr RhoK   = text "rho"
    ppr PhiK   = text "phi"
    ppr IotaK  = text "iota"

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

doPrec :: Int
doPrec = 12

doPrec1 :: Int
doPrec1 = doPrec + 1

appPrec :: Int
appPrec = 13

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

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Type TyVar where
    fvs (UnitT {})                         = mempty
    fvs (BoolT {})                         = mempty
    fvs (BitT {})                          = mempty
    fvs (IntT {})                          = mempty
    fvs (FloatT {})                        = mempty
    fvs (StringT {})                       = mempty
    fvs (StructT _ _)                      = mempty
    fvs (ArrT _ tau _)                     = fvs tau
    fvs (ST alphas omega tau1 tau2 tau3 _) = fvs omega <>
                                             (fvs tau1 <> fvs tau2 <> fvs tau3)
                                             <\\> fromList alphas
    fvs (RefT tau _)                       = fvs tau
    fvs (FunT _ taus tau _)                = fvs taus <> fvs tau
    fvs (TyVarT tv _)                      = singleton tv

instance Fvs Omega TyVar where
    fvs (C tau) = fvs tau
    fvs T       = mempty

instance Fvs Type IVar where
    fvs (UnitT {})                    = mempty
    fvs (BoolT {})                    = mempty
    fvs (BitT {})                     = mempty
    fvs (IntT {})                     = mempty
    fvs (FloatT {})                   = mempty
    fvs (StringT {})                  = mempty
    fvs (StructT _ _)                 = mempty
    fvs (ArrT iota tau _)             = fvs iota <> fvs tau
    fvs (ST _ omega tau1 tau2 tau3 _) = fvs omega <> fvs tau1 <> fvs tau2 <> fvs tau3
    fvs (RefT tau _)                  = fvs tau
    fvs (FunT ivs taus tau _)         = (fvs taus <> fvs tau) <\\> fromList ivs
    fvs (TyVarT {})                   = mempty

instance Fvs Omega IVar where
    fvs (C tau) = fvs tau
    fvs T       = mempty

instance Fvs Iota IVar where
    fvs (ConstI {}) = mempty
    fvs (VarI iv _) = singleton iv

instance Fvs Type n => Fvs [Type] n where
    fvs taus = foldMap fvs taus

instance Fvs Decl Var where
    fvs (LetD v _ e _)          = delete v (fvs e)
    fvs (LetFunD v _ vbs _ e _) = delete v (fvs e) <\\> fromList (map fst vbs)
    fvs (LetExtFunD {})         = mempty
    fvs (LetRefD v _ e _)       = delete v (fvs e)
    fvs (LetStructD {})         = mempty

instance Binders Decl Var where
    binders (LetD v _ _ _)         = singleton v
    binders (LetFunD v _ _ _ _ _)  = singleton v
    binders (LetExtFunD v _ _ _ _) = singleton v
    binders (LetRefD v _ _ _)      = singleton v
    binders (LetStructD {})        = mempty

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
    fvs (TakeE {})                  = mempty
    fvs (TakesE {})                 = mempty
    fvs (EmitE e _)                 = fvs e
    fvs (EmitsE e _)                = fvs e
    fvs (RepeatE _ e _)             = fvs e
    fvs (ParE _ _ e1 e2 _)          = fvs e1 <> fvs e2

instance Fvs Exp v => Fvs [Exp] v where
    fvs es = foldMap fvs es

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

    subst _ _ tau@(StringT {}) =
        tau

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ArrT iota tau l) =
        ArrT iota (subst theta phi tau) l

    subst theta phi (ST alphas omega tau1 tau2 tau3 l) =
        ST alphas' (s omega) (s tau1) (s tau2) (s tau3) l
      where
        (alphas', theta', phi') = freshen alphas theta phi

        s :: Subst Type TyVar a => a -> a
        s = subst theta' phi'

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (FunT iotas taus tau l) =
        FunT iotas (subst theta phi taus) (subst theta phi tau) l

    subst theta _ tau@(TyVarT alpha _) =
        fromMaybe tau (Map.lookup alpha theta)

instance Subst Type TyVar Omega where
    subst theta phi (C tau) =
        C (subst theta phi tau)

    subst _ _ T =
        T

instance Subst Iota IVar Type where
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

    subst _ _ tau@(StringT {}) =
        tau

    subst _ _ tau@(StructT {}) =
        tau

    subst theta phi (ArrT iota tau l) =
        ArrT (subst theta phi iota) (subst theta phi tau) l

    subst theta phi (ST alphas omega tau1 tau2 tau3 l) =
        ST alphas (subst theta phi omega) (subst theta phi tau1)
               (subst theta phi tau2)  (subst theta phi tau3) l

    subst theta phi (RefT tau l) =
        RefT (subst theta phi tau) l

    subst theta phi (FunT iotas taus tau l) =
        FunT iotas' (subst theta' phi' taus) (subst theta' phi' tau) l
      where
        (iotas', theta', phi') = freshen iotas theta phi

    subst _ _ tau@(TyVarT {}) =
        tau

instance Subst Iota IVar Omega where
    subst theta phi (C tau) =
        C (subst theta phi tau)

    subst _ _ T =
        T

instance Subst Iota IVar Iota where
    subst _ _ iota@(ConstI {}) =
        iota

    subst theta _ iota@(VarI iv _) =
        fromMaybe iota (Map.lookup iv theta)

instance Freshen TyVar TyVar Type where
    freshen alpha@(TyVar n) theta phi | alpha `Set.member` phi =
        (alpha', theta', phi')
      where
        phi'    = Set.insert alpha' phi
        theta'  = Map.insert alpha (tyVarT alpha') theta
        alpha'  = head [beta  | i <- [show i | i <- [(1::Integer)..]]
                              , let beta = TyVar n { nameSym = intern (s ++ i) }
                              , beta `Set.notMember` phi]
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

instance Freshen IVar IVar Iota where
    freshen alpha@(IVar n) theta phi | alpha `Set.member` phi =
        (alpha', theta', phi')
      where
        phi'    = Set.insert alpha' phi
        theta'  = Map.insert alpha (ivarT alpha') theta
        alpha'  = head [beta  | i <- [show i | i <- [(1::Integer)..]]
                              , let beta = IVar n { nameSym = intern (s ++ i) }
                              , beta `Set.notMember` phi]
          where
            s :: String
            s = namedString n

        ivarT :: IVar -> Iota
        ivarT v = VarI v (srclocOf v)

    freshen alpha theta phi =
        (alpha, theta', phi')
      where
        phi'    = Set.insert alpha phi
        theta'  = Map.delete alpha theta

{------------------------------------------------------------------------------
 -
 - Staging
 -
 ------------------------------------------------------------------------------}

instance IsEq Exp where
    e1 .==. e2 = BinopE Eq e1 e2 (e1 `srcspan` e2)
    e1 ./=. e2 = BinopE Ne e1 e2 (e1 `srcspan` e2)

instance IsOrd Exp where
    e1 .<.  e2 = BinopE Lt e1 e2 (e1 `srcspan` e2)
    e1 .<=. e2 = BinopE Le e1 e2 (e1 `srcspan` e2)
    e1 .>=. e2 = BinopE Ge e1 e2 (e1 `srcspan` e2)
    e1 .>.  e2 = BinopE Gt e1 e2 (e1 `srcspan` e2)

#include "KZC/Core/Syntax-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
