{-# LANGUAGE CPP #-}

-- |
-- Module      : Language.Core.Syntax
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Core.Syntax (
    Var(..),
    Field(..),
    Struct(..),
    TyVar(..),
    IVar(..),
    W(..),
    dEFAULT_INT_WIDTH,
    Const(..),
    Exp(..),
    VarBind(..),
    BindVar(..),
    Unop(..),
    Binop(..),
    Type(..),
    Omega(..),
    Iota(..)
  ) where

import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Pretty

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show)

newtype Field = Field Name
  deriving (Eq, Ord, Read, Show)

newtype Struct = Struct Name
  deriving (Eq, Ord, Read, Show)

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Read, Show)

newtype IVar = IVar Name
  deriving (Eq, Ord, Read, Show)

data W = W8
       | W16
       | W32
       | W64
  deriving (Eq, Ord, Read, Show)

dEFAULT_INT_WIDTH :: W
dEFAULT_INT_WIDTH = W32

data Const = UnitC
           | BoolC Bool
           | BitC Bool
           | IntC W Integer
           | FloatC W Rational
           | ComplexC W Integer Integer
           | StringC String
           | ArrayC [Const]
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp Exp !SrcLoc
         | LetE Var Type (Maybe Exp) Exp !SrcLoc
         -- Functions
         | LetFunE Var [IVar] [VarBind] Type Exp Exp !SrcLoc
         | CallE Var [Exp] [Exp] !SrcLoc
         -- References
         | DerefE Exp !SrcLoc
         | AssignE Exp Exp !SrcLoc
         -- Loops
         | WhileE Exp Exp !SrcLoc
         | UntilE Exp Exp !SrcLoc
         | ForE Var Exp Exp Exp !SrcLoc
         -- Arrays
         | ArrayE [Exp] !SrcLoc
         | IdxE Exp Exp (Maybe Int) !SrcLoc
         -- Structs Struct
         | LetStruct Struct [(Field, Type)] !SrcLoc
         | ProjE Exp Field !SrcLoc
         -- Print
         | PrintE Bool [Exp] !SrcLoc
         | ErrorE String !SrcLoc
         -- Computations
         | ReturnE Exp !SrcLoc
         | BindE BindVar Exp Exp !SrcLoc
         | TakeE !SrcLoc
         | TakesE Int !SrcLoc
         | EmitE Exp !SrcLoc
         | EmitsE Exp !SrcLoc
         | RepeatE Exp !SrcLoc
         | ArrE Exp Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data VarBind = VarBind Var Type
  deriving (Eq, Ord, Read, Show)

data BindVar = BindV Var
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

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | BitT !SrcLoc
          | IntT W !SrcLoc
          | FloatT W !SrcLoc
          | ComplexT W !SrcLoc
          | StringT !SrcLoc
          | ArrT Iota Type !SrcLoc
          | StructT Struct !SrcLoc
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
    ppr UnitC            = text "()"
    ppr (BoolC True)     = text "true"
    ppr (BoolC False)    = text "false"
    ppr (BitC True)      = text "'0"
    ppr (BitC False)     = text "'1"
    ppr (IntC _ i)       = ppr i
    ppr (FloatC _ f)     = ppr (fromRational f :: Double)
    ppr (ComplexC w r i) = text "complex" <> ppr w <+> pprStruct [(text "re", ppr r), (text "im", ppr i)]
    ppr (StringC s)      = text (show s)
    ppr (ArrayC cs)      = braces $ commasep $ map ppr cs

pprStruct :: [(Doc, Doc)] -> Doc
pprStruct flds =
    commaEmbrace $
    map pprField flds
  where
    pprField :: (Doc, Doc) -> Doc
    pprField (f, v) = f <+> text "=" <+> v

bracesIf :: Bool -> Doc -> Doc
bracesIf True doc  = braces doc
bracesIf False doc = doc

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

    pprPrec p (LetE v tau Nothing e2 _) =
        parensIf (p >= appPrec) $
        text "let" <+> ppr v <+> text ":" <+> ppr tau <+> text "in" </> ppr e2

    pprPrec p (LetE v tau (Just e1) e2 _) =
        parensIf (p >= appPrec) $
        (lhs <+> text "=" <+> flatten (ppr e1) <|> nest 2 (lhs <+> text "=" </> ppr e1)) </>
        nest 2 (text "in" </> ppr e2)
      where
        lhs = text "let" <+> ppr v <+> text ":" <+> ppr tau

    pprPrec p (LetFunE f ibs vbs tau e1 e2 _) =
        parensIf (p >= appPrec) $
        text "letfun" <+> ppr f <+> pprArgs ibs vbs <+>
        nest 4 ((text ":" <+> flatten (ppr tau) <|> text ":" </> ppr tau)) <+>
        nest 2 (text "=" </> ppr e1) </>
        text "in" </> ppr e2
      where
        pprArgs :: [IVar] -> [VarBind] -> Doc
        pprArgs [] [vb] =
            ppr vb

        pprArgs [] vbs =
            parens (commasep (map ppr vbs))

        pprArgs iotas vbs =
            parens (commasep (map ppr iotas) <> text ";" <+> commasep (map ppr vbs))

    pprPrec _ (CallE f ies es _) =
        ppr f <> parens (commasep (map ppr ies ++ map ppr es))

    pprPrec _ (DerefE v _) =
        text "!" <> pprPrec appPrec1 v

    pprPrec _ (AssignE v e _) =
        ppr v <+> text ":=" <+> pprPrec appPrec1 e

    pprPrec _ (WhileE e1 e2 _) =
        text "while" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec _ (UntilE e1 e2 _) =
        text "until" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec _ (ForE v e1 e2 e3 _) =
        text "for" <+> ppr v <+> text "in" <+>
        brackets (commasep [ppr e1, ppr e2]) <+>
        pprPrec appPrec1 e3

    pprPrec _ (ArrayE es _) =
        text "arr" <+> embrace commasep (map ppr es)

    pprPrec _ (IdxE e1 e2 Nothing _) =
        pprPrec appPrec1 e1 <> brackets (ppr e2)

    pprPrec _ (IdxE e1 e2 (Just i) _) =
        pprPrec appPrec1 e1 <> brackets (commasep [ppr e2, ppr i])

    pprPrec _ (LetStruct s flds _) =
        text "struct" <+> ppr s <+> text "=" <+>
        pprStruct [(ppr fld, ppr tau) | (fld, tau) <- flds]

    pprPrec _ (ProjE e f _) =
        pprPrec appPrec1 e <> text "." <> ppr f

    pprPrec _ (PrintE True es _) =
        text "println" <> parens (commasep (map (pprPrec appPrec1) es))

    pprPrec _ (PrintE False es _) =
        text "print" <> parens (commasep (map (pprPrec appPrec1) es))

    pprPrec _ (ErrorE s _) =
        text "error" <+> ppr s

    pprPrec p (ReturnE e _) =
        parensIf (p > appPrec) $
        text "return" <+> ppr e

    pprPrec p (BindE v e1 e2 _) =
        bracesIf (p > appPrec) $
        ppr v <+> text "<-" <+> pprPrec appPrec1 e1 <> text ";" <+/> ppr e2

    pprPrec _ (TakeE _) =
        text "take"

    pprPrec p (TakesE i _) =
        parensIf (p > appPrec) $
        text "takes" <+> pprPrec appPrec1 i

    pprPrec p (EmitE e _) =
        parensIf (p > appPrec) $
        text "emit" <+> pprPrec appPrec1 e

    pprPrec p (EmitsE e _) =
        parensIf (p > appPrec) $
        text "emits" <+> pprPrec appPrec1 e

    pprPrec p (RepeatE e _) =
        parensIf (p > appPrec) $
        text "repeat" <+> pprPrec appPrec1 e

    pprPrec p (ArrE e1 e2 _) =
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+> text ">>>" <+> pprPrec arrPrec e2

instance Pretty VarBind where
    ppr (VarBind v tau) =
        ppr v <+> text ":" <+> ppr tau

instance Pretty BindVar where
    ppr (BindV v) = ppr v
    ppr WildV     = text "_"

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

    pprPrec _ (StringT _) =
        text "string"

    pprPrec p (RefT tau _) =
        parensIf (p > tyappPrec) $
        text "ref" <+> ppr tau

    pprPrec _ (ArrT ind tau _) =
        ppr tau <> brackets (ppr ind)
    pprPrec _ (StructT s _) =
        text "struct" <+> ppr s

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
        pprForall alphas = text "forall" <+> commasep (map ppr alphas) <+> dot

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

arrowPrec :: Int
arrowPrec = 0

arrowPrec1 :: Int
arrowPrec1 = 1

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

#include "Language/Core/Syntax-instances.hs"
