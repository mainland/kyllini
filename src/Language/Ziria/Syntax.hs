{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Language.Ziria.Syntax
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Syntax (
    Dialect(..),

    Var(..),
    TyVar(..),
    Field(..),
    Struct(..),

    IP(..),

    QP(..),
    qpToFractional,
    qpFromFractional,

    FP(..),

    Program(..),
    Import(..),
    Decl(..),
    Const(..),
    Exp(..),
    GenInterval(..),
    Stm(..),

    VarBind(..),

    UnrollAnn(..),
    InlineAnn(..),
    PipelineAnn(..),
    VectAnn(..),

    Unop(..),
    Binop(..),

    Type(..),
    Nat,
    Kind(..),
    Tvk,
    Trait(..),
    Traits,
    traits,

    isComplexStruct
  ) where

import Data.Loc
import Data.Monoid
import Data.String
import Text.PrettyPrint.Mainland

import KZC.Globals
import KZC.Name
import KZC.Traits
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Uniq
import KZC.Vars

data Dialect = Classic
             | Kyllini
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

newtype TyVar = TyVar Name
  deriving (Eq, Ord, Read, Show, IsString, Relocatable, Named)

instance Gensym TyVar where
    gensymAt s l = TyVar <$> gensymAt s (locOf l)

    uniquify (TyVar n) = TyVar <$> uniquify n

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show, IsString, Relocatable, Named)

instance Gensym Var where
    gensymAt s l = Var <$> gensymAt s (locOf l)

    uniquify (Var n) = Var <$> uniquify n

newtype Field = Field Name
  deriving (Eq, Ord, Read, Show, IsString, Relocatable, Named)

newtype Struct = Struct Name
  deriving (Eq, Ord, Read, Show, IsString, Relocatable, Named)

-- | Integer precision.
data IP = IDefault
        | I Int
        | UDefault
        | U Int
  deriving (Eq, Ord, Read, Show)

-- | Fixed-point precision.
data QP = Q Int Int  -- ^ Signed Q format. Sign bit is not counted.
        | UQ Int Int -- ^ Unsigned Q format
  deriving (Eq, Ord, Read, Show)

-- | The number of bits in the fractional part of a fixed-point number.
qpFracBits :: QP -> Int
qpFracBits (Q _ w)  = w
qpFracBits (UQ _ w) = w

-- | Convert a fixed-point number to a floating-point number.
qpToFractional :: Fractional a => QP -> Int -> a
qpToFractional qp x = realToFrac x / 2^qpFracBits qp

-- | Convert a floating-point number to a fixed-point number.
qpFromFractional :: RealFrac a => QP -> a -> Int
qpFromFractional qp x = round (x * 2^qpFracBits qp)

-- | Floating-point precision.
data FP = FP16
        | FP32
        | FP64
  deriving (Eq, Ord, Read, Show)

data Program = Program [Import] [Decl]
  deriving (Eq, Ord, Read, Show)

data Import = Import ModuleName
  deriving (Eq, Ord, Read, Show)

data Decl -- | Struct declaration
          = StructD Struct [Tvk] [(Field, Type)] !SrcLoc
          -- | Type alias
          | TypeD Struct [Tvk] Type !SrcLoc
          -- | Standard let binding
          | LetD Var (Maybe Type) Exp !SrcLoc
          -- | Reference binding
          | LetRefD Var (Maybe Type) (Maybe Exp) !SrcLoc
          -- | Type variable binding
          | LetTypeD TyVar (Maybe Kind) Type !SrcLoc
          -- | Function binding
          | LetFunD Var [Tvk] [VarBind] (Maybe Type) Exp !SrcLoc
          -- | External function binding
          | LetFunExternalD Var [VarBind] Type Bool !SrcLoc
          -- | Computation bindings
          | LetCompD Var (Maybe Type) (Maybe (Int, Int)) Exp !SrcLoc
          | LetFunCompD Var (Maybe (Int, Int)) [Tvk] [VarBind] (Maybe Type) Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Const = UnitC
           | BoolC Bool
           | IntC IP Int
           | FixC QP Int
           | FloatC FP Double
           | StringC String
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | TyVarE TyVar !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp (Maybe Exp) !SrcLoc
         | LetE Var (Maybe Type) Exp Exp !SrcLoc
         | LetRefE Var (Maybe Type) (Maybe Exp) Exp !SrcLoc
         | LetTypeE TyVar Type Exp !SrcLoc
         | LetDeclE Decl Exp !SrcLoc
         -- Functions
         | CallE Var (Maybe [Type]) [Exp] !SrcLoc
         -- References
         | AssignE Exp Exp !SrcLoc
         -- Loops
         | WhileE Exp Exp !SrcLoc
         | UntilE Exp Exp !SrcLoc
         | TimesE UnrollAnn Exp Exp !SrcLoc
         | ForE UnrollAnn Var (Maybe Type) GenInterval Exp !SrcLoc
         -- Arrays
         | ArrayE [Exp] !SrcLoc
         | IdxE Exp Exp (Maybe Int) !SrcLoc
         -- Structs Struct
         | StructE Struct [Type] [(Field, Exp)] !SrcLoc
         | ProjE Exp Field !SrcLoc
         -- Casts
         | CastE Type Exp !SrcLoc
         | BitcastE Type Exp !SrcLoc
         -- Print
         | PrintE Bool [Exp] !SrcLoc
         | ErrorE String !SrcLoc
         -- Computations
         | ReturnE InlineAnn Exp !SrcLoc
         | TakeE !SrcLoc
         | TakesE Int !SrcLoc
         | EmitE Exp !SrcLoc
         | EmitsE Exp !SrcLoc
         | RepeatE VectAnn Exp !SrcLoc
         | ParE PipelineAnn Exp Exp !SrcLoc

         | ReadE (Maybe Type) !SrcLoc
         | WriteE (Maybe Type) !SrcLoc
         | StandaloneE Exp !SrcLoc
         | MapE VectAnn Var (Maybe Type) !SrcLoc
         | FilterE Var (Maybe Type) !SrcLoc
         | StmE [Stm] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data GenInterval -- | The interval @e1..e2@, /inclusive/ of @e2@.
                 = FromToInclusive Exp Exp !SrcLoc
                 -- | The interval @e1..e2@, /exclusive/ of @e2@.
                 | FromToExclusive Exp Exp !SrcLoc
                 -- | The interval that starts at @e1@ and has length @e2@.
                 | StartLen Exp Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Stm = LetS Decl !SrcLoc
         | BindS Var (Maybe Type) Exp !SrcLoc
         | ExpS Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

-- | A variable binding. The boolean is @True@ if the variable is a reference,
-- @False@ otherwise.
data VarBind = VarBind Var Bool (Maybe Type)
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

data Unop = Lnot  -- ^ Logical not
          | Bnot  -- ^ Bitwise not
          | Neg   -- ^ Negation
          | Abs   -- ^ Absolute value
          | Exp   -- ^ e^x
          | Exp2  -- ^ 2^x
          | Expm1 -- ^ e^x - 1
          | Log   -- ^ Log base e
          | Log2  -- ^ Log base 2
          | Log1p -- ^ Log base e of (1 + x)
          | Sqrt  -- ^ Square root
          | Sin
          | Cos
          | Tan
          | Asin
          | Acos
          | Atan
          | Sinh
          | Cosh
          | Tanh
          | Asinh
          | Acosh
          | Atanh
          | Len    -- ^ Array length
  deriving (Eq, Ord, Read, Show)

-- | Returns 'True' if 'Unop' application should be pretty-printed as a function
-- call.
isFunUnop :: Unop -> Bool
isFunUnop Abs   = True
isFunUnop Exp   = True
isFunUnop Exp2  = True
isFunUnop Expm1 = True
isFunUnop Log   = True
isFunUnop Log2  = True
isFunUnop Log1p = True
isFunUnop Sqrt  = True
isFunUnop Sin   = True
isFunUnop Cos   = True
isFunUnop Tan   = True
isFunUnop Asin  = True
isFunUnop Acos  = True
isFunUnop Atan  = True
isFunUnop Sinh  = True
isFunUnop Cosh  = True
isFunUnop Tanh  = True
isFunUnop Asinh = True
isFunUnop Acosh = True
isFunUnop Atanh = True
isFunUnop Len   = True
isFunUnop _     = False

data Binop = Eq   -- ^ Equal
           | Ne   -- ^ Not-equal
           | Lt   -- ^ Less-than
           | Le   -- ^ Less-than-or-equal
           | Ge   -- ^ Greater-than-or-equal
           | Gt   -- ^ Greater-than
           | Land -- ^ Logical and
           | Lor  -- ^ Logical or
           | Band -- ^ Bitwise and
           | Bor  -- ^ Bitwise or
           | Bxor -- ^ Bitwise xor
           | LshL -- ^ Logical shift left
           | LshR -- ^ Logical shift right
           | AshR -- ^ Arithmetic shift right
           | Add  -- ^ Addition
           | Sub  -- ^ Subtraction
           | Mul  -- ^ Multiplication
           | Div  -- ^ Division
           | Rem  -- ^ Remainder
           | Pow  -- ^ Power
  deriving (Eq, Ord, Read, Show)

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | IntT IP !SrcLoc
          | FixT QP !SrcLoc
          | FloatT FP !SrcLoc
          | ArrT Type Type !SrcLoc
          | StructT Struct [Type] !SrcLoc
          | C Type !SrcLoc
          | T !SrcLoc
          | ST Type Type Type !SrcLoc

          -- | Natural number types
          | NatT Int !SrcLoc

          -- | Reference to array length
          | LenT Var !SrcLoc

          -- | Unary operator applied to a type
          | UnopT Unop Type !SrcLoc

          -- | Binary operator applied to a type
          | BinopT Binop Type Type !SrcLoc

          -- | Elided type
          | UnknownT !SrcLoc

          | ForallT [Tvk] Type !SrcLoc
          | TyVarT TyVar !SrcLoc
  deriving (Eq, Ord, Read, Show)

-- | A type of kind nat.
type Nat = Type

-- | Kinds
data Kind = TauK Traits -- ^ Base types, including arrays of base types
          | NatK        -- ^ Type-level natural number
  deriving (Eq, Ord, Read, Show)

type Tvk = (TyVar, Maybe Kind)

-- | @isComplexStruct s@ is @True@ if @s@ is a complex struct type.
isComplexStruct :: Struct -> Bool
isComplexStruct "Complex" = True
isComplexStruct _         = False

{------------------------------------------------------------------------------
 -
 - Free variables
 -
 ------------------------------------------------------------------------------}

instance Fvs Decl Var where
    fvs StructD{}                      = mempty
    fvs TypeD  {}                      = mempty
    fvs d@(LetD _ _ e _)               = fvs e <\\> binders d
    fvs d@(LetRefD _ _ e _)            = fvs e <\\> binders d
    fvs LetTypeD{}                     = mempty
    fvs d@(LetFunD _ _ _ _ e _)        = fvs e <\\> binders d
    fvs LetFunExternalD{}              = mempty
    fvs d@(LetCompD _ _ _ e _)         = fvs e <\\> binders d
    fvs d@(LetFunCompD  _ _ _ _ _ e _) = fvs e <\\> binders d

instance Fvs Exp Var where
    fvs ConstE{}              = mempty
    fvs (VarE v _)            = singleton v
    fvs TyVarE{}              = mempty
    fvs (UnopE _ e _)         = fvs e
    fvs (BinopE _ e1 e2 _)    = fvs e1 <> fvs e2
    fvs (IfE e1 e2 e3 _)      = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetE v _ e1 e2 _)    = delete v (fvs e1 <> fvs e2)
    fvs (LetRefE v _ e1 e2 _) = delete v (fvs e1 <> fvs e2)
    fvs (LetTypeE _ _ e _)    = fvs e
    fvs (LetDeclE decl e _)   = fvs decl <> (fvs e <\\> binders decl)
    fvs (CallE v _ es _)      = singleton v <> fvs es
    fvs (AssignE e1 e2 _)     = fvs e1 <> fvs e2
    fvs (WhileE e1 e2 _)      = fvs e1 <> fvs e2
    fvs (UntilE e1 e2 _)      = fvs e1 <> fvs e2
    fvs (TimesE _ e1 e2 _)    = fvs e1 <> fvs e2
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
    fvs TakeE{}               = mempty
    fvs TakesE{}              = mempty
    fvs (EmitE e _)           = fvs e
    fvs (EmitsE e _)          = fvs e
    fvs (RepeatE _ e _)       = fvs e
    fvs (ParE _ e1 e2 _)      = fvs e1 <> fvs e2
    fvs ReadE{}               = mempty
    fvs WriteE{}              = mempty
    fvs (StandaloneE e _)     = fvs e
    fvs (MapE _ v _ _)        = singleton v
    fvs (FilterE v _ _)       = singleton v
    fvs (StmE stms _)         = fvs stms

instance Fvs Exp v => Fvs [Exp] v where
    fvs = foldMap fvs

instance Fvs GenInterval Var where
    fvs (FromToInclusive e1 e2 _) = fvs e1 <> fvs e2
    fvs (FromToExclusive e1 e2 _) = fvs e1 <> fvs e2
    fvs (StartLen e1 e2 _)        = fvs e1 <> fvs e2

instance Fvs [Stm] Var where
    fvs []                     = mempty
    fvs (LetS d _     : cmds)  = fvs d <> (fvs cmds <\\> binders d)
    fvs (BindS v _ e _ : cmds) = delete v (fvs e <> fvs cmds)
    fvs (ExpS e _      : cmds) = fvs e <> fvs cmds

instance Binders Decl Var where
    binders StructD{}                     = mempty
    binders TypeD{}                       = mempty
    binders (LetD v _ _ _)                = singleton v
    binders (LetRefD v _ _ _)             = singleton v
    binders LetTypeD{}                    = mempty
    binders (LetFunD v _ ps _ _ _)        = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders (LetFunExternalD v ps _ _ _)  = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders (LetCompD v _ _ _ _)          = singleton v
    binders (LetFunCompD v _ _ ps _ _ _ ) = singleton v <> fromList [pv | VarBind pv _ _ <- ps]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary Decl where
    summary (StructD s _ _ _)           = text "definition of" <+> ppr s
    summary (TypeD s _ _ _)             = text "definition of" <+> ppr s
    summary (LetD v _ _ _)              = text "definition of" <+> ppr v
    summary (LetRefD v _ _ _)           = text "definition of" <+> ppr v
    summary (LetTypeD alpha _ _ _)      = text "definition of" <+> ppr alpha
    summary (LetFunD v _ _ _ _ _)       = text "definition of" <+> ppr v
    summary (LetFunExternalD v _ _ _ _) = text "definition of" <+> ppr v
    summary (LetCompD v _ _ _ _)        = text "definition of" <+> ppr v
    summary (LetFunCompD v _ _ _ _ _ _) = text "definition of" <+> ppr v

instance Summary Exp where
    summary e = text "expression:" <+> align (ppr e)

instance Summary Stm where
    summary (LetS d _)      = summary d
    summary (BindS v _ _ _) = text "definition of" <+> ppr v
    summary (ExpS e _)      = summary e

{------------------------------------------------------------------------------
 -
 - Pretty printing
 -
 ------------------------------------------------------------------------------}

instance Pretty Var where
    ppr (Var n) = ppr n

instance Pretty TyVar where
    ppr (TyVar n) = ppr n

instance Pretty Field where
    ppr (Field n) = ppr n

instance Pretty Struct where
    ppr (Struct n) = ppr n

instance Pretty QP where
    ppr (Q 0 f)  = text "q" <> ppr f
    ppr (Q i f)  = text "q" <> ppr i <> char '_' <> ppr f
    ppr (UQ 0 f) = text "uq" <> ppr f
    ppr (UQ i f) = text "uq" <> ppr i <> char '_' <> ppr f

instance Pretty FP where
    ppr FP16 = text "16"
    ppr FP32 = text "32"
    ppr FP64 = text "64"

instance Pretty Program where
    ppr (Program imports decls) =
        ppr imports </> ppr decls

instance Pretty Import where
    ppr (Import mod) = text "import" <+> ppr mod

    pprList []      = empty
    pprList imports = semisep (map ppr imports)

instance Pretty Decl where
    pprPrec _ (StructD s _ fields _) | classicDialect =
        align $ nest 2 $
        text "struct" <+> ppr s <+> text "=" <+> pprStruct semi colon fields

    pprPrec _ (StructD s tvks fields _)=
        align $ nest 2 $
        text "struct" <+> ppr s <> pprForall tvks <+> pprStruct comma colon fields

    pprPrec _ (TypeD s tvks tau _) =
        text "type" <+> ppr s <> pprForall tvks <+> text "=" <+> ppr tau

    pprPrec p (LetD v tau e _) | classicDialect =
        parensIf (p > appPrec) $
        text "let" <+> pprTypeSig v tau <+> text "=" <+/> ppr e

    pprPrec p (LetD v tau e _) =
        parensIf (p > appPrec) $
        text "let" <+> pprTypeSig v tau <+> text "=" <+/> ppr e <> semi

    pprPrec p (LetRefD v tau e _) | classicDialect =
        parensIf (p > appPrec) $
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    pprPrec p (LetRefD v tau e _) =
        parensIf (p > appPrec) $
        text "let mut" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e <> semi

    pprPrec p (LetTypeD alpha kappa tau _) | classicDialect =
        parensIf (p > appPrec) $
        text "nat" <+> pprKindSig (alpha, kappa) <+> char '=' <+> ppr tau

    pprPrec p (LetTypeD alpha kappa tau _) =
        parensIf (p > appPrec) $
        text "let nat" <+> pprKindSig (alpha, kappa) <+> char '=' <+> ppr tau <+> semi

    pprPrec _ (LetFunD f _tvks ps _tau e _) | classicDialect =
        text "fun" <+> ppr f <> parens (commasep (map ppr ps)) <+> ppr e

    pprPrec _ (LetFunD f tvks ps maybe_tau e _) =
        text "fun" <+> ppr f <> pprForall tvks <>
        parens (commasep (map ppr ps)) <+> sig <+> ppr e
      where
        sig :: Doc
        sig = case maybe_tau of
                Nothing  -> empty
                Just tau -> text "->" <+> ppr tau

    pprPrec _ (LetFunExternalD f ps tau isPure _) | classicDialect =
        text "fun" <+> text "external" <+> pureDoc <+>
        ppr f <+> parens (commasep (map ppr ps)) <+> colon <+> ppr tau
      where
        pureDoc = if isPure then empty else text "impure"

    pprPrec _ (LetFunExternalD f ps tau isPure _) =
        text "fun" <+> text "external" <+> pureDoc <+>
        ppr f <+> parens (commasep (map ppr ps)) <+> text "->" <+> ppr tau
      where
        pureDoc = if isPure then empty else text "impure"

    pprPrec _ (LetCompD v tau range e _) | classicDialect =
        text "let" <+> text "comp" <+> pprRange range <+>
        pprTypeSig v tau <+> text "=" <+/> ppr e

    pprPrec _ (LetCompD v tau range e _) =
        text "let" <+> text "comp" <+> pprRange range <+>
        pprTypeSig v tau <+> text "=" <+/> ppr e <> semi

    -- We never see this form in the new dialect.
    pprPrec _ (LetFunCompD f range tvks ps _tau e _) =
        text "fun" <+> text "comp" <+> pprRange range <+>
        ppr f <> pprForall tvks <> parens (commasep (map ppr ps)) <+> ppr e

    pprList cls = stack (map ppr cls)

instance Pretty Const where
    pprPrec _ UnitC             = text "()"
    pprPrec _ (BoolC False)     = text "false"
    pprPrec _ (BoolC True)      = text "true"
    pprPrec _ (IntC (U 1) 0)    = text "'0"
    pprPrec _ (IntC (U 1) 1)    = text "'1"
    pprPrec _ (IntC IDefault x) = ppr x
    pprPrec _ (IntC I{} x)      = ppr x
    pprPrec _ (IntC UDefault x) = ppr x <> char 'u'
    pprPrec _ (IntC U{} x)      = ppr x <> char 'u'
    pprPrec _ (FixC qp x)       = ppr (qpToFractional qp x :: Double) <> ppr qp
    pprPrec _ (FloatC _ f)      = ppr f
    pprPrec _ (StringC s)       = text (show s)

instance Pretty Exp where
    pprPrec _ (ConstE c _) =
        ppr c

    pprPrec _ (VarE v _) =
        ppr v

    pprPrec _ (TyVarE alpha _) =
        ppr alpha

    pprPrec _ (UnopE op e _) | isFunUnop op =
        ppr op <> parens (ppr e)

    pprPrec p (UnopE op e _) =
        unop p op e

    pprPrec p (BinopE op e1 e2 _) =
        infixop p op e1 e2

    pprPrec p (IfE e1 e2 maybe_e3 _) =
        parensIf (p >= appPrec) $
        text "if"   <+> pprPrec ifPrec1 e1 <+/>
        text "then" <+> pprPrec ifPrec1 e2 <+/>
        case maybe_e3 of
          Nothing -> empty
          Just e3 -> text "else" <+> pprPrec ifPrec1 e3

    pprPrec p (LetE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        nest 2 $
        text "let" <+> pprTypeSig v tau <+>
        text "="   <+>
        ppr e1 <+/> text "in" <+> ppr e2

    pprPrec p (LetRefE v tau e1 e2 _) | classicDialect =
        parensIf (p >= appPrec) $
        text "var" <+> pprTypeSig v tau <+>
        pprInitializer e1 <+/>
        text "in" <+> pprPrec appPrec1 e2

    pprPrec p (LetRefE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        text "let mut" <+> pprTypeSig v tau <+>
        pprInitializer e1 <+/>
        text "in" <+> pprPrec appPrec1 e2

    pprPrec p (LetTypeE alpha tau e _) | classicDialect =
        parensIf (p >= appPrec) $
        text "nat" <+> ppr alpha <+> char '=' <+> ppr tau <+>
        text "in" <+> pprPrec appPrec1 e

    pprPrec p (LetTypeE alpha tau e _) =
        parensIf (p >= appPrec) $
        text "let nat" <+> ppr alpha <+> char '=' <+> ppr tau <+>
        text "in" <+> pprPrec appPrec1 e

    pprPrec p (LetDeclE decl e _) =
        parensIf (p >= appPrec) $
        ppr decl <+/> text "in" <+/> ppr e

    pprPrec _ (CallE f taus vs _) =
        ppr f <> pprMaybeTyApp taus <> parens (commasep (map ppr vs))
      where
        pprMaybeTyApp :: Maybe [Type] -> Doc
        pprMaybeTyApp Nothing     = empty
        pprMaybeTyApp (Just taus) = pprTyApp taus

    pprPrec _ (AssignE v e _) =
        ppr v <+> text ":=" <+> ppr e

    pprPrec _ (WhileE e1 e2 _) =
        text "while" <+> pprPrec appPrec1 e1 <+/>
        pprPrec appPrec1 e2

    pprPrec _ (UntilE e1 e2 _) =
        text "until" <+> pprPrec appPrec1 e1 <+/>
        pprPrec appPrec1 e2

    pprPrec _ (TimesE ann e1 e2 _) =
        ppr ann <+> text "times" <+> ppr e1 <+/>
        ppr e2

    pprPrec _ (ForE ann v tau gint e3 _) =
        ppr ann <+> text "for" <+> pprTypeSig v tau <+>
        text "in" <+> ppr gint <+/>
        ppr e3

    pprPrec _ (ArrayE es _) | classicDialect =
        text "arr" <+> enclosesep lbrace rbrace comma (map ppr es)

    pprPrec _ (ArrayE es _) =
        list (map ppr es)

    pprPrec _ (IdxE e1 e2 Nothing _) =
        pprPrec appPrec1 e1 <> brackets (ppr e2)

    pprPrec _ (IdxE e1 e2 (Just i) _) =
        pprPrec appPrec1 e1 <> brackets (commasep [ppr e2, ppr i])

    pprPrec _ (StructE s taus fields _) =
        ppr s <> pprTyApp taus <+> pprStruct comma equals fields

    pprPrec _ (ProjE e f _) =
        pprPrec appPrec1 e <> text "." <> ppr f

    pprPrec _ (CastE tau e _) | classicDialect =
        pprPrec appPrec1 tau <> parens (ppr e)

    pprPrec _ (CastE tau e _) =
        text "cast" <> angles (ppr tau) <> parens (ppr e)

    pprPrec _ (BitcastE tau e _) =
        text "bitcast" <> angles (ppr tau) <> parens (ppr e)

    pprPrec p (PrintE True es _) =
        parensIf (p > appPrec) $
        text "println" <+> commasep (map ppr es)

    pprPrec p (PrintE False es _) =
        parensIf (p > appPrec) $
        text "print" <+> commasep (map ppr es)

    pprPrec p (ErrorE s _) =
        parensIf (p > appPrec) $
        text "error" <+> (text . show) s

    pprPrec p (ReturnE ann e _) =
        parensIf (p > appPrec) $
        ppr ann <+> text "return" <+> pprPrec appPrec1 e

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

    pprPrec _ (RepeatE ann e _) =
        ppr ann <+> text "repeat" <+> ppr e

    pprPrec p (ParE Pipeline e1 e2 _) =
        parensIf (p > parrPrec) $
        pprPrec parrPrec e1 <+> text "|>>>|" <+> pprPrec parrPrec1 e2

    pprPrec p (ParE _ e1 e2 _) =
        parensIf (p > parrPrec) $
        pprPrec parrPrec e1 <+> text ">>>" <+> pprPrec parrPrec1 e2

    pprPrec _ (ReadE tau _) =
        text "read" <> pprTypeAnn tau

    pprPrec _ (WriteE tau _) =
        text "write" <> pprTypeAnn tau

    pprPrec _ (StandaloneE e _) =
        text "standalone" <+> ppr e

    pprPrec p (MapE ann v tau _) =
        parensIf (p > appPrec) $
        text "map" <+> ppr ann <+> pprTypeSig v tau

    pprPrec p (FilterE v tau _) =
        parensIf (p > appPrec) $
        text "filter" <+> pprTypeSig v tau

    pprPrec _ (StmE stms _) =
        ppr stms

instance Pretty GenInterval where
    ppr (FromToInclusive e1 e2 _) =
        brackets $ ppr e1 <> colon <> ppr e2

    ppr (FromToExclusive e1 e2 _) =
        ppr e1 <> text ".." <> ppr e2

    ppr (StartLen e1 e2 _) =
        brackets $ ppr e1 <> comma <+> ppr e2

instance Pretty VarBind where
    pprPrec p (VarBind v isRef maybe_tau) =
        case maybe_tau of
          Nothing  -> vdoc
          Just tau -> parensIf (p > appPrec) $
                      vdoc <+> colon <+> ppr tau
      where
        vdoc :: Doc
        vdoc | isRef && classicDialect = text "var" <+> ppr v
             | isRef                   = text "mut" <+> ppr v
             | otherwise               = ppr v

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
    ppr Lnot  = text "!"
    ppr Bnot  = text "~"
    ppr Neg   = text "-"
    ppr Abs   = text "abs"
    ppr Exp   = text "exp"
    ppr Exp2  = text "exp2"
    ppr Expm1 = text "expm1"
    ppr Log   = text "log"
    ppr Log2  = text "log2"
    ppr Log1p = text "log1p"
    ppr Sqrt  = text "sqrt"
    ppr Sin   = text "sin"
    ppr Cos   = text "cos"
    ppr Tan   = text "tan"
    ppr Asin  = text "asin"
    ppr Acos  = text "acos"
    ppr Atan  = text "atan"
    ppr Sinh  = text "sinh"
    ppr Cosh  = text "cosh"
    ppr Tanh  = text "tanh"
    ppr Asinh = text "asinh"
    ppr Acosh = text "acosh"
    ppr Atanh = text "atanh"
    ppr Len   = text "length"

instance Pretty Binop where
    ppr Eq   = text "=="
    ppr Ne   = text "!="
    ppr Lt   = text "<"
    ppr Le   = text "<="
    ppr Ge   = text ">="
    ppr Gt   = text ">"
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

instance Pretty Stm where
    ppr (LetS l _) =
        ppr l

    ppr (BindS v tau e _) =
        pprTypeSig v tau <+> text "<-" <+> ppr e

    ppr (ExpS e _) =
        ppr e

    pprList cmds =
        embrace (map ppr cmds)

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (IntT (U 1) _) =
        text "bit"

    pprPrec _ (IntT IDefault _) =
        text "int"

    pprPrec _ (IntT (I w) _)
      | classicDialect = text "int" <> ppr w
      | otherwise      = char 'i' <> ppr w

    pprPrec _ (IntT UDefault _) =
        text "uint"

    pprPrec _ (IntT (U w) _)
      | classicDialect = text "uint" <> ppr w
      | otherwise      = char 'u' <> ppr w

    pprPrec _ (FixT qp _) =
        ppr qp

    pprPrec _ (FloatT FP32 _) =
        text "float"

    pprPrec _ (FloatT FP64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec p (ArrT ind tau _) | classicDialect =
        parensIf (p > tyappPrec) $
        text "arr" <> brackets (ppr ind) <+> ppr tau

    pprPrec _ (ArrT UnknownT{} tau _) =
        brackets (ppr tau)

    pprPrec _ (ArrT ind tau _) =
        brackets (pprPrec appPrec1 tau <+> semi <+> ppr ind)

    pprPrec p (StructT s taus _) =
        parensIf (p > tyappPrec) $
        text "struct" <+> ppr s <> pprTyApp taus

    pprPrec p (C tau _) =
        parensIf (p > tyappPrec) $
        text "C" <+> ppr tau

    pprPrec _ (T _) =
        text "T"

    pprPrec p (ST omega tau1 tau2 _) =
        parensIf (p > tyappPrec) $
        text "ST" <+> pprPrec tyappPrec1 omega
                  <+> pprPrec tyappPrec1 tau1
                  <+> pprPrec tyappPrec1 tau2

    pprPrec _ (NatT i _) =
        ppr i

    pprPrec _ (LenT v _) =
        text "length" <> parens (ppr v)

    pprPrec _ (UnopT op tau _) | isFunUnop op =
        ppr op <> parens (ppr tau)

    pprPrec p (UnopT op tau _) =
        unop p op tau

    pprPrec p (BinopT op tau1 tau2 _) =
        infixop p op tau1 tau2

    pprPrec _ UnknownT{} =
        empty

    pprPrec _ (ForallT tvks tau _) =
        pprForall tvks <> ppr tau

    pprPrec _ (TyVarT alpha _) =
        ppr alpha

instance Pretty Kind where
    pprPrec p (TauK ts) = pprPrec p ts
    pprPrec _ NatK      = text "N"

-- | Pretty-print a thing with a type signature
pprTypeSig :: Pretty a => a -> Maybe Type -> Doc
pprTypeSig v Nothing    = ppr v
pprTypeSig v (Just tau) = parens (ppr v <+> colon <+> ppr tau)

-- | Pretty-print a thing with a kind signature
pprKindSig :: Pretty a => (a, Maybe Kind) -> Doc
pprKindSig (tau, Nothing) =
    ppr tau

pprKindSig (tau, Just (TauK traits))
    | nullTraits traits = ppr tau
    | otherwise         = ppr tau <+> colon <+> ppr traits

pprKindSig (tau, Just kappa) =
    parens (ppr tau <+> colon <+> ppr kappa)

pprInitializer :: Maybe Exp -> Doc
pprInitializer Nothing  = empty
pprInitializer (Just e) = text ":=" <+/> ppr e

pprTypeAnn :: Maybe Type -> Doc
pprTypeAnn Nothing    = empty
pprTypeAnn (Just tau) = brackets (ppr tau)

pprRange :: Maybe (Int, Int) -> Doc
pprRange Nothing           = empty
pprRange (Just (from, to)) = brackets (commasep [ppr from, ppr to])

pprForall :: [Tvk] -> Doc
pprForall []   = empty
pprForall tvks = angles $ commasep (map pprKindSig tvks)

-- | Pretty-print a type application. This is used for struct instantiation.
pprTyApp :: [Type] -> Doc
pprTyApp []   = empty
pprTyApp taus = angles $ commasep (map ppr taus)

-- %left '&&' '||'
-- %left '==' '!='
-- %left '|'
-- %left '^'
-- %left '&'
-- %left '<' '<=' '>' '>='
-- %left '<<' '>>'
-- %left '+' '-'
-- %left '*' '/' '%'
-- %left '**'
-- %left 'length'
-- %left '~' 'not' NEG

instance HasFixity Unop where
    fixity Lnot  = infixr_ 12
    fixity Bnot  = infixr_ 12
    fixity Neg   = infixr_ 12
    fixity Abs   = infixr_ 11
    fixity Exp   = infixr_ 11
    fixity Exp2  = infixr_ 11
    fixity Expm1 = infixr_ 11
    fixity Log   = infixr_ 11
    fixity Log2  = infixr_ 11
    fixity Log1p = infixr_ 11
    fixity Sqrt  = infixr_ 11
    fixity Sin   = infixr_ 11
    fixity Cos   = infixr_ 11
    fixity Tan   = infixr_ 11
    fixity Asin  = infixr_ 11
    fixity Acos  = infixr_ 11
    fixity Atan  = infixr_ 11
    fixity Sinh  = infixr_ 11
    fixity Cosh  = infixr_ 11
    fixity Tanh  = infixr_ 11
    fixity Asinh = infixr_ 11
    fixity Acosh = infixr_ 11
    fixity Atanh = infixr_ 11
    fixity Len   = infixr_ 11

instance HasFixity Binop where
    fixity Eq   = infixl_ 2
    fixity Ne   = infixl_ 2
    fixity Lt   = infixl_ 6
    fixity Le   = infixl_ 6
    fixity Ge   = infixl_ 6
    fixity Gt   = infixl_ 6
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
    fixity Pow  = infixl_ 10

#if !defined(ONLY_TYPEDEFS)
{------------------------------------------------------------------------------
 -
 - Types of kind nat
 -
 ------------------------------------------------------------------------------}

instance Num Type where
    NatT x l + NatT y l' = NatT (x+y) (l `srcspan` l')
    tau1     + tau2      = BinopT Add tau1 tau2 (tau1 `srcspan` tau2)

    NatT x l - NatT y l' = NatT (x-y) (l `srcspan` l')
    tau1     - tau2      = BinopT Sub tau1 tau2 (tau1 `srcspan` tau2)

    NatT x l * NatT y l' = NatT (x*y) (l `srcspan` l')
    tau1     * tau2      = BinopT Mul tau1 tau2 (tau1 `srcspan` tau2)

    negate (NatT x l) = NatT (-x) l
    negate tau        = UnopT Neg tau (srclocOf tau)

    abs (NatT x l) = NatT (abs x) l
    abs tau        = UnopT Abs tau (srclocOf tau)

    signum (NatT x l) = NatT (signum x) l
    signum tau        = errordoc $ text "signum: not supported for type" <+>
                                   enquote (ppr tau)

    fromInteger i = NatT (fromInteger i) noLoc

instance Real Type where
    toRational (NatT i _) = toRational i
    toRational tau        = errordoc $ text "toRational: not supported for type" <+>
                                       enquote (ppr tau)

instance Enum Type where
    toEnum i = NatT i noLoc

    fromEnum (NatT i _) = i
    fromEnum tau        = errordoc $ text "fromEnum: not supported for type" <+>
                                     enquote (ppr tau)

instance Integral Type where
    toInteger (NatT i _) = toInteger i
    toInteger tau        = errordoc $ text "toInteger: not supported for type" <+>
                                      enquote (ppr tau)

    NatT x l `quot` NatT y l' = NatT (x `quot` y) (l `srcspan` l')
    tau1     `quot` tau2      = BinopT Div tau1 tau1 (tau1 `srcspan` tau2)

    _ `rem` _ = error "rem: not supported for types"

    x `quotRem` y = (x `quot` y, x `rem` y)

#include "Language/Ziria/Syntax-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
