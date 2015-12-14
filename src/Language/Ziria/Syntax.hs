{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

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

    Scale(..),
    Signedness(..),
    W(..),
    BP(..),
    FP(..),

    Const(..),
    Exp(..),
    VarBind(..),

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

    isComplexStruct
  ) where

import Data.Foldable
import Data.Loc
import Data.Monoid
import Data.Ratio (denominator, numerator)
import Data.String
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Pretty
import KZC.Summary
import KZC.Util.SetLike
import KZC.Vars

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show)

instance IsString Var where
    fromString s = Var $ fromString s

instance Named Var where
    namedSymbol (Var n) = namedSymbol n

    mapName f (Var n) = Var (f n)

newtype Field = Field Name
  deriving (Eq, Ord, Read, Show)

instance IsString Field where
    fromString s = Field $ fromString s

instance Named Field where
    namedSymbol (Field n) = namedSymbol n

    mapName f (Field n) = Field (f n)

newtype Struct = Struct Name
  deriving (Eq, Ord, Read, Show)

instance IsString Struct where
    fromString s = Struct $ fromString s

instance Named Struct where
    namedSymbol (Struct n) = namedSymbol n

    mapName f (Struct n) = Struct (f n)

-- | Fixed point scale factor
data Scale = I
           | PI
  deriving (Eq, Ord, Read, Show)

-- | Fixed point signedness
data Signedness = S
                | U
  deriving (Eq, Ord, Read, Show)

-- | Fixed-point width
data W = WDefault
       | W Int
  deriving (Eq, Ord, Read, Show)

-- | Fixed-point binary point
newtype BP = BP Int
  deriving (Eq, Ord, Read, Show, Num)

-- | Floating-point width
data FP = FP16
        | FP32
        | FP64
  deriving (Eq, Ord, Read, Show)

data Const = UnitC
           | BoolC Bool
           | BitC Bool
           | FixC Scale Signedness W BP Rational
           | FloatC FP Rational
           | StringC String
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp (Maybe Exp) !SrcLoc
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
         | IdxE Exp Exp (Maybe Int) !SrcLoc
         -- Structs Struct
         | StructE Struct [(Field, Exp)] !SrcLoc
         | ProjE Exp Field !SrcLoc
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
         | CompLetE CompLet Exp !SrcLoc
         | StmE [Stm] !SrcLoc
         | CmdE [Cmd] !SrcLoc
  deriving (Eq, Ord, Read, Show)

-- | A variable binding. The boolean is @True@ if the variable is a reference,
-- @False@ otherwise.
data VarBind = VarBind Var Bool Type
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

data Unop = Lnot      -- ^ Logical not
          | Bnot      -- ^ Bitwise not
          | Neg       -- ^ Negation
          | Cast Type -- ^ Type case
          | Len       -- ^ Array length
  deriving (Eq, Ord, Read, Show)

data Binop = Lt   -- ^ Less-than
           | Le   -- ^ Less-than-or-equal
           | Eq   -- ^ Equal
           | Ge   -- ^ Greater-than-or-equal
           | Gt   -- ^ Greater-than
           | Ne   -- ^ Not-equal
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

data CompLet = LetCL Var (Maybe Type) Exp !SrcLoc
             | LetRefCL Var Type (Maybe Exp) !SrcLoc
             | LetFunCL Var (Maybe Type) [VarBind] Exp !SrcLoc
             | LetFunExternalCL Var [VarBind] Type  Bool !SrcLoc
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
          | FixT Scale Signedness W BP !SrcLoc
          | FloatT FP !SrcLoc
          | ArrT Ind Type !SrcLoc
          | StructT Struct !SrcLoc
          | C Type !SrcLoc
          | T !SrcLoc
          | ST Type Type Type !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Ind = ConstI Int !SrcLoc
         | ArrI Var !SrcLoc
         | NoneI !SrcLoc
  deriving (Eq, Ord, Read, Show)

-- | @isComplexStruct s@ is @True@ if @s@ is a complex struct type.
isComplexStruct :: Struct -> Bool
isComplexStruct "complex"   = True
isComplexStruct "complex8"  = True
isComplexStruct "complex16" = True
isComplexStruct "complex32" = True
isComplexStruct "complex64" = True
isComplexStruct _           = False

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
    fvs (ParE _ e1 e2 _)        = fvs e1 <> fvs e2
    fvs (ReadE {})              = mempty
    fvs (WriteE {})             = mempty
    fvs (StandaloneE e _)       = fvs e
    fvs (MapE _ v _ _)          = singleton v
    fvs (FilterE v _ _)         = singleton v
    fvs (CompLetE cl e _)       = fvs cl <> (fvs e <\\> binders cl)
    fvs (StmE stms _)           = fvs stms
    fvs (CmdE cmds _)           = fvs cmds

instance Fvs Exp v => Fvs [Exp] v where
    fvs es = foldMap fvs es

instance Fvs [Stm] Var where
    fvs []                       = mempty
    fvs (LetS v _ e _    : stms) = delete v (fvs e <> fvs stms)
    fvs (LetRefS v _ e _ : stms) = delete v (fvs e <> fvs stms)
    fvs (ExpS e _        : stms) = fvs e <> fvs stms

instance Fvs [Cmd] Var where
    fvs []                     = mempty
    fvs (LetC cl _     : cmds) = fvs cl <> (fvs cmds <\\> binders cl)
    fvs (BindC v _ e _ : cmds) = delete v (fvs e <> fvs cmds)
    fvs (ExpC e _      : cmds) = fvs e <> fvs cmds

instance Fvs CompLet Var where
    fvs cl@(LetCL _ _ e _)            = fvs e <\\> binders cl
    fvs cl@(LetRefCL _ _ e _)         = fvs e <\\> binders cl
    fvs cl@(LetFunCL _ _ _ e _)       = fvs e <\\> binders cl
    fvs (LetFunExternalCL {})         = mempty
    fvs (LetStructCL {})              = mempty
    fvs cl@(LetCompCL _ _ _ e _)      = fvs e <\\> binders cl
    fvs cl@(LetFunCompCL _ _ _ _ e _) = fvs e <\\> binders cl

instance Binders CompLet Var where
    binders (LetCL v _ _ _)               = singleton v
    binders (LetRefCL v _ _ _)            = singleton v
    binders (LetFunCL v _ ps _ _)         = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders (LetFunExternalCL v ps _ _ _) = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders (LetStructCL {})              = mempty
    binders (LetCompCL v _ _ _ _)         = singleton v
    binders (LetFunCompCL v _ _ ps _ _)   = singleton v <> fromList [pv | VarBind pv _ _ <- ps]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary Exp where
    summary e = text "expression:" <+> align (ppr e)

instance Summary StructDef where
    summary (StructDef s _ _) = text "struct" <+> ppr s

instance Summary CompLet where
    summary (LetCL v _ _ _)              = text "definition of" <+> ppr v
    summary (LetRefCL v _ _ _)           = text "definition of" <+> ppr v
    summary (LetFunCL v _ _ _ _)         = text "definition of" <+> ppr v
    summary (LetFunExternalCL v _ _ _ _) = text "definition of" <+> ppr v
    summary (LetStructCL s _)            = text "definition of" <+> summary s
    summary (LetCompCL v _ _ _ _)        = text "definition of" <+> ppr v
    summary (LetFunCompCL v _ _ _ _ _)   = text "definition of" <+> ppr v

instance Summary Stm where
    summary (LetS v _ _ _)    = text "definition of" <+> ppr v
    summary (LetRefS v _ _ _) = text "definition of" <+> ppr v
    summary (ExpS e _)        = summary e

instance Summary Cmd where
    summary (LetC cl _)     = summary cl
    summary (BindC v _ _ _) = text "definition of" <+> ppr v
    summary (ExpC e _)      = summary e

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

instance Pretty FP where
    ppr FP16 = text "16"
    ppr FP32 = text "32"
    ppr FP64 = text "64"

instance Pretty W where
    ppr (W w)    = ppr w
    ppr WDefault = text "<default>"

instance Pretty BP where
    ppr (BP bp) = ppr bp

instance Pretty Const where
    pprPrec _ UnitC              = text "()"
    pprPrec _ (BoolC False)      = text "false"
    pprPrec _ (BoolC True)       = text "true"
    pprPrec _ (BitC False)       = text "'0"
    pprPrec _ (BitC True)        = text "'1"
    pprPrec p (FixC sc s _ bp r) = pprScaled p sc s bp r <> pprSign s
    pprPrec _ (FloatC _ f)       = ppr (fromRational f :: Double)
    pprPrec _ (StringC s)        = text (show s)

pprSign :: Signedness -> Doc
pprSign S = empty
pprSign U = char 'u'

pprScaled :: Int -> Scale -> Signedness -> BP -> Rational -> Doc
pprScaled p I _ (BP 0) r
    | denominator r == 1 = pprPrec p (numerator r)
    | otherwise          = pprPrec p r

pprScaled p sc _ (BP bp) r =
    pprPrec p (fromRational r * scale sc / 2^bp :: Double)
  where
    scale :: Scale -> Double
    scale I  = 1.0
    scale PI = pi

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

    pprPrec p (IfE e1 e2 maybe_e3 _) =
        parensIf (p >= appPrec) $
        text "if"   <+> pprPrec appPrec1 e1 <+/>
        text "then" <+> pprPrec appPrec1 e2 <+/>
        case maybe_e3 of
          Nothing -> empty
          Just e3 -> text "else" <+> pprPrec appPrec1 e3

    pprPrec p (LetE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        nest 2 $
        text "let" <+> pprSig v tau <+>
        text "="   <+>
        ppr e1 <+/> text "in" <+> ppr e2

    pprPrec _ (CallE f vs _) =
        ppr f <> parens (commasep (map ppr vs))

    pprPrec p (LetRefE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        nest 2 $
        text "var" <+> ppr v <+> colon <+> ppr tau <+>
        pprInitializer e1 <+/>
        text "in"  <+> pprPrec appPrec1 e2

    pprPrec _ (AssignE v e _) =
        ppr v <+> text ":=" <+> ppr e

    pprPrec _ (WhileE e1 e2 _) =
        nest 2 $
        text "while" <+> pprPrec appPrec1 e1 <+/>
        pprPrec appPrec1 e2

    pprPrec _ (UntilE e1 e2 _) =
        nest 2 $
        text "until" <+> pprPrec appPrec1 e1 <+/>
        pprPrec appPrec1 e2

    pprPrec _ (TimesE ann e1 e2 _) =
        nest 2 $
        ppr ann <+> text "times" <+> ppr e1 <+/>
        ppr e2

    pprPrec _ (ForE ann v tau e1 e2 e3 _) =
        nest 2 $
        ppr ann <+> text "for" <+> pprSig v tau <+> text "in" <+>
        flatten (brackets (commasep [ppr e1, ppr e2])) <+/>
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
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+> text "|>>>|" <+> pprPrec arrPrec e2

    pprPrec p (ParE _ e1 e2 _) =
        parensIf (p > arrPrec) $
        pprPrec arrPrec e1 <+> text ">>>" <+> pprPrec arrPrec e2

    pprPrec _ (ReadE tau _) =
        text "read" <> pprTypeAnn tau

    pprPrec _ (WriteE tau _) =
        text "write" <> pprTypeAnn tau

    pprPrec _ (StandaloneE e _) =
        text "standalone" <+> ppr e

    pprPrec p (MapE ann v tau _) =
        parensIf (p > appPrec) $
        text "map" <+> ppr ann <+> pprSig v tau

    pprPrec p (FilterE v tau _) =
        parensIf (p > appPrec) $
        text "filter" <+> pprSig v tau

    pprPrec _ (CompLetE cl e _) =
        nest 2 $ ppr cl <+/> text "in" <+/> ppr e

    pprPrec _ (StmE stms _) =
        text "do" <+> ppr stms

    pprPrec _ (CmdE cmds _) =
        ppr cmds

instance Pretty VarBind where
    pprPrec p (VarBind v True tau) =
        parensIf (p > appPrec) $
        text "var" <+> ppr v <+> colon <+> ppr tau

    pprPrec p (VarBind v False tau) =
        parensIf (p > appPrec) $
        ppr v <+> colon <+> ppr tau

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
        nest 2 $
        text "let" <+> pprSig v tau <+> text "=" <+/> ppr e

    ppr (LetRefCL v tau e _) =
        nest 2 $
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    ppr (LetFunCL f tau ps e _) =
        nest 2 $
        text "fun" <+> pprSig f tau <+> parens (commasep (map ppr ps)) <+/> ppr e

    ppr (LetFunExternalCL f ps tau isPure _) =
        nest 2 $
        text "fun" <+> text "external" <+> pureDoc <+>
        ppr f <+> parens (commasep (map ppr ps)) <+> colon <+> ppr tau
      where
        pureDoc = if isPure then empty else text "impure"

    ppr (LetStructCL def _) =
        ppr def

    ppr (LetCompCL v tau range e _) =
        nest 2 $
        text "let" <+> text "comp" <+> pprRange range <+>
        pprSig v tau <+> text "=" <+/> ppr e

    ppr (LetFunCompCL f tau range ps e _) =
        nest 2 $
        text "fun" <+> text "comp" <+> pprRange range <+>
        pprSig f tau <+> parens (commasep (map ppr ps)) <+> text "=" <+/> ppr e

    pprList cls = stack (map ppr cls)

instance Pretty Stm where
    ppr (LetS v tau e _) =
        nest 2 $
        text "let" <+> pprSig v tau <+> text "=" <+> ppr e

    ppr (LetRefS v tau e _) =
        nest 2 $
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    ppr (ExpS e _) =
        ppr e

    pprList stms =
        semiEmbrace (map ppr stms)

instance Pretty Cmd where
    ppr (LetC l _) =
        ppr l

    ppr (BindC v tau e _) =
        pprSig v tau <+> text "<-" <+> ppr e

    ppr (ExpC e _) =
        ppr e

    pprList cmds =
        semiEmbrace (map ppr cmds)

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

    pprPrec _ (FixT sc s w bp _) =
        pprBase sc s <> pprW w bp
      where
        pprBase :: Scale -> Signedness -> Doc
        pprBase I  S = "int"
        pprBase I  U = "uint"
        pprBase PI S = "rad"
        pprBase PI U = "urad"

        pprW :: W -> BP -> Doc
        pprW WDefault (BP 0)  = empty
        pprW WDefault (BP bp) = parens (commasep [text "default", ppr bp])
        pprW (W w)    (BP 0)  = ppr w
        pprW (W w)    (BP bp) = parens (commasep [ppr w, ppr bp])

    pprPrec _ (FloatT FP32 _) =
        text "float"

    pprPrec _ (FloatT FP64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

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

pprSig :: Var -> Maybe Type -> Doc
pprSig v Nothing    = ppr v
pprSig v (Just tau) = parens (ppr v <+> colon <+> ppr tau)

pprInitializer :: Maybe Exp -> Doc
pprInitializer Nothing  = empty
pprInitializer (Just e) = text ":=" <+/> ppr e

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

#if !defined(ONLY_TYPEDEFS)

#include "Language/Ziria/Syntax-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
