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
    Field(..),
    Struct(..),

    IP(..),
    ipWidth,
    ipIsSigned,
    ipIsIntegral,

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

    StructDef(..),
    Type(..),

    isComplexStruct
  ) where

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Loc
import Data.Monoid
import Data.String
import Text.PrettyPrint.Mainland

import KZC.Name
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Uniq
import KZC.Vars

data Dialect = Classic
             | Kyllini
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

newtype Var = Var Name
  deriving (Eq, Ord, Read, Show)

instance IsString Var where
    fromString s = Var $ fromString s

instance Named Var where
    namedSymbol (Var n) = namedSymbol n

    mapName f (Var n) = Var (f n)

instance Gensym Var where
    gensymAt s l = Var <$> gensymAt s (locOf l)

    uniquify (Var n) = Var <$> uniquify n

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

-- | Fixed-point format.
data IP = I (Maybe Int)
        | U (Maybe Int)
  deriving (Eq, Ord, Read, Show)

ipWidth :: IP -> Maybe Int
ipWidth (I w) = w
ipWidth (U w) = w

ipIsSigned :: IP -> Bool
ipIsSigned I{} = True
ipIsSigned U{} = False

ipIsIntegral :: IP -> Bool
ipIsIntegral I{} = True
ipIsIntegral U{} = True

-- | Floating-point width
data FP = FP16
        | FP32
        | FP64
  deriving (Eq, Ord, Read, Show)

data Program = Program [Import] [Decl]
  deriving (Eq, Ord, Read, Show)

data Import = Import ModuleName
  deriving (Eq, Ord, Read, Show)

data Decl = LetD Var (Maybe Type) Exp !SrcLoc
          | LetRefD Var (Maybe Type) (Maybe Exp) !SrcLoc
          | LetFunD Var [VarBind] (Maybe Type) Exp !SrcLoc
          | LetFunExternalD Var [VarBind] Type Bool !SrcLoc
          | LetStructD StructDef !SrcLoc
          | LetCompD Var (Maybe Type) (Maybe (Int, Int)) Exp !SrcLoc
          | LetFunCompD Var (Maybe (Int, Int)) [VarBind] (Maybe Type) Exp !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Const = UnitC
           | BoolC Bool
           | FixC IP Int
           | FloatC FP Double
           | StringC String
  deriving (Eq, Ord, Read, Show)

data Exp = ConstE Const !SrcLoc
         | VarE Var !SrcLoc
         | UnopE Unop Exp !SrcLoc
         | BinopE Binop Exp Exp !SrcLoc
         | IfE Exp Exp (Maybe Exp) !SrcLoc
         | LetE Var (Maybe Type) Exp Exp !SrcLoc
         | LetRefE Var (Maybe Type) (Maybe Exp) Exp !SrcLoc
         | LetDeclE Decl Exp !SrcLoc
         -- Functions
         | CallE Var [Exp] !SrcLoc
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
         | StmE [Stm] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data GenInterval -- | The interval @e1..e2@, /inclusive/ of @e2@.
                 = FromToInclusive Exp Exp !SrcLoc
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

data Unop = Lnot      -- ^ Logical not
          | Bnot      -- ^ Bitwise not
          | Neg       -- ^ Negation
          | Cast Type -- ^ Type case
          | Len       -- ^ Array length
  deriving (Eq, Ord, Read, Show)

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

data StructDef = StructDef Struct [(Field, Type)] !SrcLoc
  deriving (Eq, Ord, Read, Show)

data Type = UnitT !SrcLoc
          | BoolT !SrcLoc
          | FixT IP !SrcLoc
          | FloatT FP !SrcLoc
          | ArrT Type Type !SrcLoc
          | StructT Struct !SrcLoc
          | C Type !SrcLoc
          | T !SrcLoc
          | ST Type Type Type !SrcLoc

          -- | Natural number types
          | NatT Int !SrcLoc

          -- | Reference to array length
          | LenT Var !SrcLoc

          -- | Elided type
          | UnknownT !SrcLoc
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

instance Fvs Decl Var where
    fvs d@(LetD _ _ e _)             = fvs e <\\> binders d
    fvs d@(LetRefD _ _ e _)          = fvs e <\\> binders d
    fvs d@(LetFunD _ _ _ e _)        = fvs e <\\> binders d
    fvs LetFunExternalD{}            = mempty
    fvs LetStructD{}                 = mempty
    fvs d@(LetCompD _ _ _ e _)       = fvs e <\\> binders d
    fvs d@(LetFunCompD  _ _ _ _ e _) = fvs e <\\> binders d

instance Fvs Exp Var where
    fvs ConstE{}              = mempty
    fvs (VarE v _)            = singleton v
    fvs (UnopE _ e _)         = fvs e
    fvs (BinopE _ e1 e2 _)    = fvs e1 <> fvs e2
    fvs (IfE e1 e2 e3 _)      = fvs e1 <> fvs e2 <> fvs e3
    fvs (LetE v _ e1 e2 _)    = delete v (fvs e1 <> fvs e2)
    fvs (LetRefE v _ e1 e2 _) = delete v (fvs e1 <> fvs e2)
    fvs (LetDeclE decl e _)   = fvs decl <> (fvs e <\\> binders decl)
    fvs (CallE v es _)        = singleton v <> fvs es
    fvs (AssignE e1 e2 _)     = fvs e1 <> fvs e2
    fvs (WhileE e1 e2 _)      = fvs e1 <> fvs e2
    fvs (UntilE e1 e2 _)      = fvs e1 <> fvs e2
    fvs (TimesE _ e1 e2 _)    = fvs e1 <> fvs e2
    fvs (ForE _ v _ gint e _) = fvs gint <> delete v (fvs e)
    fvs (ArrayE es _)         = fvs es
    fvs (IdxE e1 e2 _ _)      = fvs e1 <> fvs e2
    fvs (StructE _ flds _)    = fvs (map snd flds)
    fvs (ProjE e _ _)         = fvs e
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
    fvs (StartLen e1 e2 _)        = fvs e1 <> fvs e2

instance Fvs [Stm] Var where
    fvs []                     = mempty
    fvs (LetS d _     : cmds)  = fvs d <> (fvs cmds <\\> binders d)
    fvs (BindS v _ e _ : cmds) = delete v (fvs e <> fvs cmds)
    fvs (ExpS e _      : cmds) = fvs e <> fvs cmds

instance Binders Decl Var where
    binders (LetD v _ _ _)               = singleton v
    binders (LetRefD v _ _ _)            = singleton v
    binders (LetFunD v ps _ _ _)         = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders (LetFunExternalD v ps _ _ _) = singleton v <> fromList [pv | VarBind pv _ _ <- ps]
    binders LetStructD{}                 = mempty
    binders (LetCompD v _ _ _ _)         = singleton v
    binders (LetFunCompD v _ ps _ _ _ )  = singleton v <> fromList [pv | VarBind pv _ _ <- ps]

{------------------------------------------------------------------------------
 -
 - Summaries
 -
 ------------------------------------------------------------------------------}

instance Summary Decl where
    summary (LetD v _ _ _)              = text "definition of" <+> ppr v
    summary (LetRefD v _ _ _)           = text "definition of" <+> ppr v
    summary (LetFunD v _ _ _ _)         = text "definition of" <+> ppr v
    summary (LetFunExternalD v _ _ _ _) = text "definition of" <+> ppr v
    summary (LetStructD s _)            = text "definition of" <+> summary s
    summary (LetCompD v _ _ _ _)        = text "definition of" <+> ppr v
    summary (LetFunCompD v _ _ _ _ _)   = text "definition of" <+> ppr v

instance Summary Exp where
    summary e = text "expression:" <+> align (ppr e)

instance Summary Stm where
    summary (LetS d _)      = summary d
    summary (BindS v _ _ _) = text "definition of" <+> ppr v
    summary (ExpS e _)      = summary e

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
    pprPrec p (LetD v tau e _) =
        parensIf (p > appPrec) $
        text "let" <+> pprSig v tau <+> text "=" <+/> ppr e

    pprPrec p (LetRefD v tau e _) =
        parensIf (p > appPrec) $
        text "var" <+> ppr v <+> colon <+> ppr tau <+> pprInitializer e

    pprPrec _ (LetFunD f ps _tau e _) =
        text "fun" <+> ppr f <> parens (commasep (map ppr ps)) <+> ppr e

    pprPrec _ (LetFunExternalD f ps tau isPure _) =
        text "fun" <+> text "external" <+> pureDoc <+>
        ppr f <+> parens (commasep (map ppr ps)) <+> colon <+> ppr tau
      where
        pureDoc = if isPure then empty else text "impure"

    pprPrec _ (LetStructD def _) =
        ppr def

    pprPrec _ (LetCompD v tau range e _) =
        text "let" <+> text "comp" <+> pprRange range <+>
        pprSig v tau <+> text "=" <+/> ppr e

    pprPrec _ (LetFunCompD f range ps _tau e _) =
        text "fun" <+> text "comp" <+> pprRange range <+>
        ppr f <> parens (commasep (map ppr ps)) <+> ppr e

    pprList cls = stack (map ppr cls)

instance Pretty Const where
    pprPrec _ UnitC                 = text "()"
    pprPrec _ (BoolC False)         = text "false"
    pprPrec _ (BoolC True)          = text "true"
    pprPrec _ (FixC (U (Just 1)) 0) = text "'0"
    pprPrec _ (FixC (U (Just 1)) 1) = text "'1"
    pprPrec _ (FixC I{} x)          = ppr x
    pprPrec _ (FixC U{} x)          = ppr x <> char 'u'
    pprPrec _ (FloatC _ f)          = ppr f
    pprPrec _ (StringC s)           = text (show s)

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
        text "let" <+> pprSig v tau <+>
        text "="   <+>
        ppr e1 <+/> text "in" <+> ppr e2

    pprPrec p (LetRefE v tau e1 e2 _) =
        parensIf (p >= appPrec) $
        text "var" <+> pprSig v tau <+>
        pprInitializer e1 <+/>
        text "in"  <+> pprPrec appPrec1 e2

    pprPrec p (LetDeclE decl e _) =
        parensIf (p >= appPrec) $
        ppr decl <+/> text "in" <+/> ppr e

    pprPrec _ (CallE f vs _) =
        ppr f <> parens (commasep (map ppr vs))

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
        ppr ann <+> text "for" <+> pprSig v tau <+>
        text "in" <+> ppr gint <+/>
        ppr e3

    pprPrec _ (ArrayE es _) =
        text "arr" <+> enclosesep lbrace rbrace comma (map ppr es)

    pprPrec _ (IdxE e1 e2 Nothing _) =
        pprPrec appPrec1 e1 <> brackets (ppr e2)

    pprPrec _ (IdxE e1 e2 (Just i) _) =
        pprPrec appPrec1 e1 <> brackets (commasep [ppr e2, ppr i])

    pprPrec _ (StructE s fields _) =
        ppr s <+> pprStruct comma equals fields

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
        text "map" <+> ppr ann <+> pprSig v tau

    pprPrec p (FilterE v tau _) =
        parensIf (p > appPrec) $
        text "filter" <+> pprSig v tau

    pprPrec _ (StmE stms _) =
        ppr stms

instance Pretty GenInterval where
    ppr (FromToInclusive e1 e2 _) =
        brackets $ ppr e1 <> colon <> ppr e2

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
        vdoc | isRef     = text "var" <+> ppr v
             | otherwise = ppr v

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
        pprSig v tau <+> text "<-" <+> ppr e

    ppr (ExpS e _) =
        ppr e

    pprList cmds =
        embrace (map ppr cmds)

instance Pretty StructDef where
    ppr (StructDef s fields _) =
        align $ nest 2 $
        text "struct" <+> ppr s <+> text "=" <+> pprStruct semi colon fields

instance Pretty Type where
    pprPrec _ (UnitT _) =
        text "()"

    pprPrec _ (BoolT _) =
        text "bool"

    pprPrec _ (FixT (U (Just 1)) _) =
        text "bit"

    pprPrec _ (FixT (I Nothing) _) =
        text "int"

    pprPrec _ (FixT (I (Just w)) _) =
        text "int" <> ppr w

    pprPrec _ (FixT (U Nothing) _) =
        text "uint"

    pprPrec _ (FixT (U (Just w)) _) =
        text "uint" <> ppr w

    pprPrec _ (FloatT FP32 _) =
        text "float"

    pprPrec _ (FloatT FP64 _) =
        text "double"

    pprPrec _ (FloatT w _) =
        text "float" <> ppr w

    pprPrec p (ArrT ind tau _) =
        parensIf (p > tyappPrec) $
        text "arr" <> brackets (ppr ind) <+> ppr tau

    pprPrec p (StructT s _) =
        parensIf (p > tyappPrec) $
        text "struct" <+> ppr s

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

    pprPrec _ UnknownT{} =
        empty

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
-- %left '*' '/' '%'
-- %left '**'
-- %left 'length'
-- %left '~' 'not' NEG

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

instance HasFixity Unop where
    fixity Lnot        = infixr_ 12
    fixity Bnot        = infixr_ 12
    fixity Neg         = infixr_ 12
    fixity Len         = infixr_ 11
    fixity (Cast _)    = infixr_ 10

#if !defined(ONLY_TYPEDEFS)

#include "Language/Ziria/Syntax-instances.hs"

#endif /* !defined(ONLY_TYPEDEFS) */
