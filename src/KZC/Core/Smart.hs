{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Core.Smart
-- Copyright   : (c) 2015-2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Smart (
    module KZC.Expr.Smart,

    letD,
    letrefD,

    unConstE,
    constE,

    fromIntE,

    unitE,
    intE,
    varE,
    notE,
    catE,
    castE,
    bitcastE,
    letE,
    letrefE,
    callE,
    derefE,
    assignE,
    whileE,
    forE,
    arrayE,
    structE,
    idxE,
    sliceE,
    projE,
    returnE,
    bindE,
    seqE,

    (.:=.),
    (.>>.),

    isStructD,

    isConstE,
    isArrE,

    refPathRoot
  ) where

import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Core.Syntax
import KZC.Expr.Smart (tyVarT,

                       unitT,
                       boolT,
                       bitT,
                       intT,
                       int8T,
                       int16T,
                       int32T,
                       int64T,
                       refT,
                       unRefT,
                       arrT,
                       arrKnownT,
                       stT,

                       isBaseT,
                       isUnitT,
                       isBitT,
                       isBitArrT,
                       isComplexT,
                       isFunT,
                       isArrT,
                       isRefT,
                       isSTUnitT,
                       isCompT,
                       isPureT,
                       isPureishT,

                       structName,

                       splitArrT,

                       bitC,
                       intC,
                       uintC,
                       arrayC,
                       structC,

                       fromIntC,

                       mkVar)

letD :: Var -> Type -> Exp -> LocalDecl
letD v tau e = LetLD (mkBoundVar v) tau e (v `srcspan` e)

letrefD :: Var -> Type -> Maybe Exp -> LocalDecl
letrefD v tau e = LetRefLD (mkBoundVar v) tau e (v `srcspan` e)

-- | @'unConstE' e@ returns a constant version of @e@ if possible.
unConstE :: forall m . Monad m => Exp -> m Const
unConstE (ConstE c _) =
    return c

unConstE (UnopE (Cast tau) (ConstE c _) _) | Just c' <- liftCast tau c =
    return c'

unConstE (ArrayE es _) = do
    cs <- mapM unConstE es
    return $ ArrayC cs

unConstE (StructE s flds _) = do
    cs <- mapM unConstE es
    return $ StructC s (fs `zip` cs)
  where
    fs :: [Field]
    es :: [Exp]
    (fs, es) = unzip flds

unConstE e =
    faildoc $ text "Expression" <+> ppr e <+> text "is non-constant."

constE :: Const -> Exp
constE c = ConstE c noLoc

fromIntE :: Monad m => Exp -> m Integer
fromIntE (ConstE c _) = fromIntC c
fromIntE _            = fail "fromIntE: not an integer"

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integral a => a -> Exp
intE i = ConstE (intC i) noLoc

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

catE :: Exp -> Exp -> Exp
catE e1 e2 = BinopE Cat e1 e2 (e1 `srcspan` e2)

castE :: Type -> Exp -> Exp
castE tau e = UnopE (Cast tau) e (srclocOf e)

bitcastE :: Type -> Exp -> Exp
bitcastE tau e = UnopE (Bitcast tau) e (srclocOf e)

letE :: Var -> Type -> Exp -> Exp -> Exp
letE v tau e1 e2 = LetE d e2 (v `srcspan` e2)
  where
    d :: LocalDecl
    d = letD v tau e1

letrefE :: Var -> Type -> Maybe Exp -> Exp -> Exp
letrefE v tau e1 e2 = LetE d e2 (d `srcspan` e2)
  where
    d :: LocalDecl
    d = letrefD v tau e1

callE :: Var -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

assignE :: Exp -> Exp -> Exp
assignE e1 e2 = AssignE e1 e2 (e1 `srcspan` e2)

whileE :: Exp -> Exp -> Exp
whileE e1 e2 = WhileE e1 e2 (e1 `srcspan` e2)

forE :: UnrollAnn -> Var -> Type -> Exp -> Exp -> Exp -> Exp
forE ann v tau e1 e2 e3 = ForE ann v tau e1 e2 e3 (e1 `srcspan` e2 `srcspan` e3)

arrayE :: [Exp] -> Exp
arrayE es = ArrayE es (srclocOf es)

structE :: Struct -> [(Field, Exp)] -> Exp
structE s fs = StructE s fs (srclocOf (map snd fs))

idxE :: Exp -> Exp -> Exp
idxE e1 e2 = IdxE e1 e2 Nothing (e1 `srcspan` e2)

sliceE :: Exp -> Exp -> Int -> Exp
sliceE e1 e2 len = IdxE e1 e2 (Just len) (e1 `srcspan` e2)

projE :: Exp -> Field -> Exp
projE e f = ProjE e f (e `srcspan` f)

returnE :: Exp -> Exp
returnE e = ReturnE AutoInline e (srclocOf e)

bindE :: Var -> Type -> Exp -> Exp -> Exp
bindE v tau e1 e2 = BindE (TameV (mkBoundVar v)) tau e1 e2 (v `srcspan` e1 `srcspan` e2)

seqE :: Exp -> Exp -> Exp
seqE (ReturnE _ (ConstE UnitC _) _) e2 =
    e2

seqE e1 e2 =
    BindE WildV unitT e1 e2 (e1 `srcspan` e2)

infixr 1 .:=.

(.:=.) :: Var -> Exp -> Exp
v .:=. e = AssignE (varE v) e (v `srcspan` e)

infixl 1 .>>.

(.>>.) :: Monad m => m (Comp l) -> m (Comp l) -> m (Comp l)
m1 .>>. m2 = do
    m1' <- m1
    m2' <- m2
    return $ m1' <> m2'

isStructD :: Decl l -> Bool
isStructD LetStructD{} = True
isStructD _            = False

isConstE :: Exp -> Bool
isConstE ConstE{} = True
isConstE _        = False

isArrE :: Exp -> Bool
isArrE (ConstE ArrayC{} _) = True
isArrE ArrayE{}            = True
isArrE _                   = False

-- | Given an expression of type @ref \tau@, return the source variable of type
-- @ref@.
refPathRoot :: Monad m => Exp -> m Var
refPathRoot (VarE v _)     = return v
refPathRoot (IdxE e _ _ _) = refPathRoot e
refPathRoot (ProjE e _ _)  = refPathRoot e
refPathRoot e              = faildoc $ text "Not a reference:" <+> ppr e
