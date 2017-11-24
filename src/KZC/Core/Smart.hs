{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : KZC.Core.Smart
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Core.Smart (
    module KZC.Expr.Smart,

    letD,
    letrefD,
    letviewD,

    unConstE,
    constE,

    fromIntE,
    fromIdxVarE,

    unitE,
    intE,
    uintE,
    asintE,
    varE,
    notE,
    catE,
    castE,
    bitcastE,
    localdeclE,
    localdeclsE,
    letE,
    letrefE,
    letviewE,
    callE,
    derefE,
    assignE,
    whileE,
    forE,
    arrayE,
    idxE,
    sliceE,
    structE,
    projE,
    returnE,
    bindE,
    seqE,

    startLenGenInt,
    toStartLenGenInt,

    genE,
    genG,
    genrefG,

    expS,
    returnS,

    (.:=.),
    (.>>.),

    isStructD,

    isConstE,
    isArrE,

    sliceLen,

    tagIdentityC,
    isIdentityC,
    identityRateC,

    refPathRoot
  ) where

import Data.Loc
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Core.Syntax
import KZC.Expr.Smart (qualK,
                       tauK,
                       eqK,
                       ordK,
                       boolK,
                       numK,
                       intK,
                       fracK,
                       bitsK,

                       tyVarT,

                       unitT,
                       boolT,
                       bitT,
                       intT,
                       int8T,
                       int16T,
                       int32T,
                       int64T,
                       uintT,
                       uint8T,
                       uint16T,
                       uint32T,
                       uint64T,
                       idxT,
                       refT,
                       unRefT,
                       arrT,
                       arrKnownT,
                       sliceT,
                       structT,
                       stT,
                       forallST,
                       unSTC,
                       funT,
                       unFunT,
                       forallT,

                       isNatK,

                       isBaseT,
                       isUnitT,
                       isBitT,
                       isBitArrT,
                       isFunT,
                       isArrT,
                       isArrOrRefArrT,
                       isRefT,
                       isSTUnitT,
                       isCompT,
                       isPureT,
                       isPureishT,

                       structName,

                       splitArrT,

                       natT,

                       bitC,
                       intC,
                       uintC,
                       idxC,
                       arrayC,
                       structC,

                       isArrC,

                       fromIntC,

                       mkVar,
                       mkStruct)

letD :: Var -> Type -> Exp -> LocalDecl
letD v tau e = LetLD (mkBoundVar v) tau e (v `srcspan` e)

letrefD :: Var -> Type -> Maybe Exp -> LocalDecl
letrefD v tau e = LetRefLD (mkBoundVar v) tau e (v `srcspan` e)

letviewD :: Var -> Type -> Var -> Exp -> Maybe Type -> LocalDecl
letviewD v tau v_arr e_base len =
    LetViewLD (mkBoundVar v) tau view (v `srcspan` view)
  where
    view :: View
    view = IdxVW v_arr e_base len (v_arr `srcspan` e_base)

-- | @'unConstE' e@ returns a constant version of @e@ if possible.
unConstE :: forall m . Monad m => Exp -> m Const
unConstE (ConstE c _) =
    return c

unConstE (CastE tau (ConstE c _) _) | Just c' <- liftCast tau c =
    return c'

unConstE (ArrayE es _) = do
    cs <- mapM unConstE es
    return $ ArrayC $ V.fromList cs

unConstE (StructE s taus flds _) = do
    cs <- mapM unConstE es
    return $ StructC s taus (fs `zip` cs)
  where
    fs :: [Field]
    es :: [Exp]
    (fs, es) = unzip flds

unConstE e =
    faildoc $ text "Expression" <+> ppr e <+> text "is non-constant."

constE :: Const -> Exp
constE c = ConstE c noLoc

fromIntE :: Monad m => Exp -> m Int
fromIntE (ConstE c _) = fromIntC c
fromIntE _            = fail "fromIntE: not an integer"

-- | Return the index variable from an array indexing expression.
fromIdxVarE :: Monad m => Exp -> m Var
fromIdxVarE (VarE v _)             = return v
fromIdxVarE (CastE _ (VarE v _) _) = return v
fromIdxVarE _                      = fail "Not an index variable"

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integral a => a -> Exp
intE i = ConstE (intC i) noLoc

uintE :: Integral a => a -> Exp
uintE i = ConstE (uintC i) noLoc

-- | Create an integer constant expression at the given integer type.
asintE :: Integral a => Type -> a -> Exp
asintE (IntT ip l) i = ConstE (IntC ip (fromIntegral i)) l
asintE tau         _ = errordoc $ text "Expected integer type but got:" <+> ppr tau

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

catE :: Exp -> Exp -> Exp
catE e1 e2 = BinopE Cat e1 e2 (e1 `srcspan` e2)

castE :: Type -> Exp -> Exp
castE tau (ConstE c l) | Just c' <- liftCast tau c =
    ConstE c' l

castE tau e = CastE tau e (srclocOf e)

bitcastE :: Type -> Exp -> Exp
bitcastE tau e = BitcastE tau e (srclocOf e)

localdeclE :: LocalDecl -> Exp -> Exp
localdeclE d e = LetE d e (d `srcspan` e)

localdeclsE :: [LocalDecl] -> Exp -> Exp
localdeclsE ds e = foldr localdeclE e ds

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

letviewE :: Var -> Type -> Var -> Exp -> Maybe Type -> Exp -> Exp
letviewE v tau v_arr e_base len e2 = LetE d e2 (d `srcspan` e2)
  where
    d :: LocalDecl
    d = letviewD v tau v_arr e_base len

callE :: Var -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

assignE :: Exp -> Exp -> Exp
assignE e1 e2 = AssignE e1 e2 (e1 `srcspan` e2)

whileE :: Exp -> Exp -> Exp
whileE e1 e2 = WhileE e1 e2 (e1 `srcspan` e2)

forE :: UnrollAnn -> Var -> Type -> Exp -> Exp -> Exp -> Exp
forE ann v tau e1 e2 e3 = ForE ann v tau (startLenGenInt e1 e2) e3 l
  where
    l = e1 `srcspan` e2 `srcspan` e3

arrayE :: [Exp] -> Exp
arrayE es = ArrayE es (srclocOf es)

idxE :: Exp -> Exp -> Exp
idxE e1 e2 = IdxE e1 (castE idxT e2) Nothing (e1 `srcspan` e2)

sliceE :: Exp -> Exp -> Int -> Exp
sliceE e1 e2 len = IdxE e1 (castE idxT e2) (Just (fromIntegral len)) (e1 `srcspan` e2)

structE :: StructDef -> [Type] -> [(Field, Exp)] -> Exp
structE struct taus fs = StructE struct taus fs (srclocOf (map snd fs))

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

startLenGenInt :: Exp -> Exp -> GenInterval Exp
startLenGenInt e1 e2 = StartLen e1 e2 (e1 `srcspan` e2)

toStartLenGenInt :: GenInterval Exp -> (Exp, Exp)
toStartLenGenInt (FromToInclusive from to _) = (from, to - from + 1)
toStartLenGenInt (FromToExclusive from to _) = (from, to - from)
toStartLenGenInt (StartLen start len _)      = (start, len)

genE :: Exp -> [Gen] -> Exp
genE e gs = GenE e gs (e `srcspan` gs)

genG :: Var -> Type -> Const -> Gen
genG v tau c = GenG v tau c (v `srcspan` tau)

genrefG :: Var -> Type -> Const -> Gen
genrefG v tau c = GenRefG v tau c (v `srcspan` tau)

expS :: Exp -> Stm LocalDecl BoundVar Exp
expS e = ExpS e (srclocOf e)

returnS :: Exp -> Stm LocalDecl BoundVar Exp
returnS e = ReturnS AutoInline e (srclocOf e)

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
isStructD StructD{} = True
isStructD _            = False

isConstE :: Exp -> Bool
isConstE ConstE{} = True
isConstE _        = False

isArrE :: Exp -> Bool
isArrE (ConstE c _) = isArrC c
isArrE ArrayE{}     = True
isArrE _            = False

sliceLen :: Num a => Maybe Type -> a
sliceLen Nothing             = 1
sliceLen (Just (NatT len _)) = fromInteger (toInteger len)
sliceLen (Just nat)          = errordoc $ text "unknown slice length:" <+> ppr nat

-- | Tag a computation as an identity with rate n.
tagIdentityC :: Int -> Comp l -> Comp l
tagIdentityC n comp = comp{compTag = Just (IdT n)}

-- | Return 'True' if computation is an identity computation.
isIdentityC :: Comp l -> Bool
isIdentityC Comp{compTag = Just IdT{}} = True
isIdentityC _                          = False

-- | If a computation is the identityq, return its rate.
identityRateC :: Comp l -> Maybe Int
identityRateC Comp{compTag = Just (IdT n)} = Just n
identityRateC _                            = Nothing

-- | Given an expression of type @ref \tau@, return the source variable of type
-- @ref@.
refPathRoot :: Monad m => Exp -> m Var
refPathRoot (VarE v _)     = return v
refPathRoot (IdxE e _ _ _) = refPathRoot e
refPathRoot (ProjE e _ _)  = refPathRoot e
refPathRoot e              = faildoc $ text "Not a reference:" <+> ppr e
