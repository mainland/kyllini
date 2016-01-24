-- |
-- Module      : KZC.Auto.Smart
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Auto.Smart (
    module KZC.Auto.Smart,
    isCompT,
    isPureT,
    isPureishT
  ) where

import Control.Applicative (Applicative, (<$>))
import Data.Loc
import Text.PrettyPrint.Mainland

import KZC.Auto.Syntax
import KZC.Core.Smart (isCompT,
                       isPureT,
                       isPureishT)
import KZC.Name
import KZC.Platform
import KZC.Uniq

infixl 1 .>>.
(.>>.) :: Monad m => m (Comp l) -> m (Comp l) -> m (Comp l)
m1 .>>. m2 = do
    m1' <- m1
    m2' <- m2
    return $ m1' <> m2'

mkUniqVar :: (Located a, Applicative m, MonadUnique m) => String -> a -> m Var
mkUniqVar s l = Var <$> mkUniqName s (locOf l)

mkVar :: String -> Var
mkVar s = Var (mkName s noLoc)

intC :: Integral i => i -> Const
intC i = FixC I S dEFAULT_INT_WIDTH 0 (fromIntegral i)

arrayC :: [Const] -> Const
arrayC cs = ArrayC cs

structC :: Struct -> [(Field, Const)] -> Const
structC s fs = StructC s fs

-- | @'isConstE' e@ returns a constant version of @e@ if possible.
unConstE :: Monad m => Exp -> m Const
unConstE (ConstE c _) =
    return c

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

unitE :: Exp
unitE = ConstE UnitC noLoc

intE :: Integer -> Exp
intE i = ConstE (intC i) noLoc

varE :: Var -> Exp
varE v = VarE v (srclocOf v)

notE :: Exp -> Exp
notE e = UnopE Lnot e (srclocOf e)

castE :: Type -> Exp -> Exp
castE tau e = UnopE (Cast tau) e (srclocOf e)

letE :: Var -> Type -> Exp -> Exp -> Exp
letE v tau e1 e2 = LetE d e2 (d `srcspan` e2)
  where
    d :: LocalDecl
    d = LetLD (mkBoundVar v) tau e1 (v `srcspan` e1)

letrefE :: Var -> Type -> Maybe Exp -> Exp -> Exp
letrefE v tau e1 e2 = LetE d e2 (d `srcspan` e2)
  where
    d :: LocalDecl
    d = LetRefLD (mkBoundVar v) tau e1 (v `srcspan` e1)

callE :: Var -> [Exp] -> Exp
callE f es = CallE f [] es (f `srcspan` es)

derefE :: Exp -> Exp
derefE e = DerefE e (srclocOf e)

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

unitT :: Type
unitT = UnitT noLoc

boolT :: Type
boolT = BoolT noLoc

bitT :: Type
bitT = BitT noLoc

intT :: Type
intT = FixT I S dEFAULT_INT_WIDTH 0 noLoc

int8T :: Type
int8T = FixT I S 8 0 noLoc

int16T :: Type
int16T = FixT I S 16 0 noLoc

int32T :: Type
int32T = FixT I S 32 0 noLoc

int64T :: Type
int64T = FixT I S 64 0 noLoc

refT :: Type -> Type
refT tau = RefT tau noLoc

arrKnownT :: Int -> Type -> Type
arrKnownT i tau = ArrT (ConstI i l) tau l
  where
    l :: SrcLoc
    l = srclocOf tau

stT :: Omega -> Type -> Type -> Type -> Type
stT omega s a b = ST [] omega s a b (omega `srcspan` s `srcspan` a `srcspan` b)

tyVarT :: TyVar -> Type
tyVarT alpha = TyVarT alpha noLoc

isComplexT :: Type -> Bool
isComplexT (StructT s _) = isComplexStruct s
isComplexT _             = False

isUnitT :: Type -> Bool
isUnitT (UnitT {}) = True
isUnitT _          = False

isFunT :: Type -> Bool
isFunT (FunT {}) = True
isFunT _         = False

isSTUnitT :: Type -> Bool
isSTUnitT (ST [] (C (UnitT {})) _ _ _ _) = True
isSTUnitT _                              = False

structName :: StructDef -> Struct
structName (StructDef s _ _) = s

splitArrT :: Monad m => Type -> m (Iota, Type)
splitArrT (ArrT iota tau _) =
    return (iota, tau)

splitArrT tau =
    faildoc $ text "Expected array type, but got:" <+> ppr tau
