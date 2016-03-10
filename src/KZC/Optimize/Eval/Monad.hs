{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  KZC.Optimize.Eval.Monad
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval.Monad (
    Val(..),
    Ref(..),
    VarPtr,
    Heap,
    ArgVal(..),

    EvalM,
    evalEvalM,

    partial,
    maybePartialVal,
    partialExp,
    partialCmd,
    partialComp,

    askSubst,
    withSubst,
    lookupSubst,
    extendSubst,

    withUniqVar,
    withUniqVars,
    withUniqBoundVar,
    withUniqWildVar,

    askIVarSubst,
    extendIVarSubst,

    askTyVarSubst,
    extendTyVarSubst,

    withInstantiatedTyVars,

    isInScope,

    lookupVarBind,
    extendVarBinds,
    extendWildVarBinds,

    lookupCVarBind,
    extendCVarBinds,

    extendUnknownVarBinds,

    getHeap,
    putHeap,
    savingHeap,
    heapLookup,

    newVarPtr,
    readVarPtr,
    writeVarPtr,

    killVars,
    killHeap,

    diffHeapExp,
    diffHeapComp,
    diffHeapExps,

    isTrue,
    isFalse,
    isZero,
    isOne,

    simplType,
    simplIota,

    isValue,
    liftBool,
    liftBool2,
    liftEq,
    liftOrd,
    liftNum,
    liftNum2,
    liftBits,
    liftBits2,
    liftShift,

    ModifiedVars(..),

    ToExp(..),
    ToSteps(..),
    toComp
  ) where

import Control.Applicative (Applicative, (<$>))
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Data.Bits
import Data.Foldable (toList, foldMap)
import Data.IORef (IORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (foldl',
                  partition)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Monoid
import Data.Ratio (numerator)
import Data.Set (Set)
import Data.String (fromString)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Name
import qualified KZC.Optimize.Eval.PArray as P
import KZC.Platform
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

data Val a where
    UnknownV :: Val Exp

    UnitV   :: Val Exp
    BoolV   :: !Bool -> Val Exp
    FixV    :: !Scale -> !Signedness -> !W -> !BP -> !Rational -> Val Exp
    FloatV  :: !FP -> !Rational -> Val Exp
    StringV :: !String -> Val Exp
    StructV :: !Struct -> !(Map Field (Val Exp)) -> Val Exp
    ArrayV  :: !(P.PArray (Val Exp)) -> Val Exp

    -- | An element of an array
    IdxV :: Val Exp -> Val Exp -> Val Exp

    -- | An array slice
    SliceV :: Val Exp -> Val Exp -> Int -> Val Exp

    -- | A Reference
    RefV :: Ref -> Val Exp

    -- | A residual expression.
    ExpV :: Exp -> Val Exp

    -- | A value returned from a monadic action. We need to wrap it in a
    -- 'ReturnV' constructor so that we can convert it to a type-correct
    -- expression later.
    ReturnV :: Val Exp -> Val Exp

    -- | A residual command that cannot be fully evaluated. The 'Heap' argument
    -- is the state of the heap right before the residual expression is
    -- executed.
    CmdV :: Heap -> Exp -> Val Exp

    -- | A function closure
    FunClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM (Val Exp)) -> Val Exp

    -- | A value returned from a computation.
    CompReturnV :: Val Exp -> Val LComp

    -- | A residual computation.
    CompV :: Heap -> [LStep] -> Val LComp

    -- | A computation or computation function we know nothing about except its name.
    CompVarV :: Var -> Val LComp

    -- | A computation closure.
    CompClosV :: !Theta -> Type -> !(EvalM (Val LComp)) -> Val LComp

    -- | A computation function closure.
    FunCompClosV :: !Theta -> ![IVar] -> ![(Var, Type)] -> Type -> !(EvalM (Val LComp)) -> Val LComp

deriving instance Eq (Val a)
deriving instance Ord (Val a)
deriving instance Show (Val a)

instance Num (Val Exp) where
    x + y | isZero x  = y
          | isZero y  = x
          | otherwise = liftNum2 Add (+) x y

    x - y | isZero x  = - y
          | isZero y  = x
          | otherwise = liftNum2 Sub (-) x y

    x * y | isOne x   = y
          | isOne y   = x
          | otherwise = liftNum2 Mul (*) x y

    negate x = liftNum Neg negate x

    fromInteger i = FixV I S dEFAULT_INT_WIDTH (BP 0) (fromInteger i)

    abs _ = error "Val: abs undefined"

    signum _ = error "Val: signum undefined"

data Ref = VarR Var VarPtr
         | IdxR Ref (Val Exp) (Maybe Int)
         | ProjR Ref Field
  deriving (Eq, Ord, Show)

type VarPtr = Int

type Heap = IntMap (Val Exp)

data ArgVal = ExpAV (Val Exp)
            | CompAV (Val LComp)

deriving instance Eq ArgVal
deriving instance Ord ArgVal
deriving instance Show ArgVal

type Theta = Map Var Var

type Phi = Map IVar Iota

type Psi = Map TyVar Type

data EvalEnv = EvalEnv
    { evalTcEnv  :: TcEnv
    , varSubst   :: Theta
    , ivarSubst  :: Phi
    , tyVarSubst :: Psi
    , varBinds   :: Map Var (Val Exp)
    , cvarBinds  :: Map Var (Val LComp)
    }

deriving instance Eq EvalEnv
deriving instance Ord EvalEnv
deriving instance Show EvalEnv

defaultEvalEnv :: TcEnv -> EvalEnv
defaultEvalEnv tcenv = EvalEnv
    { evalTcEnv  = tcenv
    , varSubst   = mempty
    , ivarSubst  = mempty
    , tyVarSubst = mempty
    , varBinds   = mempty
    , cvarBinds  = mempty
    }

data EvalState = EvalState
    { heapLoc :: !VarPtr
    , heap    :: !Heap
    }
  deriving (Eq, Ord, Show)

defaultEvalState :: EvalState
defaultEvalState = EvalState
    { heapLoc = 1
    , heap    = mempty
    }

newtype EvalM a = EvalM { unEvalM :: ReaderT EvalEnv (StateT EvalState KZC) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader EvalEnv,
              MonadState EvalState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

instance MonadTc EvalM where
    askTc       = EvalM $ asks evalTcEnv
    localTc f m = EvalM $ local (\env -> env { evalTcEnv = f (evalTcEnv env) }) (unEvalM m)

evalEvalM :: EvalM a -> TcEnv -> KZC a
evalEvalM m tcenv = evalStateT (runReaderT (unEvalM m) (defaultEvalEnv tcenv)) defaultEvalState

partial :: a -> EvalM a
partial x = return x

maybePartialVal :: Val a -> EvalM (Val a)
maybePartialVal val = return val

partialExp :: Exp -> EvalM (Val Exp)
partialExp e = return $ ExpV e

partialCmd :: Exp -> EvalM (Val Exp)
partialCmd e = do
    h <- getHeap
    return $ CmdV h e

partialComp :: LComp -> EvalM (Val LComp)
partialComp c = do
    h <- getHeap
    return $ CompV h (unComp c)

askSubst :: EvalM Theta
askSubst = asks varSubst

withSubst :: Theta -> EvalM a -> EvalM a
withSubst _theta k = k
    --local (\env -> env { varSubst = theta }) k

lookupSubst :: Var -> EvalM (Maybe Var)
lookupSubst v = asks (Map.lookup v . varSubst)

extendSubst :: Var -> Var -> EvalM a -> EvalM a
extendSubst v v' k =
    local (\env -> env { varSubst = Map.insert v v' (varSubst env) }) k

withUniqVar :: Var
            -> (Var -> EvalM a)
            -> EvalM a
withUniqVar v k = do
    inscope <- isInScope v
    if inscope
      then do v' <- mkUniq v
              extendSubst v v' $ k v'
      else k v

withUniqVars :: [Var]
             -> ([Var] -> EvalM a)
             -> EvalM a
withUniqVars [] k =
    k []

withUniqVars (v:vs) k =
    withUniqVar  v  $ \v'  ->
    withUniqVars vs $ \vs' ->
    k (v':vs')

withUniqBoundVar :: BoundVar
                 -> (BoundVar -> EvalM a)
                 -> EvalM a
withUniqBoundVar v k = do
    inscope <- isInScope (bVar v)
    if inscope
      then do v' <- mkUniq v
              extendSubst (bVar v) (bVar v') $ k v'
      else k v

withUniqWildVar :: WildVar
                -> (WildVar -> EvalM a)
                -> EvalM a
withUniqWildVar WildV     k = k WildV
withUniqWildVar (TameV v) k = withUniqBoundVar v $ \v' -> k (TameV v')

askIVarSubst :: EvalM Phi
askIVarSubst = asks ivarSubst

extendIVarSubst :: [(IVar, Iota)] -> EvalM a -> EvalM a
extendIVarSubst ivs m =
    extendEnv ivarSubst (\env x -> env { ivarSubst = x }) ivs m

askTyVarSubst :: EvalM Psi
askTyVarSubst = asks tyVarSubst

extendTyVarSubst :: [(TyVar, Type)] -> EvalM a -> EvalM a
extendTyVarSubst ivs m =
    extendEnv tyVarSubst (\env x -> env { tyVarSubst = x }) ivs m

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context.
withInstantiatedTyVars :: Type -> EvalM a ->EvalM a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarSubst [(alpha, tau) | (TyVarT alpha _, tau) <-
                                       [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

isInScope :: Var -> EvalM Bool
isInScope v = asks (Map.member v . varBinds)

lookupVarBind :: Var -> EvalM (Val Exp)
lookupVarBind v = do
  maybe_val <- asks (Map.lookup v . varBinds)
  case maybe_val of
    Nothing       -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
    Just UnknownV -> partialExp $ varE v
    Just val      -> return val

extendVarBinds :: [(Var, Val Exp)] -> EvalM a -> EvalM a
extendVarBinds vbs m =
    extendEnv varBinds (\env x -> env { varBinds = x }) vbs m

extendWildVarBinds :: [(WildVar, Val Exp)] -> EvalM a -> EvalM a
extendWildVarBinds wvbs m =
    extendVarBinds [(bVar v, val) | (TameV v, val) <- wvbs] m

lookupCVarBind :: Var -> EvalM (Val LComp)
lookupCVarBind v = do
  maybe_val <- asks (Map.lookup v . cvarBinds)
  case maybe_val of
    Nothing  -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
    Just val -> return val

extendCVarBinds :: [(Var, Val LComp)] -> EvalM a -> EvalM a
extendCVarBinds vbs m =
    extendEnv cvarBinds (\env x -> env { cvarBinds = x }) vbs m

-- | Extend the set of variable bindings. The given variables are all specified
-- as having unknown values. We use this when partially evaluating function
-- bodies.
extendUnknownVarBinds :: [(Var, Type)] -> EvalM a -> EvalM a
extendUnknownVarBinds vbs m =
    extendVarBinds  [(v, UnknownV)   | (v, _) <- pvbs] $
    extendCVarBinds [(v, CompVarV v) | (v, _) <- ipvbs] $
    m
  where
    pvbs, ipvbs :: [(Var, Type)]
    (pvbs, ipvbs) = partition isPure vbs

    isPure :: (Var, Type) -> Bool
    isPure (_, tau) = isPureT tau

getHeap :: EvalM Heap
getHeap = gets heap

putHeap :: Heap -> EvalM ()
putHeap h = modify $ \s -> s { heap = h }

savingHeap :: EvalM a -> EvalM a
savingHeap m = do
    h <- getHeap
    x <- m
    putHeap h
    return x

heapLookup :: Heap -> VarPtr -> EvalM (Val Exp)
heapLookup h ptr =
    case IntMap.lookup ptr h of
      Nothing  -> faildoc $ text "Unknown variable reference in heap!"
      Just val -> return val

diffHeapExp :: Heap -> Heap -> Exp -> EvalM Exp
diffHeapExp h h' e =
    foldr seqE e <$> diffHeapExps h h'

diffHeapComp :: Heap -> Heap -> LComp -> EvalM LComp
diffHeapComp h h' comp = do
    comps_diff <- diffHeapExps h h' >>= mapM liftC
    return $ Comp $ concatMap unComp comps_diff ++ unComp comp

-- | Generate a list of expressions that captures all the heap changes from @h1@
-- to @h2@
diffHeapExps :: Heap -> Heap -> EvalM [Exp]
diffHeapExps h1 h2 = do
    -- Get a list of all variables currently in scope. We assume that this list
    -- contains all variables that may have changed from @h1@ to @h2@. This
    -- assumption will be true unless we try to diff with @h2@ at some point
    -- after a variable in @h2@ has gone out of scope. This should never happen,
    -- since we should only be diffing heaps when we are sequencing actions.
    vvals <- asks (Map.assocs . varBinds)
    return $
        mapMaybe update $
        [(v, maybe UnknownV id (IntMap.lookup ptr h1), maybe UnknownV id (IntMap.lookup ptr h2)) | (_, RefV (VarR v ptr)) <- vvals]
  where
    update :: (Var, Val Exp, Val Exp) -> Maybe Exp
    -- This case occurs when the variable @v@ is killed. If this happens, all
    -- changes to @v@ are captured by the expression in the 'CmdV' associated
    -- with @h2@, so we don't need to do anything.
    update (_v, _old, UnknownV) =
        Nothing

    update (v, UnknownV, val) =
        Just $ v .:=. toExp val

    update (v, val, val')
        | val' == val = Nothing
        | otherwise   = Just $ v .:=. toExp val'


newVarPtr :: EvalM VarPtr
newVarPtr = do
    ptr <- gets heapLoc
    modify $ \s -> s { heapLoc = heapLoc s + 1 }
    return ptr

readVarPtr :: VarPtr -> EvalM (Val Exp)
readVarPtr ptr = do
    maybe_val <- gets (IntMap.lookup ptr . heap)
    case maybe_val of
      Nothing  -> faildoc $ text "Unknown variable reference!"
      Just val -> return val

writeVarPtr :: VarPtr -> Val Exp -> EvalM ()
writeVarPtr ptr val =
    modify $ \s -> s { heap = IntMap.insert ptr val (heap s) }

killVars :: ModifiedVars e Var => e -> EvalM ()
killVars e = do
    vs       <- mapM (\v -> maybe v id <$> lookupSubst v) (toList (mvs e :: Set Var))
    vbs      <- asks varBinds
    let ptrs =  [ptr | Just (RefV (VarR _ ptr)) <- [Map.lookup v vbs | v <- vs]]
    modify $ \s -> s { heap = foldl' (\m ptr -> IntMap.insert ptr UnknownV m) (heap s) ptrs }

-- | Kill the entire heap. We use this when partially evaluating function
-- bodies.
killHeap :: EvalM a -> EvalM a
killHeap m =
    savingHeap $ do
    modify $ \s -> s { heap = IntMap.map (const UnknownV) (heap s) }
    m

isTrue :: Val Exp -> Bool
isTrue (BoolV True) = True
isTrue _            = False

isFalse :: Val Exp -> Bool
isFalse (BoolV False) = True
isFalse _             = False

isZero :: Val Exp -> Bool
isZero (FixV _ _ _ _ 0) = True
isZero (FloatV _ 0)     = True
isZero _                = False

isOne :: Val Exp -> Bool
isOne (FixV _ _ _ _ 1) = True
isOne (FloatV _ 1)     = True
isOne _                = False

simplType :: Type -> EvalM Type
simplType tau = do
    phi <- askTyVarSubst
    psi <- askIVarSubst
    return $ subst psi mempty (subst phi mempty tau)

simplIota :: Iota -> EvalM Iota
simplIota iota = do
    psi <- askIVarSubst
    return $ subst psi mempty iota

-- | Return 'True' if a 'Val Exp' is actually a value and 'False'
-- otherwise.
isValue :: Val Exp -> Bool
isValue UnitV            = True
isValue (BoolV {})       = True
isValue (FixV {})        = True
isValue (FloatV {})      = True
isValue (StringV {})     = True
isValue (StructV _ flds) = all isValue (Map.elems flds)
isValue (ArrayV vals)    = isValue (P.defaultValue vals) &&
                           all (isValue . snd) (P.nonDefaultValues vals)
isValue _                = False

liftBool :: Unop -> (Bool -> Bool) -> Val Exp -> Val Exp
liftBool _ f (BoolV b) =
    BoolV (f b)

liftBool op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftBool2 :: Binop -> (Bool -> Bool -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftBool2 _ f (BoolV x) (BoolV y) =
    BoolV (f x y)

liftBool2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftEq :: Binop -> (forall a . Eq a => a -> a -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftEq _ f val1 val2 | isValue val1 && isValue val2 =
    BoolV (f val1 val2)

liftEq op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftOrd :: Binop -> (forall a . Ord a => a -> a -> Bool) -> Val Exp -> Val Exp -> Val Exp
liftOrd _ f val1 val2 | isValue val1 && isValue val2 =
    BoolV (f val1 val2)

liftOrd op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftNum :: Unop -> (forall a . Num a => a -> a) -> Val Exp -> Val Exp
liftNum _ f (FixV sc s w bp r) =
    FixV sc s w bp (f r)

liftNum _ f (FloatV fp r) =
    FloatV fp (f r)

liftNum op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftNum2 :: Binop -> (forall a . Num a => a -> a -> a) -> Val Exp -> Val Exp -> Val Exp
liftNum2 _ f (FixV sc s w bp r1) (FixV _ _ _ _ r2) =
    FixV sc s w bp (f r1 r2)

liftNum2 _ f (FloatV fp r1) (FloatV _ r2) =
    FloatV fp (f r1 r2)

liftNum2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftBits :: Unop -> (forall a . Bits a => a -> a) -> Val Exp -> Val Exp
liftBits _ f (FixV sc s w (BP 0) r) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r)))

liftBits op _ val =
    ExpV $ UnopE op (toExp val) noLoc

liftBits2 :: Binop -> (forall a . Bits a => a -> a -> a) -> Val Exp -> Val Exp -> Val Exp
liftBits2 _ f (FixV sc s w (BP 0) r1) (FixV _ _ _ _ r2) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r1) (numerator r2)))

liftBits2 op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

liftShift :: Binop -> (forall a . Bits a => a -> Int -> a) -> Val Exp -> Val Exp -> Val Exp
liftShift _ f (FixV sc s w (BP 0) r1) (FixV _ _ _ _ r2) =
    FixV sc s w (BP 0) (fromIntegral (f (numerator r1) (fromIntegral (numerator r2))))

liftShift op _ val1 val2 =
    ExpV $ BinopE op (toExp val1) (toExp val2) noLoc

class ToExp a where
    toExp :: a -> Exp

instance ToExp (Val Exp) where
    toExp UnknownV =
        errordoc $ text "toExp: Cannot convert unknown value to expression"

    toExp UnitV =
        constE UnitC

    toExp (BoolV f) =
        constE $ BoolC f

    toExp (FixV sc s w bp r) =
        constE $ FixC sc s w bp r

    toExp (FloatV fp r) =
        constE $ FloatC fp r

    toExp (StringV s) =
        constE $ StringC s

    toExp (StructV s flds) =
        structE s (fs `zip` map toExp vals)
      where
        fs :: [Field]
        vals :: [Val Exp]
        (fs, vals) = unzip $ Map.assocs flds

    toExp (ArrayV vvals) =
        arrayE (map toExp vals)
      where
        vals :: [Val Exp]
        vals = P.toList vvals

    toExp (IdxV arr i) =
        idxE (toExp arr) (toExp i)

    toExp (SliceV arr start len) =
        sliceE (toExp arr) (toExp start) len

    toExp (RefV r) =
        toExp r

    toExp (ReturnV v) =
        returnE (toExp v)

    toExp (ExpV e) =
        e

    toExp (CmdV _ e) =
        e

    toExp val =
        errordoc $ text "toExp: Cannot convert value to expression:" <+> ppr val

instance ToExp Ref where
    toExp (VarR v _) =
        varE v

    toExp (IdxR r start len) =
        IdxE (toExp r) (toExp start) len noLoc

    toExp (ProjR r f) =
        ProjE (toExp r) f noLoc

class ToSteps a where
    toSteps :: a -> EvalM [LStep]

toComp :: ToSteps a => a -> EvalM LComp
toComp x = Comp <$> toSteps x

instance ToSteps (Val LComp) where
    toSteps (CompReturnV val) =
        unComp <$> returnC (toExp val)

    toSteps (CompV _ steps) =
        return steps

    toSteps (CompVarV v) =
        unComp <$> varC v

    toSteps val =
        faildoc $ text "toSteps: Cannot convert value to steps:" <+> ppr val

class Ord n => ModifiedVars x n where
    mvs :: SetLike m n => x -> m n
    mvs _ = mempty

instance ModifiedVars x n => ModifiedVars (Maybe x) n where
    mvs = foldMap mvs

instance ModifiedVars Exp Var where
    mvs (ConstE {})           = mempty
    mvs (VarE {})             = mempty
    mvs (UnopE {})            = mempty
    mvs (BinopE {})           = mempty
    mvs (IfE _ e2 e3 _)       = mvs e2 <> mvs e3
    mvs (LetE decl body _)    = mvs body <\\> binders decl
    mvs (CallE _ _ es _)      = fvs es
    mvs (DerefE {})           = mempty
    mvs (AssignE e1 _ _)      = fvs e1
    mvs (WhileE e1 e2 _)      = mvs e1 <> mvs e2
    mvs (ForE _ _ _ _ _ e3 _) = mvs e3
    mvs (ArrayE {})           = mempty
    mvs (IdxE {})             = mempty
    mvs (StructE {})          = mempty
    mvs (ProjE {})            = mempty
    mvs (PrintE {})           = mempty
    mvs (ErrorE {})           = mempty
    mvs (ReturnE {})          = mempty
    mvs (BindE wv _ e1 e2 _)  = mvs e1 <> (mvs e2 <\\> binders wv)

instance ModifiedVars Exp v => ModifiedVars [Exp] v where
    mvs es = foldMap mvs es

instance ModifiedVars (Step l) Var where
    mvs (VarC {})              = mempty
    mvs (CallC _ _ _ es _)     = fvs es
    mvs (IfC _ _ e2 e3 _)      = mvs e2 <> mvs e3
    mvs (LetC {})              = mempty
    mvs (WhileC _ e c _)       = mvs e <> mvs c
    mvs (ForC _ _ _ _ _ _ c _) = mvs c
    mvs (LiftC _ e _)          = mvs e
    mvs (ReturnC {})           = mempty
    mvs (BindC {})             = mempty
    mvs (TakeC {})             = mempty
    mvs (TakesC {})            = mempty
    mvs (EmitC {})             = mempty
    mvs (EmitsC {})            = mempty
    mvs (RepeatC _ _ c _)      = mvs c
    mvs (ParC _ _ e1 e2 _)     = mvs e1 <> mvs e2
    mvs (LoopC {})             = mempty

instance ModifiedVars (Comp l) Var where
    mvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                          = mempty
        go (BindC _ wv _ _ : k)        = go k <\\> binders wv
        go (LetC _ decl _ : k)         = go k <\\> binders decl
        go (step : k)                  = mvs step <> go k

instance ModifiedVars (Comp l) v => ModifiedVars [Step l] v where
    mvs steps = mvs (Comp steps)

instance Eq (EvalM (Val a)) where
    (==) = error "EvalM incomparable"

instance Ord (EvalM (Val a)) where
    compare = error "EvalM incomparable"

instance Show (EvalM (Val a)) where
    show _ = "<evaluation action>"

instance Pretty (Val a) where
    ppr UnknownV         = text "<unknown>"
    ppr val@UnitV        = ppr (toExp val)
    ppr val@(BoolV {})   = ppr (toExp val)
    ppr val@(FixV {})    = ppr (toExp val)
    ppr val@(FloatV {})  = ppr (toExp val)
    ppr val@(StringV {}) = ppr (toExp val)
    ppr val@(StructV {}) = ppr (toExp val)
    ppr val@(ArrayV {})  = ppr (toExp val)
    ppr val@(IdxV {})    = ppr (toExp val)
    ppr val@(SliceV {})  = ppr (toExp val)
    ppr (RefV ref)       = ppr ref
    ppr val@(ExpV {})    = ppr (toExp val)
    ppr val@(ReturnV {}) = ppr (toExp val)

    ppr (CmdV h e) =
        nest 2 $ pprPrec appPrec1 e <+> text "with heap" <+/> pprHeap h

    ppr (FunClosV _env ivs vs tau_ret _) =
        langle <> text "fun" <+> ppr ivs <+> ppr vs <+> colon <+> ppr tau_ret <> rangle

    ppr (CompReturnV val) =
        ppr ([ReturnC (fromString "" :: Label) (toExp val) noLoc])

    ppr (CompV h c) =
        nest 2 $ ppr c <> nest (-2) (line <> text "with heap") <+/> pprHeap h

    ppr (CompVarV v) =
        ppr v

    ppr (CompClosV _ tau_ret _) =
        langle <> text "computation" <+> colon <+> ppr tau_ret <> rangle

    ppr (FunCompClosV _env ivs vs tau_ret _) =
        langle <> text "fun comp" <+> ppr ivs <+> ppr vs <+> colon <+> ppr tau_ret <> rangle

instance Pretty Ref where
    ppr = string . show

pprHeap :: Heap -> Doc
pprHeap m = braces $ commasep (map ppr (IntMap.assocs m))
