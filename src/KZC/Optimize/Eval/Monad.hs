{-# LANGUAGE CPP #-}
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

    lookupVarValue,
    extendVarValues,

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

    simplType,
    simplIota,

    ModifiedVars(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
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
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (foldMap)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Foldable (toList)
import Data.IORef (IORef)
import qualified Data.IntMap as IntMap
import Data.List (foldl',
                  partition)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Monoid
import Data.Set (Set)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Label
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Optimize.Eval.Val
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

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
      then do v' <- uniquify v
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
      then do v' <- uniquify v
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

lookupVarValue :: Var -> EvalM (Val Exp)
lookupVarValue v =
    lookupVarBind v >>= extract
  where
    extract :: Val Exp -> EvalM (Val Exp)
    extract (RefV (VarR _ ptr)) =
        readVarPtr ptr >>= extract

    extract (ReturnV val) =
        return val

    extract val =
        return val

extendVarValues :: [(Var, Type, Val Exp)] -> EvalM a -> EvalM a
extendVarValues vbs m =
    savingHeap $ go vbs m
  where
    go :: [(Var, Type, Val Exp)] -> EvalM a -> EvalM a
    go [] m =
        m

    go ((v, RefT {}, val):vbs) m = do
        v'  <- maybe v id <$> lookupSubst v
        old <- lookupVarBind v'
        case old of
          RefV (VarR _ ptr) ->
              do writeVarPtr ptr val
                 go vbs m
          _ ->
              do ptr <- newVarPtr
                 writeVarPtr ptr val
                 extendVarBinds [(v', RefV (VarR v ptr))] $ do
                 go vbs m

    go ((v, _tau, val):vbs) m = do
        v' <- maybe v id <$> lookupSubst v
        extendVarBinds [(v', val)] $ do
        go vbs m

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

simplType :: Type -> EvalM Type
simplType tau = do
    phi <- askTyVarSubst
    psi <- askIVarSubst
    return $ subst psi mempty (subst phi mempty tau)

simplIota :: Iota -> EvalM Iota
simplIota iota = do
    psi <- askIVarSubst
    return $ subst psi mempty iota

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
    mvs (LutE e)              = mvs e

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
