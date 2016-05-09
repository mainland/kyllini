{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

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

    appendTopDecl,
    getTopDecls,

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
import Control.Monad.Primitive (PrimMonad(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..))
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
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
import Data.Sequence ((|>),
                      Seq)
import Data.Set (Set)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Optimize.Eval.Val
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

data ArgVal l m = ExpAV (Val l m Exp)
                | CompAV (Val l m (Comp l))

deriving instance Eq l => Eq (ArgVal l m)
deriving instance Ord l => Ord (ArgVal l m)
deriving instance Show l => Show (ArgVal l m)

type Theta = Map Var Var

type Phi = Map IVar Iota

type Psi = Map TyVar Type

data EvalEnv l m = EvalEnv
    { varSubst   :: Theta
    , ivarSubst  :: Phi
    , tyVarSubst :: Psi
    , varBinds   :: Map Var (Val l m Exp)
    , cvarBinds  :: Map Var (Val l m (Comp l))
    }

deriving instance Eq l => Eq (EvalEnv l m)
deriving instance Ord l => Ord (EvalEnv l m)
deriving instance Show l => Show (EvalEnv l m)

defaultEvalEnv :: EvalEnv l m
defaultEvalEnv = EvalEnv
    { varSubst   = mempty
    , ivarSubst  = mempty
    , tyVarSubst = mempty
    , varBinds   = mempty
    , cvarBinds  = mempty
    }

data EvalState l m = EvalState
    { topDecls :: !(Seq (Decl l))
    , heapLoc  :: !VarPtr
    , heap     :: !(Heap l m)
    }
  deriving (Eq, Ord, Show)

defaultEvalState :: EvalState l m
defaultEvalState = EvalState
    { topDecls = mempty
    , heapLoc  = 1
    , heap     = mempty
    }

newtype EvalM l m a = EvalM { unEvalM :: ReaderT (EvalEnv l m) (StateT (EvalState l m) m) a }
    deriving (Applicative, Functor, Monad, MonadIO,
              MonadReader (EvalEnv l m),
              MonadState (EvalState l m),
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

deriving instance MonadRef IORef m => MonadRef IORef (EvalM l m)

instance PrimMonad m => PrimMonad (EvalM l m) where
    type PrimState (EvalM l m) = PrimState m
    primitive = EvalM . primitive

instance MonadTrans (EvalM l) where
    lift m = EvalM $ lift $ lift m

deriving instance MonadTcRef m => MonadTcRef (EvalM l m)

evalEvalM :: MonadTc m => EvalM l m a -> m a
evalEvalM m = evalStateT (runReaderT (unEvalM m) defaultEvalEnv) defaultEvalState

partial :: MonadTc m => a -> EvalM l m a
partial x = return x

maybePartialVal :: MonadTc m => Val l m a -> EvalM l m (Val l m a)
maybePartialVal val = return val

partialExp :: MonadTc m => Exp -> EvalM l m (Val l m Exp)
partialExp e = return $ ExpV e

partialCmd :: MonadTc m => Exp -> EvalM l m (Val l m Exp)
partialCmd e = do
    h <- getHeap
    return $ CmdV h e

partialComp :: MonadTc m => Comp l -> EvalM l m (Val l m (Comp l))
partialComp c = do
    h <- getHeap
    return $ CompV h (unComp c)

askSubst :: MonadTc m => EvalM l m Theta
askSubst = asks varSubst

withSubst :: MonadTc m => Theta -> EvalM l m a -> EvalM l m a
withSubst _theta k = k
    --local (\env -> env { varSubst = theta }) k

lookupSubst :: MonadTc m => Var -> EvalM l m (Maybe Var)
lookupSubst v = asks (Map.lookup v . varSubst)

extendSubst :: MonadTc m
            => Var
            -> Var
            -> EvalM l m a
            -> EvalM l m a
extendSubst v v' k =
    local (\env -> env { varSubst = Map.insert v v' (varSubst env) }) k

withUniqVar :: MonadTc m
            => Var
            -> (Var -> EvalM l m a)
            -> EvalM l m a
withUniqVar v k = do
    inscope <- isInScope v
    if inscope
      then do v' <- uniquify v
              extendSubst v v' $ k v'
      else k v

withUniqVars :: MonadTc m
             => [Var]
             -> ([Var] -> EvalM l m a)
             -> EvalM l m a
withUniqVars [] k =
    k []

withUniqVars (v:vs) k =
    withUniqVar  v  $ \v'  ->
    withUniqVars vs $ \vs' ->
    k (v':vs')

withUniqBoundVar :: MonadTc m
                 => BoundVar
                 -> (BoundVar -> EvalM l m a)
                 -> EvalM l m a
withUniqBoundVar v k = do
    inscope <- isInScope (bVar v)
    if inscope
      then do v' <- uniquify v
              extendSubst (bVar v) (bVar v') $ k v'
      else k v

withUniqWildVar :: MonadTc m
                => WildVar
                -> (WildVar -> EvalM l m a)
                -> EvalM l m a
withUniqWildVar WildV     k = k WildV
withUniqWildVar (TameV v) k = withUniqBoundVar v $ \v' -> k (TameV v')

askIVarSubst :: MonadTc m => EvalM l m Phi
askIVarSubst = asks ivarSubst

extendIVarSubst :: MonadTc m
                => [(IVar, Iota)]
                -> EvalM l m a
                -> EvalM l m a
extendIVarSubst ivs m =
    extendEnv ivarSubst (\env x -> env { ivarSubst = x }) ivs m

askTyVarSubst :: MonadTc m => EvalM l m Psi
askTyVarSubst = asks tyVarSubst

extendTyVarSubst :: MonadTc m
                 => [(TyVar, Type)]
                 -> EvalM l m a
                 -> EvalM l m a
extendTyVarSubst ivs m =
    extendEnv tyVarSubst (\env x -> env { tyVarSubst = x }) ivs m

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context.
withInstantiatedTyVars :: MonadTc m
                       => Type
                       -> EvalM l m a
                       -> EvalM l m a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarSubst [(alpha, tau) | (TyVarT alpha _, tau) <-
                                       [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

isInScope :: MonadTc m => Var -> EvalM l m Bool
isInScope v = asks (Map.member v . varBinds)

lookupVarBind :: MonadTc m => Var -> EvalM l m (Val l m Exp)
lookupVarBind v = do
  maybe_val <- asks (Map.lookup v . varBinds)
  case maybe_val of
    Nothing       -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
    Just UnknownV -> partialExp $ varE v
    Just val      -> return val

extendVarBinds :: MonadTc m
               => [(Var, Val l m Exp)]
               -> EvalM l m a
               -> EvalM l m a
extendVarBinds vbs m =
    extendEnv varBinds (\env x -> env { varBinds = x }) vbs m

extendWildVarBinds :: MonadTc m
                   => [(WildVar, Val l m Exp)]
                   -> EvalM l m a
                   -> EvalM l m a
extendWildVarBinds wvbs m =
    extendVarBinds [(bVar v, val) | (TameV v, val) <- wvbs] m

lookupVarValue :: forall l m . MonadTc m
               => Var
               -> EvalM l m (Val l m Exp)
lookupVarValue v =
    lookupVarBind v >>= extract
  where
    extract :: Val l m Exp -> EvalM l m (Val l m Exp)
    extract (RefV (VarR _ ptr)) =
        readVarPtr ptr >>= extract

    extract (ReturnV val) =
        return val

    extract val =
        return val

extendVarValues :: forall l m a . MonadTc m
                => [(Var, Type, Val l m Exp)]
                -> EvalM l m a
                -> EvalM l m a
extendVarValues vbs m =
    savingHeap $ go vbs m
  where
    go :: [(Var, Type, Val l m Exp)] -> EvalM l m a -> EvalM l m a
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

lookupCVarBind :: MonadTc m => Var -> EvalM l m (Val l m (Comp l))
lookupCVarBind v = do
  maybe_val <- asks (Map.lookup v . cvarBinds)
  case maybe_val of
    Nothing  -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
    Just val -> return val

extendCVarBinds :: MonadTc m => [(Var, Val l m (Comp l))] -> EvalM l m a -> EvalM l m a
extendCVarBinds vbs m =
    extendEnv cvarBinds (\env x -> env { cvarBinds = x }) vbs m

-- | Extend the set of variable bindings. The given variables are all specified
-- as having unknown values. We use this when partially evaluating function
-- bodies.
extendUnknownVarBinds :: MonadTc m => [(Var, Type)] -> EvalM l m a -> EvalM l m a
extendUnknownVarBinds vbs m =
    extendVarBinds  [(v, UnknownV)   | (v, _) <- pvbs] $
    extendCVarBinds [(v, CompVarV v) | (v, _) <- ipvbs] $
    m
  where
    pvbs, ipvbs :: [(Var, Type)]
    (pvbs, ipvbs) = partition isPure vbs

    isPure :: (Var, Type) -> Bool
    isPure (_, tau) = isPureT tau

appendTopDecl :: MonadTc m => Decl l -> EvalM l m ()
appendTopDecl decl = modify $ \s -> s { topDecls = topDecls s |> decl }

getTopDecls :: MonadTc m => EvalM l m [Decl l]
getTopDecls = toList <$> gets topDecls

getHeap :: MonadTc m => EvalM l m (Heap l m)
getHeap = gets heap

putHeap :: MonadTc m => Heap l m -> EvalM l m ()
putHeap h = modify $ \s -> s { heap = h }

savingHeap :: MonadTc m => EvalM l m a -> EvalM l m a
savingHeap m = do
    h <- getHeap
    x <- m
    putHeap h
    return x

heapLookup :: MonadTc m => Heap l m -> VarPtr -> EvalM l m (Val l m Exp)
heapLookup h ptr =
    case IntMap.lookup ptr h of
      Nothing  -> faildoc $ text "Unknown variable reference in heap!"
      Just val -> return val

diffHeapExp :: (IsLabel l, MonadTc m) => Heap l m -> Heap l m -> Exp -> EvalM l m Exp
diffHeapExp h h' e =
    foldr seqE e <$> diffHeapExps h h'

diffHeapComp :: (IsLabel l, MonadTc m)
             => Heap l m
             -> Heap l m
             -> Comp l
             -> EvalM l m (Comp l)
diffHeapComp h h' comp = do
    comps_diff <- diffHeapExps h h' >>= mapM liftC
    return $ Comp $ concatMap unComp comps_diff ++ unComp comp

-- | Generate a list of expressions that captures all the heap changes from @h1@
-- to @h2@
diffHeapExps :: forall l m . (IsLabel l, MonadTc m)
             => Heap l m
             -> Heap l m
             -> EvalM l m [Exp]
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
    update :: (Var, Val l m Exp, Val l m Exp) -> Maybe Exp
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


newVarPtr :: MonadTc m => EvalM l m VarPtr
newVarPtr = do
    ptr <- gets heapLoc
    modify $ \s -> s { heapLoc = heapLoc s + 1 }
    return ptr

readVarPtr :: MonadTc m => VarPtr -> EvalM l m (Val l m Exp)
readVarPtr ptr = do
    maybe_val <- gets (IntMap.lookup ptr . heap)
    case maybe_val of
      Nothing  -> faildoc $ text "Unknown variable reference!"
      Just val -> return val

writeVarPtr :: MonadTc m => VarPtr -> Val l m Exp -> EvalM l m ()
writeVarPtr ptr val =
    modify $ \s -> s { heap = IntMap.insert ptr val (heap s) }

killVars :: (ModifiedVars e Var, MonadTc m)
         => e
         -> EvalM l m ()
killVars e = do
    vs       <- mapM (\v -> maybe v id <$> lookupSubst v) (toList (mvs e :: Set Var))
    vbs      <- asks varBinds
    let ptrs =  [ptr | Just (RefV (VarR _ ptr)) <- [Map.lookup v vbs | v <- vs]]
    modify $ \s -> s { heap = foldl' (\m ptr -> IntMap.insert ptr UnknownV m) (heap s) ptrs }

-- | Kill the entire heap. We use this when partially evaluating function
-- bodies.
killHeap :: MonadTc m => EvalM l m a -> EvalM l m a
killHeap m =
    savingHeap $ do
    modify $ \s -> s { heap = IntMap.map (const UnknownV) (heap s) }
    m

simplType :: MonadTc m => Type -> EvalM l m Type
simplType tau = do
    phi <- askTyVarSubst
    psi <- askIVarSubst
    return $ subst psi mempty (subst phi mempty tau)

simplIota :: MonadTc m => Iota -> EvalM l m Iota
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
