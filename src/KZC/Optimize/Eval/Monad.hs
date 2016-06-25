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

    freezeHeap,
    thawHeap,
    savingHeap,
    heapLookup,
    frozenHeapLookup,

    withNewVarPtr,
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
import Control.Monad (forM_,
                      when)
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
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe,
                   mapMaybe)
import Data.Monoid
import Data.Sequence ((|>),
                      Seq)
import Data.Set (Set)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Text.PrettyPrint.Mainland

import KZC.Core.Comp
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Optimize.Eval.Val
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

dEFAULT_HEAP_SIZE :: Int
dEFAULT_HEAP_SIZE = 128

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
    , heap     :: !(Heap l m)
    }

defaultEvalState :: MonadTcRef m => m (EvalState l m)
defaultEvalState = do
    h <- newHeap
    return EvalState { topDecls = mempty
                     , heap     = h
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

evalEvalM :: MonadTcRef m => EvalM l m a -> m a
evalEvalM m = do
    s <- defaultEvalState
    evalStateT (runReaderT (unEvalM m) defaultEvalEnv) s

partial :: MonadTc m => a -> EvalM l m a
partial = return

maybePartialVal :: MonadTc m => Val l m a -> EvalM l m (Val l m a)
maybePartialVal = return

partialExp :: MonadTc m => Exp -> EvalM l m (Val l m Exp)
partialExp = return . ExpV

partialCmd :: MonadTcRef m => Exp -> EvalM l m (Val l m Exp)
partialCmd e = do
    h <- freezeHeap
    return $ CmdV h e

partialComp :: MonadTcRef m => Comp l -> EvalM l m (Val l m (Comp l))
partialComp c = do
    h <- freezeHeap
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
extendSubst v v' =
    local $ \env -> env { varSubst = Map.insert v v' (varSubst env) }

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
extendIVarSubst = extendEnv ivarSubst (\env x -> env { ivarSubst = x })

askTyVarSubst :: MonadTc m => EvalM l m Psi
askTyVarSubst = asks tyVarSubst

extendTyVarSubst :: MonadTc m
                 => [(TyVar, Type)]
                 -> EvalM l m a
                 -> EvalM l m a
extendTyVarSubst = extendEnv tyVarSubst (\env x -> env { tyVarSubst = x })

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
extendVarBinds = extendEnv varBinds (\env x -> env { varBinds = x })

extendWildVarBinds :: MonadTc m
                   => [(WildVar, Val l m Exp)]
                   -> EvalM l m a
                   -> EvalM l m a
extendWildVarBinds wvbs =
  extendVarBinds [(bVar v, val) | (TameV v, val) <- wvbs]

lookupVarValue :: forall l m . MonadTcRef m
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

extendVarValues :: forall l m a . MonadTcRef m
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
        v'  <- fromMaybe v <$> lookupSubst v
        old <- lookupVarBind v'
        case old of
          RefV (VarR _ ptr) ->
              do writeVarPtr ptr val
                 go vbs m
          _ ->
              withNewVarPtr $ \ptr -> do
                 writeVarPtr ptr val
                 extendVarBinds [(v', RefV (VarR v ptr))] $
                   go vbs m

    go ((v, _tau, val):vbs) m = do
        v' <- fromMaybe v <$> lookupSubst v
        extendVarBinds [(v', val)] $
          go vbs m

lookupCVarBind :: MonadTc m => Var -> EvalM l m (Val l m (Comp l))
lookupCVarBind v = do
  maybe_val <- asks (Map.lookup v . cvarBinds)
  case maybe_val of
    Nothing  -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
    Just val -> return val

extendCVarBinds :: MonadTc m => [(Var, Val l m (Comp l))] -> EvalM l m a -> EvalM l m a
extendCVarBinds = extendEnv cvarBinds (\env x -> env { cvarBinds = x })

-- | Extend the set of variable bindings. The given variables are all specified
-- as having unknown values. We use this when partially evaluating function
-- bodies.
extendUnknownVarBinds :: MonadTc m => [(Var, Type)] -> EvalM l m a -> EvalM l m a
extendUnknownVarBinds vbs m =
    extendVarBinds  [(v, UnknownV)   | (v, _) <- pvbs] $
    extendCVarBinds [(v, CompVarV v) | (v, _) <- ipvbs]
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

newHeap :: MonadTcRef m => m (Heap l m)
newHeap = Heap <$> newRef 0 <*> MV.new dEFAULT_HEAP_SIZE

savingHeap :: MonadTcRef m => EvalM l m a -> EvalM l m a
savingHeap m = do
    fh <- freezeHeap
    x  <- m
    thawHeap fh
    return x

freezeHeap :: MonadTcRef m => EvalM l m (FrozenHeap l m)
freezeHeap = do
    h <- gets heap
    FrozenHeap <$> readRef (heapLoc h) <*> V.freeze (heapMem h)

thawHeap :: MonadTcRef m => FrozenHeap l m -> EvalM l m ()
thawHeap fh = do
    h <- Heap <$> newRef (fheapLoc fh) <*> V.thaw (fheapMem fh)
    modify $ \s -> s { heap = h }

heapLookup :: MonadTcRef m
           => Heap l m
           -> VarPtr
           -> EvalM l m (Val l m Exp)
heapLookup h = MV.read (heapMem h)

frozenHeapLookup :: MonadTcRef m
                 => FrozenHeap l m
                 -> VarPtr
                 -> EvalM l m (Val l m Exp)
frozenHeapLookup fh ptr = return $ fheapMem fh V.! ptr

diffHeapExp :: (IsLabel l, MonadTcRef m)
            => FrozenHeap l m
            -> FrozenHeap l m
            -> Exp
            -> EvalM l m Exp
diffHeapExp h h' e =
    foldr seqE e <$> diffHeapExps h h'

diffHeapComp :: (IsLabel l, MonadTcRef m)
             => FrozenHeap l m
             -> FrozenHeap l m
             -> Comp l
             -> EvalM l m (Comp l)
diffHeapComp h h' comp = do
    comps_diff <- diffHeapExps h h' >>= mapM liftC
    return $ mkComp $ concatMap unComp comps_diff ++ unComp comp

-- | Generate a list of expressions that captures all the heap changes from @h1@
-- to @h2@
diffHeapExps :: forall l m . (IsLabel l, MonadTcRef m)
             => FrozenHeap l m
             -> FrozenHeap l m
             -> EvalM l m [Exp]
diffHeapExps h1 h2 = do
    -- Get a list of all variables currently in scope. We assume that this list
    -- contains all variables that may have changed from @h1@ to @h2@. This
    -- assumption will be true unless we try to diff with @h2@ at some point
    -- after a variable in @h2@ has gone out of scope. This should never happen,
    -- since we should only be diffing heaps when we are sequencing actions.
    vvals <- asks (Map.assocs . varBinds)
    return $
        mapMaybe update
        [( v
         , if ptr >= fheapLoc h1 then UnknownV else fheapMem h1 V.! ptr
         , if ptr >= fheapLoc h2 then UnknownV else fheapMem h2 V.! ptr
         ) | (_, RefV (VarR v ptr)) <- vvals]
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

withNewVarPtr :: MonadTcRef m => (VarPtr -> EvalM l m a) -> EvalM l m a
withNewVarPtr k = do
    ref <- gets (heapLoc . heap)
    sz  <- gets (MV.length . heapMem . heap)
    ptr <- readRef ref
    when (ptr >= sz) $ do
      mv  <- gets (heapMem . heap)
      mv' <- MV.grow mv sz
      modify $ \s -> s { heap = Heap ref mv' }
    let ptr' = ptr + 1
    ptr' `seq` writeRef ref ptr'
    x <- k ptr
    writeRef ref ptr
    return x

readVarPtr :: MonadTcRef m => VarPtr -> EvalM l m (Val l m Exp)
readVarPtr ptr = do
    mv <- gets (heapMem . heap)
    MV.read mv ptr

writeVarPtr :: MonadTcRef m => VarPtr -> Val l m Exp -> EvalM l m ()
writeVarPtr ptr val = do
    mv <- gets (heapMem . heap)
    MV.write mv ptr val

killVars :: (ModifiedVars e Var, MonadTcRef m)
         => e
         -> EvalM l m ()
killVars e = do
    vs       <- mapM (\v -> fromMaybe v <$> lookupSubst v)
                     (toList (mvs e :: Set Var))
    vbs      <- asks varBinds
    let ptrs =  [ptr | Just (RefV (VarR _ ptr)) <- [Map.lookup v vbs | v <- vs]]
    mv <- gets (heapMem . heap)
    forM_ ptrs $ \ptr -> MV.write mv ptr UnknownV

-- | Kill the entire heap. We use this when partially evaluating function
-- bodies.
killHeap :: MonadTcRef m => EvalM l m a -> EvalM l m a
killHeap m =
    savingHeap $ do
    sz <- gets (heapLoc . heap) >>= readRef
    mv <- gets (heapMem . heap)
    let loop i | i >= sz   = return ()
               | otherwise = MV.write mv i UnknownV >> loop (i+1)
    loop 0
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
    mvs ConstE{}              = mempty
    mvs VarE{}                = mempty
    mvs UnopE{}               = mempty
    mvs BinopE{}              = mempty
    mvs (IfE _ e2 e3 _)       = mvs e2 <> mvs e3
    mvs (LetE decl body _)    = mvs body <\\> binders decl
    mvs (CallE _ _ es _)      = fvs es
    mvs DerefE{}              = mempty
    mvs (AssignE e1 _ _)      = fvs e1
    mvs (WhileE e1 e2 _)      = mvs e1 <> mvs e2
    mvs (ForE _ _ _ _ _ e3 _) = mvs e3
    mvs ArrayE{}              = mempty
    mvs IdxE{}                = mempty
    mvs StructE{}             = mempty
    mvs ProjE{}               = mempty
    mvs PrintE{}              = mempty
    mvs ErrorE{}              = mempty
    mvs ReturnE{}             = mempty
    mvs (BindE wv _ e1 e2 _)  = mvs e1 <> (mvs e2 <\\> binders wv)
    mvs (LutE e)              = mvs e

instance ModifiedVars Exp v => ModifiedVars [Exp] v where
    mvs = foldMap mvs

instance ModifiedVars (Step l) Var where
    mvs VarC{}                 = mempty
    mvs (CallC _ _ _ es _)     = fvs es
    mvs (IfC _ _ e2 e3 _)      = mvs e2 <> mvs e3
    mvs LetC{}                 = mempty
    mvs (WhileC _ e c _)       = mvs e <> mvs c
    mvs (ForC _ _ _ _ _ _ c _) = mvs c
    mvs (LiftC _ e _)          = mvs e
    mvs ReturnC{}              = mempty
    mvs BindC{}                = mempty
    mvs TakeC{}                = mempty
    mvs TakesC{}               = mempty
    mvs EmitC{}                = mempty
    mvs EmitsC{}               = mempty
    mvs (RepeatC _ _ c _)      = mvs c
    mvs (ParC _ _ e1 e2 _)     = mvs e1 <> mvs e2
    mvs LoopC{}                = mempty

instance ModifiedVars (Comp l) Var where
    mvs comp = go (unComp comp)
      where
        go :: SetLike m Var => [Step l] -> m Var
        go []                          = mempty
        go (BindC _ wv _ _ : k)        = go k <\\> binders wv
        go (LetC _ decl _ : k)         = go k <\\> binders decl
        go (step : k)                  = mvs step <> go k

instance ModifiedVars (Comp l) v => ModifiedVars [Step l] v where
    mvs steps = mvs (mkComp steps)
