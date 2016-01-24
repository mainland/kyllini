{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  KZC.Optimize.Eval
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval (
    EvalM,
    evalEvalM,

    evalProgram,
    evalExp,
    toExp
  ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
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
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Bits
import Data.Foldable (toList, foldMap)
import Data.IORef (IORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (foldl')
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
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

data Val a where
    UnknownV :: Val Exp

    UnitV   :: Val Exp
    BoolV   :: !Bool -> Val Exp
    BitV    :: !Bool -> Val Exp
    FixV    :: !Scale -> !Signedness -> !W -> !BP -> !Rational -> Val Exp
    FloatV  :: !FP -> !Rational -> Val Exp
    StringV :: !String -> Val Exp
    StructV :: !Struct -> !(Map Field (Val Exp)) -> Val Exp
    ArrayV  :: !(P.PArray (Val Exp)) -> Val Exp
    RefV    :: Ref -> Val Exp

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
    FunClosV :: !Theta -> ![IVar] -> ![Var] -> Type -> !(EvalM (Val Exp)) -> Val Exp

    -- | A value returned from a computation.
    CompReturnV :: Val Exp -> Val LComp

    -- | A residual computation.
    CompV :: Heap -> [LStep] -> Val LComp

    -- | A computation or computation function we nothing about except its name.
    CompVarV :: Var -> Val LComp

    -- | A computation closure.
    CompClosV :: !Theta -> Type -> !(EvalM (Val LComp)) -> Val LComp

    -- | A computation function closure.
    FunCompClosV :: !Theta -> ![IVar] -> ![Var] -> Type -> !(EvalM (Val LComp)) -> Val LComp

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

newtype EvalM (a :: *) = EvalM { unEvalM :: ReaderT EvalEnv (StateT EvalState KZC) a }
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

isTrue :: Val Exp -> Bool
isTrue (BoolV True) = True
isTrue _            = False

isFalse :: Val Exp -> Bool
isFalse (BoolV False) = True
isFalse _             = False

isZero :: Val Exp -> Bool
isZero (BitV False)     = True
isZero (FixV _ _ _ _ 0) = True
isZero (FloatV _ 0)     = True
isZero _                = False

isOne :: Val Exp -> Bool
isOne (BitV True)      = True
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

evalProgram :: LProgram -> EvalM LProgram
evalProgram (Program decls comp tau) =
  evalDecls decls $ \mkDecls ->
  inSTScope tau $
  inLocalScope $
  withLocContext comp (text "In definition of main") $ do
  val         <- evalComp comp
  (h', comp') <- case val of
                   CompReturnV {}  -> do h'    <- getHeap
                                         comp' <- toComp val
                                         return (h', comp')
                   CompV h' steps' -> return (h', Comp steps')
                   _               -> faildoc $ text "Computation did not return CompReturnV or CompV."
  decls' <- mkDecls h'
  return $ Program decls' comp' tau

evalDecls :: [LDecl] -> ((Heap -> EvalM [LDecl]) -> EvalM a) -> EvalM a
evalDecls [] k =
    k $ \_h -> return []

evalDecls (decl:decls) k =
    evalDecl  decl  $ \mkDecl' ->
    evalDecls decls $ \mkDecls' ->
    k $ \h -> (:) <$> mkDecl' h <*> mkDecls' h

evalDecl :: forall a . LDecl -> ((Heap -> EvalM LDecl) -> EvalM a) -> EvalM a
evalDecl (LetD decl s) k =
    evalLocalDecl decl go
  where
  go :: LocalLetVal -> EvalM a
  go (DeclVal decl') =
      k $ \_h -> return $ LetD decl' s

  go (HeapDeclVal mkDecl) =
      k $ \h -> LetD <$> mkDecl h <*> pure s

evalDecl (LetFunD f ivs vbs tau_ret e l) k = do
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' -> do
    withUniqVars vs $ \vs' -> do
    extendVarBinds [(bVar f', FunClosV theta ivs vs' tau_ret eval)] $ do
    k $ const . return $ LetFunD f' ivs (vs' `zip` taus) tau_ret e l
  where
    tau :: Type
    tau = FunT ivs taus tau_ret l

    vs :: [Var]
    taus :: [Type]
    (vs, taus) = unzip vbs

    eval :: EvalM (Val Exp)
    eval =
        extendIVars (ivs `zip` repeat IotaK) $
        extendVars vbs $
        withInstantiatedTyVars tau_ret $
        withSummaryContext e $
        evalExp e

evalDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(bVar f, tau)] $
    extendVarBinds [(bVar f, UnknownV)] $
    k $ const . return $ LetExtFunD f iotas vbs tau_ret l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

evalDecl (LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k $ const . return $ LetStructD s flds l

evalDecl (LetCompD v tau comp s) k =
    extendVars [(bVar v, tau)] $ do
    theta <- askSubst
    withUniqBoundVar v $ \v' -> do
    extendCVarBinds [(bVar v', CompClosV theta tau eval)] $ do
    k $ const . return $ LetCompD v' tau comp s
  where
    eval :: EvalM (Val LComp)
    eval =
        withInstantiatedTyVars tau $
        withSummaryContext comp $
        uniquifyCompLabels comp >>= evalComp

evalDecl (LetFunCompD f ivs vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' -> do
    withUniqVars vs $ \vs' -> do
    extendCVarBinds [(bVar f', FunCompClosV theta ivs vs' tau_ret eval)] $ do
    k $ const . return $ LetFunCompD f' ivs (vs' `zip` taus) tau_ret comp l
  where
    tau :: Type
    tau = FunT ivs taus tau_ret l

    vs :: [Var]
    taus :: [Type]
    (vs, taus) = unzip vbs

    eval :: EvalM (Val LComp)
    eval =
        withSummaryContext comp $
        extendIVars (ivs `zip` repeat IotaK) $
        extendVars vbs $
        withInstantiatedTyVars tau_ret $
        uniquifyCompLabels comp >>= evalComp

data LocalLetVal -- | Local declaration is pure and produces a declaration
                 = DeclVal LocalDecl
                 -- | Local declaration requires a heap so it can push the heap
                 -- through the declaration.
                 | HeapDeclVal (Heap -> EvalM LocalDecl)

evalLocalDecl :: forall a . LocalDecl -> (LocalLetVal -> EvalM a) -> EvalM a
evalLocalDecl (LetLD v tau e1 s1) k =
    extendVars [(bVar v, tau)] $ do
    -- Bind v to the value of e2
    val1 <- withSummaryContext e1 $ evalExp e1
    withUniqBoundVar v $ \v' -> do
    extendVarBinds [(bVar v', val1)] $ do
    tau' <- simplType tau
    k $ DeclVal $ LetLD v' tau' (toExp val1) s1

evalLocalDecl decl@(LetRefLD v tau maybe_e1 s1) k =
    extendVars [(bVar v, refT tau)] $ do
    withUniqBoundVar v $ \v' -> do
    tau' <- simplType tau
    val1 <- case maybe_e1 of
              Nothing -> defaultValue tau'
              Just e1 -> withSummaryContext e1 $ evalExp e1
    -- Allocate heap storage for v and initialize it
    ptr <- newVarPtr
    writeVarPtr ptr val1
    extendVarBinds [(bVar v', RefV (VarR (bVar v') ptr))] $ do
    k $ HeapDeclVal $ \h ->
        withSummaryContext decl $ do
        tau'      <- simplType tau
        maybe_e1' <- mkInit h ptr val1
        return $ LetRefLD v' tau' maybe_e1' s1
  where
    mkInit :: Heap -> VarPtr -> Val Exp -> EvalM (Maybe Exp)
    mkInit h ptr dflt = do
        val      <- heapLookup h ptr
        let val' =  if isKnown val then val else dflt
        if isDefaultValue val'
          then return Nothing
          else return $ Just (toExp val')

evalComp :: LComp -> EvalM (Val LComp)
evalComp (Comp steps) = evalSteps steps
  where
    evalSteps :: [LStep] -> EvalM (Val LComp)
    evalSteps [] =
        faildoc $ text "Cannot evaluate empty sequence of steps"

    evalSteps [step] =
        evalStep step

    evalSteps (LetC l decl s : steps) = do
        evalLocalDecl decl go
      where
        go :: LocalLetVal -> EvalM (Val LComp)
        go (DeclVal decl') = do
            val <- evalSteps steps
            case val of
              CompV h steps' -> partial $ CompV h $ LetC l decl' s : steps'
              _              -> return val

        go (HeapDeclVal k) = do
            val <- evalSteps steps
            case val of
              CompV h steps' -> do decl' <- k h
                                   partial $ CompV h $ LetC l decl' s : steps'
              _              -> return val

    evalSteps (step:steps) = do
        val <- evalStep step
        case val of
          CompReturnV {} -> evalBind step val steps
          CompV h steps1 -> do steps2 <- evalFullBind steps
                               return $ CompV h (steps1 ++ steps2)
          _              -> faildoc $ text "Step did not return CompReturnV or CompV."

    evalBind :: LStep -> Val LComp -> [LStep] -> EvalM (Val LComp)
    evalBind _step (CompReturnV val1) (BindC l wv tau s : k) =
        extendWildVars [(wv, tau)] $
        withUniqWildVar wv $ \wv' -> do
        extendWildVarBinds [(wv', val1)] $ do
        val <- evalSteps k
        case val of
          CompReturnV {}  -> return val
          CompV h steps2' -> do tau'    <- simplType tau
                                steps1' <- returnC (toExp val1)
                                partial $ CompV h $ unComp steps1' ++ BindC l wv' tau' s : steps2'
          _               -> faildoc $ text "Steps did not return CompReturnV or CompV."

    evalBind _step (CompReturnV _val1) k =
        evalSteps k

    evalBind _step (CompV h1 steps1') (BindC l wv tau s : k) =
        extendWildVars [(wv, tau)] $ do
        withUniqWildVar wv $ \wv' -> do
        killVars steps1'
        tau'    <- simplType tau
        steps2' <- extendWildVarBinds [(wv', UnknownV)] $
                   evalFullSteps k
        partial $ CompV h1 $ steps1' ++ BindC l wv' tau' s : steps2'

    evalBind _step (CompV h1 steps1') k = do
        killVars steps1'
        steps2' <- evalFullSteps k
        partial $ CompV h1 $ steps1' ++ steps2'

    evalBind step _ _ =
        withSummaryContext step $
        faildoc $ text "Command did not return CmdV or ReturnV."

    evalFullBind :: [LStep] -> EvalM [LStep]
    evalFullBind (BindC l wv tau s : steps) =
        extendWildVars [(wv, tau)] $
        withUniqWildVar wv $ \wv' -> do
        tau'   <- simplType tau
        steps' <- extendWildVarBinds [(wv, UnknownV)] $
                  evalFullSteps steps
        return $ BindC l wv' tau' s : steps'

    evalFullBind steps =
        evalFullSteps steps

evalStep :: LStep -> EvalM (Val LComp)
evalStep (VarC _ v _) =
    lookupCVarBind v >>= go
  where
    go :: Val a -> EvalM (Val LComp)
    go (CompClosV theta _tau k) =
        withSubst theta $
        k

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "is not a computation, but we are trying to call it!"

evalStep step@(CallC _ f iotas args _) =
    withSummaryContext step $ do
    maybe_f' <- lookupSubst f
    v_f      <- case maybe_f' of
                  Nothing -> lookupCVarBind f
                  Just f' -> lookupCVarBind f'
    iotas'  <- mapM simplIota iotas
    v_args  <- mapM evalArg args
    go v_f iotas' v_args
  where
    go :: Val a -> [Iota] -> [ArgVal] -> EvalM (Val LComp)
    go (FunCompClosV theta ivs vs _tau_ret k) iotas' v_args =
        withSubst theta $
        extendIVarSubst (ivs `zip` iotas') $
        extendArgBinds  (vs  `zip` v_args) $
        k

    go _val _iotas' _v_es = do
      faildoc $ text "Cannot call computation function" <+> ppr f

    evalArg :: LArg -> EvalM ArgVal
    evalArg (ExpA e)  = ExpAV <$> evalExp e
    evalArg (CompA c) = do tau   <- inferComp c
                           theta <- askSubst
                           return $ CompAV $ CompClosV theta tau (evalComp c)

    extendArgBinds :: [(Var, ArgVal)] -> EvalM a -> EvalM a
    extendArgBinds []                   m = m
    extendArgBinds ((v, ExpAV e):args)  m = extendVarBinds [(v, e)] $
                                            extendArgBinds args m
    extendArgBinds ((v, CompAV c):args) m = extendCVarBinds [(v, c)] $
                                            extendArgBinds args m

evalStep (IfC l e1 c2 c3 s) = do
    h <- getHeap
    evalExp e1 >>= evalIfBody h
  where
    -- Note that @e1@ is pure, so we don't have to worry about it changing the
    -- heap.
    evalIfBody :: Heap -> Val Exp -> EvalM (Val LComp)
    evalIfBody h val
        | isTrue  val = evalComp c2
        | isFalse val = evalComp c3
        | otherwise   = do c2' <- savingHeap $ evalFullSteps $ unComp c2
                           c3' <- savingHeap $ evalFullSteps $ unComp c3
                           killVars c2'
                           killVars c3'
                           partial $ CompV h [IfC l (toExp val) (Comp c2') (Comp c3') s]

evalStep (LetC {}) =
    panicdoc $ text "evalStep: saw LetC"

evalStep (WhileC _ e c _) =
    evalWhile e c

evalStep (ForC _ ann v tau e1 e2 c _) =
    evalFor ann v tau e1 e2 c

evalStep step@(LiftC l e s) = do
    val <- withSummaryContext e $ evalExp e
    case val of
      ReturnV val' -> return $ CompReturnV val'
      CmdV h e'    -> partial $ CompV h [LiftC l e' s]
      _            -> withSummaryContext step $
                      faildoc $ text "Command did not return CmdV or ReturnV."

evalStep (ReturnC l e s) = do
    val <- evalExp e
    case val of
      ExpV e' -> partialComp $ Comp [ReturnC l e' s]
      _       -> return $ CompReturnV val

evalStep (BindC {}) =
    panicdoc $ text "evalStep: saw BindC"

evalStep (TakeC l tau s) = do
    tau' <- simplType tau
    partialComp $ Comp [TakeC l tau' s]

evalStep (TakesC l n tau s) = do
    tau' <- simplType tau
    partialComp $ Comp [TakesC l n tau' s]

evalStep (EmitC l e s) = do
    val <- evalExp e
    partialComp $ Comp [EmitC l (toExp val) s]

evalStep (EmitsC l e s) = do
    val <- evalExp e
    partialComp $ Comp [EmitsC l (toExp val) s]

evalStep (RepeatC l ann c s) = do
    h <- getHeap
    killVars c
    val    <- savingHeap $
              withSummaryContext c $
              evalComp c
    steps' <- toSteps val
    partial $ CompV h $ [RepeatC l ann (Comp steps') s]

evalStep (ParC ann tau c1 c2 s) = do
    h      <- getHeap
    val1   <- withSummaryContext c1 $ evalComp c1
    val2   <- withSummaryContext c2 $ evalComp c2
    steps1 <- toSteps val1
    steps2 <- toSteps val2
    partial $ CompV h $ [ParC ann tau (Comp steps1) (Comp steps2) s]

evalStep (LoopC {}) =
    panicdoc $ text "evalStep: saw LoopC"

-- | Fully evaluate a sequence of steps in the current heap, returning a
-- sequence of steps representing all changes to the heap.
evalFullSteps :: [LStep] -> EvalM [LStep]
evalFullSteps steps = do
    h            <- getHeap
    val          <- evalComp (Comp steps)
    (h', steps') <- case val of
                      CompReturnV {}  -> do h'     <- getHeap
                                            steps' <- toSteps val
                                            return (h', steps')
                      CompV h' steps' -> return (h', steps')
                      _               -> faildoc $ text "Computation did not return CompReturnV or CompV."
    unComp <$> diffHeapComp h h' (Comp steps')

evalFullComp :: LComp -> EvalM LComp
evalFullComp comp = Comp <$> evalFullSteps (unComp comp)

evalConst :: Const -> EvalM (Val Exp)
evalConst UnitC              = return UnitV
evalConst (BoolC f)          = return $ BoolV f
evalConst (BitC f)           = return $ BitV f
evalConst (FixC sc s w bp r) = return $ FixV sc s w bp r
evalConst (FloatC fp r)      = return $ FloatV fp r
evalConst (StringC s)        = return $ StringV s
evalConst c@(ArrayC cs)      = do (_, tau) <- inferConst noLoc c >>= checkArrT
                                  dflt     <- defaultValue tau
                                  (ArrayV . P.fromList dflt) <$> mapM evalConst cs

evalConst (StructC s flds) = do
    vals <- mapM evalConst cs
    return $ StructV s (Map.fromList (fs `zip` vals))
  where
    fs :: [Field]
    cs :: [Const]
    (fs, cs) = unzip  flds

evalExp :: Exp -> EvalM (Val Exp)
evalExp (ConstE c _) =
    evalConst c

evalExp (VarE v _) = do
    maybe_v' <- lookupSubst v
    case maybe_v' of
      Nothing -> lookupVarBind v
      Just v' -> lookupVarBind v'

evalExp (UnopE op e s) = do
    val <- evalExp e
    unop op val
  where
    unop :: Unop -> Val Exp -> EvalM (Val Exp)
    unop Lnot val =
        maybePartialVal $ liftBool op not val

    unop Neg val =
        maybePartialVal $ negate val

    unop (Cast (BitT _)) (FixV _ _ _ (BP 0) r) =
        return $ BitV (r /= 0)

    unop (Cast (FixT sc s w (BP 0) _)) (FixV sc' s' _ (BP 0) r) | sc' == sc && s' == s =
        return $ FixV sc s w (BP 0) r

    unop (Cast (FixT I s w (BP 0) _)) (FloatV _ r) =
        return $ FixV I s w (BP 0) (fromIntegral (truncate r :: Integer))

    unop (Cast (FloatT fp _)) (FixV I _ _ (BP 0) r) =
        return $ FloatV fp r

    unop Len val = do
        (iota, _) <- inferExp e >>= checkArrT
        psi       <- askIVarSubst
        case subst psi mempty iota of
          ConstI n _ -> evalConst $ intC n
          _ -> partialExp $ UnopE op (toExp val) s

    unop op val =
        partialExp $ UnopE op (toExp val) s

evalExp (BinopE op e1 e2 s) = do
    val1 <- evalExp e1
    val2 <- evalExp e2
    binop op val1 val2
  where
    binop :: Binop -> Val Exp -> Val Exp -> EvalM (Val Exp)
    binop Lt val1 val2 =
        maybePartialVal $ liftOrd op (<) val1 val2

    binop Le val1 val2 =
        maybePartialVal $ liftOrd op (<=) val1 val2

    binop Eq val1 val2 =
        maybePartialVal $ liftEq op (==) val1 val2

    binop Ge val1 val2 =
        maybePartialVal $ liftOrd op (>=) val1 val2

    binop Gt val1 val2 =
        maybePartialVal $ liftOrd op (>) val1 val2

    binop Ne val1 val2 =
        maybePartialVal $ liftEq op (/=) val1 val2

    binop Land val1 val2
        | isTrue  val1 = maybePartialVal val2
        | isFalse val1 = return $ BoolV False
        | otherwise    = maybePartialVal $ liftBool2 op (&&) val1 val2

    binop Lor val1 val2
        | isTrue  val1 = return $ BoolV True
        | isFalse val1 = maybePartialVal val2
        | otherwise    = maybePartialVal $ liftBool2 op (||) val1 val2

    binop Band val1 val2 =
        maybePartialVal $ liftBits2 op (.&.) val1 val2

    binop Bor val1 val2
        | isZero val1 = maybePartialVal val2
        | isZero val2 = maybePartialVal val1
        | otherwise   = maybePartialVal $ liftBits2 op (.|.) val1 val2

    binop Bxor val1 val2
        | isZero val1 = maybePartialVal val2
        | isZero val2 = maybePartialVal val1
        | otherwise   = maybePartialVal $ liftBits2 op xor val1 val2

    binop LshL val1 val2 =
        maybePartialVal $ liftShift op shiftL val1 val2

    binop AshR val1 val2 =
        maybePartialVal $ liftShift op shiftR val1 val2

    binop Add val1 val2 = maybePartialVal $ val1 + val2

    binop Sub val1 val2 = maybePartialVal $ val1 - val2

    binop Mul val1 val2 = maybePartialVal $ val1 * val2

    binop Div (FixV I s w (BP 0) r1) (FixV _ _ _ _ r2) =
        return $ FixV I s w (BP 0) (fromIntegral (numerator r1 `quot` numerator r2))

    binop Div (FloatV fp x) (FloatV _ y) =
        return $ FloatV fp (x / y)

    binop Rem (FixV I s w (BP 0) r1) (FixV _ _ _ _ r2) =
        return $ FixV I s w (BP 0) (fromIntegral (numerator r1 `rem` numerator r2))

    binop op val1 val2 =
        partialExp $ BinopE op (toExp val1) (toExp val2) s

evalExp e@(IfE e1 e2 e3 s) = do
    tau <- inferExp e
    h   <- getHeap
    evalExp e1 >>= evalIfExp tau h
  where
    -- Note that @e1@ is pure, so we don't have to worry about it changing the
    -- heap.
    evalIfExp :: Type -> Heap -> Val Exp -> EvalM (Val Exp)
    evalIfExp tau h val
        | isTrue  val = evalExp e2
        | isFalse val = evalExp e3
        | isPureT tau = do val2 <- evalExp e2
                           val3 <- evalExp e3
                           partial $ ExpV $ IfE (toExp val) (toExp val2) (toExp val3) s
        | otherwise   = do e2' <- savingHeap $ evalFullCmd e2
                           e3' <- savingHeap $ evalFullCmd e3
                           killVars e2'
                           killVars e3'
                           partial $ CmdV h $ IfE (toExp val) e2' e3' s

evalExp (LetE decl e2 s2) =
    evalLocalDecl decl go
  where
    go :: LocalLetVal -> EvalM (Val Exp)
    go (DeclVal decl) = do
        val2 <- evalExp e2
        case val2 of
          ExpV e2'   -> partial $ ExpV   $ LetE decl e2' s2
          CmdV h e2' -> partial $ CmdV h $ LetE decl e2' s2
          _          -> return val2

    go (HeapDeclVal k) = do
        val2 <- evalExp e2
        case val2 of
          CmdV h e2' -> do decl <- k h
                           partial $ CmdV h $ LetE decl e2' s2
          _          -> return val2

evalExp e@(CallE f iotas es s) = do
    maybe_f' <- lookupSubst f
    v_f      <- case maybe_f' of
                  Nothing -> lookupVarBind f
                  Just f' -> lookupVarBind f'
    iotas'  <- mapM simplIota iotas
    v_es    <- mapM evalExp es
    tau     <- inferExp e
    go tau v_f iotas' v_es
  where
    go :: Type -> Val Exp -> [Iota] -> [Val Exp] -> EvalM (Val Exp)
    go _tau (FunClosV theta ivs vs _tau_ret k) iotas' v_es =
        withSubst theta $
        extendIVarSubst (ivs `zip` iotas') $
        extendVarBinds  (vs  `zip` v_es) $
        k

    -- Note that the heap cannot change as the result of evaluating function
    -- arguments, so we can call 'partialCmd' here instead of saving the heap
    -- above and constructing a 'CmdV' from it manually.
    go tau (ExpV (VarE f' _)) iotas' v_es
       | isPureT tau = do killVars e
                          partialExp $ CallE f' iotas' (map toExp v_es) s
       | otherwise   = do killVars e
                          partialCmd $ CallE f' iotas' (map toExp v_es) s

    go _tau val _iotas' _v_es = do
      faildoc $ text "Cannot call function" <+> ppr val

evalExp (DerefE e s) =
    evalExp e >>= go
  where
    go :: Val Exp -> EvalM (Val Exp)
    go (RefV r) = do
        val <- readVarPtr ptr
        if isKnown val
          then ReturnV <$> view val
          else partialCmd $ DerefE (toExp r) s
      where
        (ptr, view) = follow r

    go (ExpV e') =
        partialCmd $ DerefE e' s

    go val =
        faildoc $ text "Cannot dereference" <+> ppr val

    -- Given a 'Ref', follow the reference and return a 'VarPtr' where we can
    -- find the root value along with a view function that will give us the
    -- portion of the root value that we want.
    follow :: Ref -> (VarPtr, Val Exp -> EvalM (Val Exp))
    follow (VarR _ ptr) =
        (ptr, return)

    follow (IdxR r i len) =
        (ptr, view')
      where
        (ptr, view) = follow r

        view' :: Val Exp -> EvalM (Val Exp)
        view' val = do val' <- view val
                       evalIdx val' i len

    follow (ProjR r f) = do
        (ptr, view')
      where
        (ptr, view) = follow r

        view' :: Val Exp -> EvalM (Val Exp)
        view' val = do val' <- view val
                       evalProj val' f

evalExp e@(AssignE e1 e2 s) = do
    val1 <- evalExp e1
    val2 <- evalExp e2
    go val1 val2
  where
    go :: Val Exp -> Val Exp -> EvalM (Val Exp)
    go (RefV r) val2 = do
        h         <- getHeap
        old       <- readVarPtr ptr
        maybe_new <- runMaybeT $ update old val2
        case maybe_new of
          Nothing  -> do killVars e
                         partial $ CmdV h $ AssignE (toExp r) (toExp val2) s
          Just new -> do writeVarPtr ptr new
                         return $ ReturnV UnitV
      where
        (ptr, update) = follow r

    go val1 val2 =
        partialCmd $ AssignE (toExp val1) (toExp val2) s

    -- | Given a reference, an accessor, and a value, set the
    follow :: Ref -> (VarPtr, Val Exp -> Val Exp -> MaybeT EvalM (Val Exp))
    follow (VarR _ ptr) =
        (ptr, update)
      where
        update :: Val Exp -> Val Exp -> MaybeT EvalM (Val Exp)
        update _old new = return new

    follow (IdxR r i len) =
        (ptr, update' i len)
      where
        (ptr, update) = follow r

        update' :: Val Exp -> Maybe Int -> Val Exp -> Val Exp -> MaybeT EvalM (Val Exp)
        update' i@(FixV I _ _ (BP 0) r) len@Nothing old@(ArrayV vs) new = do
            old' <- lift $ evalIdx old i len
            new' <- update old' new
            ArrayV <$> vs P.// [(start, new')]
          where
            start :: Int
            start = fromIntegral (numerator r)

        update' i@(FixV I _ _ (BP 0) r) (Just len) old@(ArrayV vs) new = do
            old' <- lift $ evalIdx old i (Just len)
            new' <- update old' new
            case new' of
              ArrayV vs' | P.length vs' == len ->
                  ArrayV <$> vs P.// ([start..start+len-1] `zip` P.toList vs')
              _ ->
                  fail "Cannot update slice with non-ArrayV"
          where
            start :: Int
            start = fromIntegral (numerator r)

        update' _ _ _ _ =
            fail "Cannot take slice of non-ArrayV"

    follow (ProjR r f) =
        (ptr, update' f)
      where
        (ptr, update) = follow r

        update' :: Field -> Val Exp -> Val Exp -> MaybeT EvalM (Val Exp)
        update' f old@(StructV s flds) new = do
            old' <- lift $ evalProj old f
            new' <- update old' new
            return $ StructV s (Map.insert f new' flds)

        update' _ _ _ =
            fail "Cannot project non-StructV"

evalExp (WhileE e1 e2 _) =
    evalWhile e1 e2

evalExp (ForE ann v tau e1 e2 e3 _) =
    evalFor ann v tau e1 e2 e3

evalExp e@(ArrayE es _) = do
    (_, tau) <- inferExp e >>= checkArrT
    dflt     <- defaultValue tau
    vals     <- mapM evalExp es
    return $ ArrayV $ P.fromList dflt vals

evalExp (IdxE arr start len _) = do
    v_arr   <- evalExp arr
    v_start <- evalExp start
    evalIdx v_arr v_start len

evalExp (StructE s flds _) = do
    vals <- mapM evalExp es
    return $ StructV s (Map.fromList (fs `zip` vals))
  where
    fs :: [Field]
    es :: [Exp]
    (fs, es) = unzip  flds

evalExp (ProjE e f _) = do
    val <- evalExp e
    evalProj val f

evalExp (PrintE nl es s) = do
    vals <- mapM evalExp es
    partialCmd $ PrintE nl (map toExp vals) s

evalExp e@(ErrorE {}) =
    partialCmd e

evalExp (ReturnE _ e _) = do
    val <- evalExp e
    case val of
      ExpV e -> partialCmd $ returnE e
      _      -> return $ ReturnV val

evalExp (BindE wv tau e1 e2 s) = do
  val1 <- withSummaryContext e1 $ evalExp e1
  extendWildVars [(wv, tau)] $ do
  withUniqWildVar wv $ \wv' -> do
  case val1 of
    CmdV h1 e1'   -> do killVars e1'
                        tau' <- simplType tau
                        e2'  <- case wv' of
                                  WildV    -> evalFullCmd e2
                                  TameV v' -> extendVarBinds [(bVar v', UnknownV)] $
                                              evalFullCmd e2
                        partial $ CmdV h1 $ BindE wv' tau' e1' e2' s
    ReturnV val1' -> extendWildVarBinds [(wv', val1')] $
                     withSummaryContext e2 $
                     evalExp e2
    _             -> withSummaryContext e1 $
                     faildoc $ text "Command did not return CmdV or ReturnV."

-- | Fully evaluate an expression, which must be an effectful command, in the
-- current heap, and return a single expression representing all changes to the
-- heap. We use this when we need to sequence two commands and the first command
-- produced a residual, meaning we can't push the prefix heap of the second
-- command past the first command.
evalFullCmd :: Exp -> EvalM Exp
evalFullCmd e =
    withSummaryContext e $ do
    h        <- getHeap
    val      <- evalExp e
    (h', e') <- case val of
                  ReturnV {} -> do h' <- getHeap
                                   return (h', toExp val)
                  CmdV h' e' -> return (h', e')
                  _          -> faildoc $ text "Command did not return CmdV or ReturnV." </> ppr val
    diffHeapExp h h' e'

class Eval a where
    eval :: a -> EvalM (Val a)

    returnUnit :: Val a

    residualWhile :: Exp -> a -> EvalM (Val a)

    -- | Construct a residual for loop. The loop bounds have already been
    -- residualized.
    residualFor :: UnrollAnn -> Var -> Type -> Exp -> Exp -> a -> EvalM (Val a)

instance Eval Exp where
    eval =
        evalExp

    returnUnit = ReturnV UnitV

    residualWhile e1 e2 =
        savingHeap $ do
        killVars e1
        killVars e2
        e1' <- evalFullCmd e1
        e2' <- evalFullCmd e2
        partialCmd $ whileE e1' e2'

    residualFor ann v tau e1 e2 e3 =
        savingHeap $
        extendVarBinds [(v, UnknownV)] $ do
        killVars e3
        e3' <- evalFullCmd e3
        partialCmd $ forE ann v tau e1 e2 e3'

instance Eval LComp where
    eval =
        evalComp

    returnUnit =
        CompReturnV UnitV

    residualWhile e c = do
        savingHeap $ do
        killVars e
        killVars c
        e' <- evalFullCmd e
        c' <- evalFullComp c
        whileC e' c' >>= partialComp

    residualFor ann v tau e1 e2 e3 =
        savingHeap $
        extendVarBinds [(v, UnknownV)] $ do
        killVars e3
        e3' <- evalFullComp e3
        forC ann v tau e1 e2 e3' >>= partialComp

evalWhile :: forall a . (ModifiedVars a Var, Eval a)
          => Exp
          -> a
          -> EvalM (Val a)
evalWhile e_cond body = do
    evalLoop body $ evalCond >>= loop
  where
    loop :: Val Exp -> EvalM (Val a)
    loop (ReturnV val) | isTrue val = do
        val2 <- evalBody
        case val2 of
          ReturnV {} -> return val2
          CmdV {}    -> residualWhile e_cond body
          CompV {}   -> residualWhile e_cond body
          _          -> faildoc $ text "Bad body evaluation in while:" <+> ppr val2

    loop (ReturnV val) | isFalse val =
        return $ returnUnit

    loop (CmdV {}) =
        residualWhile e_cond body

    loop val =
        faildoc $ text "Bad condition evaluation in while:" <+> ppr val

    evalCond :: EvalM (Val Exp)
    evalCond = eval e_cond

    evalBody :: EvalM (Val a)
    evalBody = eval body

evalFor :: forall a . (ModifiedVars a Var, Eval a)
        => UnrollAnn
        -> Var
        -> Type
        -> Exp
        -> Exp
        -> a
        -> EvalM (Val a)
evalFor ann v tau e1 e2 body = do
    start <- evalExp e1
    len   <- evalExp e2
    withUniqVar v $ \v' ->
        evalLoop body $
        extendVars [(v, tau)] $
        go v' start len
  where
    go :: Var -> Val Exp -> Val Exp -> EvalM (Val a)
    go v' start@(FixV I _ _ (BP 0) r_start) len@(FixV I _ _ (BP 0) r_len) =
        loop (numerator r_start) (numerator (r_start + r_len))
      where
        loop :: Integer -> Integer -> EvalM (Val a)
        loop !i !end | i == end =
            return $ returnUnit

        loop !i !end = do
            val3 <- extendVarBinds [(v', toIdxVal i)] $ eval body
            case val3 of
              ReturnV {}     -> loop (i+1) end
              CompReturnV {} -> loop (i+1) end
              CmdV {}        -> residualFor ann v' tau (toExp start) (toExp len) body
              CompV {}       -> residualFor ann v' tau (toExp start) (toExp len) body
              _              -> faildoc $ text "Bad body evaluation in for:" <+> ppr val3

    go v' start len =
        residualFor ann v' tau (toExp start) (toExp len) body

    toIdxVal :: Integral i => i -> Val Exp
    toIdxVal i = FixV sc s w bp (fromIntegral i)
      where
        FixT sc s w bp _ = tau

-- | Attempt to execute a loop. If the loop cannot be fully evaluated, we
-- perform the following steps:
--
-- 1) Restore the initial heap.
--
-- 2) Kill all variables that the loop could have been modified by the loop,
-- i.e., the free variables of @body@.
--
-- 3) Return a command consisting of the initial heap and the
-- partially-evaluated loop.
evalLoop :: ModifiedVars e Var => e -> EvalM (Val a) -> EvalM (Val a)
evalLoop body m = do
    h   <- getHeap
    val <- m
    case val of
      ReturnV {}     -> return val
      CompReturnV {} -> return val
      CmdV _ e'      -> do putHeap h
                           killVars body
                           partial $ CmdV h e'
      CompV _ c'     -> do putHeap h
                           killVars body
                           partial $ CompV h c'
      _              -> faildoc $ text "Bad loop:" <+> ppr val

evalIdx :: Val Exp -> Val Exp -> Maybe Int -> EvalM (Val Exp)
evalIdx (RefV r) start len =
    return $ RefV $ IdxR r start len

evalIdx (ArrayV vs) (FixV I _ _ (BP 0) r) Nothing =
    case vs P.!? start of
      Nothing  -> faildoc $ text "Array index out of bounds"
      Just val -> return val
  where
    start :: Int
    start = fromIntegral (numerator r)

evalIdx (ArrayV vs) (FixV I _ _ (BP 0) r) (Just len) =
    ArrayV <$> P.slice start len vs
  where
    start :: Int
    start = fromIntegral (numerator r)

evalIdx val1 val2 len =
    partialExp $ IdxE (toExp val1) (toExp val2) len noLoc

evalProj :: Val Exp -> Field -> EvalM (Val Exp)
evalProj (RefV r) f =
    return $ RefV $ ProjR r f

evalProj (StructV _ kvs) f =
    case Map.lookup f kvs of
      Nothing  -> faildoc $ text "Unknown struct field" <+> ppr f
      Just val -> return val

evalProj val f =
    partialExp $ ProjE (toExp val) f noLoc

-- | Produce a default value of the given type.
defaultValue :: Type -> EvalM (Val Exp)
defaultValue tau =
    go tau
  where
    go :: Type -> EvalM (Val Exp)
    go (UnitT {})         = return UnitV
    go (BoolT {})         = return $ BoolV False
    go (BitT {})          = return $ BitV False
    go (FixT sc s w bp _) = return $ FixV sc s w bp 0
    go (FloatT fp _)      = return $ FloatV fp 0
    go (StringT {})       = return $ StringV ""

    go (StructT s _) = do
        StructDef s flds _ <- lookupStruct s
        let (fs, taus)     =  unzip flds
        vals               <- mapM go taus
        return $ StructV s (Map.fromList (fs `zip` vals))

    go (ArrT (ConstI n _) tau _) = do
        val <- go tau
        return $ ArrayV (P.replicateDefault n val)

    go tau =
        faildoc $ text "Cannot generate default value for type" <+> ppr tau

-- | Given a type and a value, return 'True' if the value is the
-- default of that type and 'False' otherwise.
isDefaultValue :: Val Exp -> Bool
isDefaultValue UnitV            = True
isDefaultValue (BoolV False)    = True
isDefaultValue (BitV False)     = True
isDefaultValue (FixV _ _ _ _ 0) = True
isDefaultValue (FloatV _ 0)     = True
isDefaultValue (StringV "")     = True
isDefaultValue (StructV _ flds) = all isDefaultValue (Map.elems flds)
isDefaultValue (ArrayV vals)    = all isDefaultValue (P.toList vals)
isDefaultValue _                = False

diffHeapExp :: Heap -> Heap -> Exp -> EvalM Exp
diffHeapExp h h' e =
    foldr seqE e <$> diffHeapExps h h'

diffHeapComp :: Heap -> Heap -> LComp -> EvalM LComp
diffHeapComp h h' comp = do
    comps_diff <- diffHeapExps h h' >>= mapM liftC
    return $ Comp $ concatMap unComp comps_diff ++ unComp comp

-- | Return 'True' if a 'Val' is actually a value, 'False' otherwise.
isValue :: Val Exp -> Bool
isValue (BoolV {})       = True
isValue (BitV {})        = True
isValue (FixV {})        = True
isValue (FloatV {})      = True
isValue (StringV {})     = True
isValue (StructV _ flds) = all isValue (Map.elems flds)
isValue (ArrayV vals)    = isValue (P.defaultValue vals) &&
                           all (isValue . snd) (P.nonDefaultValues vals)
isValue _                = False

-- | Return 'True' if a 'Val' is completely known, even if it is a residual,
-- 'False' otherwise.
isKnown :: Val Exp -> Bool
isKnown UnknownV         = False
isKnown (BoolV {})       = True
isKnown (BitV {})        = True
isKnown (FixV {})        = True
isKnown (FloatV {})      = True
isKnown (StringV {})     = True
isKnown (StructV _ flds) = all isKnown (Map.elems flds)
isKnown (ArrayV vals)    = isKnown (P.defaultValue vals) &&
                           all (isKnown . snd) (P.nonDefaultValues vals)
isKnown (ExpV {})        = True
isKnown _                = False

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

    toExp (BitV f) =
        constE $ BitC f

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
    toSteps (CompReturnV val) = do
        unComp <$> returnC (toExp val)

    toSteps (CompV _ steps) =
        return steps

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
    ppr val@(BitV {})    = ppr (toExp val)
    ppr val@(FixV {})    = ppr (toExp val)
    ppr val@(FloatV {})  = ppr (toExp val)
    ppr val@(StringV {}) = ppr (toExp val)
    ppr val@(StructV {}) = ppr (toExp val)
    ppr val@(ArrayV {})  = ppr (toExp val)
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
