{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.FloatViews
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.FloatViews (
    floatViews,
    floatViewsComp
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.List (partition,
                  sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Comp
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Name
import KZC.Util.Error
import KZC.Util.SetLike
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

-- | An array slice starting at the given offset, which is a sum of expressions.
data Slice = Slice Var [Exp] Bool Type
  deriving (Eq, Ord, Show)

instance ToExp Slice where
  toExp (Slice v es _ _) = idxE (varE v) (sum es)

instance Pretty Slice where
    ppr = ppr . toExp

instance Fvs Slice Var where
    fvs (Slice v es _ _) = singleton v <> fvs es

-- | A view of an array slice
data SliceView = SliceView Var Int
  deriving (Eq, Ord, Show)

instance Pretty SliceView where
    ppr (SliceView v i) = ppr v <> brackets (comma <> ppr i)

data FEnv = FEnv { loopVars :: Map Var Int }
  deriving (Eq, Ord, Show)

defaultFEnv :: FEnv
defaultFEnv = FEnv mempty

data FState = FState { views :: Map Slice SliceView }
  deriving (Eq, Ord, Show)

defaultFState :: FState
defaultFState = FState mempty

newtype F m a = F { unF :: ReaderT FEnv (StateT FState m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadReader FEnv,
              MonadState FState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace,
              MonadTc)

instance MonadTrans F where
    lift = F . lift . lift

runF :: MonadTc m => F m a -> m a
runF m = evalStateT (runReaderT (unF m) defaultFEnv) defaultFState

floatViews :: (IsLabel l, MonadTc m) => Program l -> m (Program l)
floatViews = runF . programT

floatViewsComp :: (IsLabel l, MonadTc m) => Comp l -> m (Comp l)
floatViewsComp = runF . compT

lookupLoopVar :: MonadTc m => Var -> F m (Maybe Int)
lookupLoopVar v = asks (Map.lookup v . loopVars)

extendLoopVar :: MonadTc m
              => Var -> Exp -> Exp
              -> F m a
              -> F m a
extendLoopVar v e_i e_len k | Just 0   <- fromIntE e_i,
                              Just len <- fromIntE e_len =
    local (\env -> env { loopVars = Map.insert v (len-1) (loopVars env) }) k

extendLoopVar _ _ _ k =
    k

lookupView :: forall m . MonadTc m => Slice -> Int -> F m (Maybe Var)
lookupView arr@(Slice v es _ _) n
  | shouldViewSlice es = gets (Map.lookup arr . views) >>= go
  | otherwise          = return Nothing
  where
    go :: Maybe SliceView -> F m (Maybe Var)
    go (Just (SliceView v' m)) = do
        when (n > m) $
          modify $ \s -> s { views = Map.insert arr (SliceView v' n) (views s) }
        return $ Just v'

    go Nothing = do
        v' <- gensym (namedString v)
        modify $ \s -> s { views = Map.insert arr (SliceView v' n) (views s) }
        return $ Just v'

    shouldViewSlice :: [Exp] -> Bool
    shouldViewSlice []       = False
    shouldViewSlice [VarE{}] = False
    shouldViewSlice _        = True

withSlices :: forall a m . MonadTc m
           => [Var]
           -> F m a
           -> F m ([LocalDecl], a)
withSlices vs k = do
    (oldStaysInScope, oldShadowed) <- gets (Map.partitionWithKey sliceNotShadowed . views)
    modify $ \s -> s { views = oldStaysInScope }
    x <- k
    (stayInScope, goOutOfScope) <- gets (Map.partitionWithKey sliceNotShadowed . views)
    modify $ \s -> s { views = stayInScope `Map.union` oldShadowed }
    decls <- mapM toLocalDecl $ Map.assocs goOutOfScope
    return (decls, x)
  where
    -- Set of variables going out of scope
    vs' :: Set Var
    vs' = Set.fromList vs

    notShadowed :: forall a . Fvs a Var => a -> Bool
    notShadowed x = Set.null (vs' `Set.intersection` fvs x)

    sliceNotShadowed :: forall a . Slice -> a -> Bool
    sliceNotShadowed slice _ = notShadowed slice

    residualView :: Slice -> Int -> F m (Maybe (Var, [Exp]))
    residualView (Slice v es isRef tau) n = runMaybeT lookupResidualView
      where
        es_stayInScope, es_goOutOfScope :: [Exp]
        (es_stayInScope, es_goOutOfScope) = partition notShadowed es

        lookupResidualView :: MaybeT (F m) (Var, [Exp])
        lookupResidualView = do
            when (v `Set.member` vs' || es_goOutOfScope == es) $
              fail "All expressions going out of scope"
            ks   <- mapM loopFactor es_goOutOfScope
            view <- MaybeT $ lookupView (Slice v es_stayInScope isRef tau) (n + sum ks)
            return (view, es_goOutOfScope)

        loopFactor :: Exp -> MaybeT (F m) Int
        loopFactor (VarE v _) =
            MaybeT $ lookupLoopVar v

        loopFactor (BinopE Mul (VarE v _) e _) | Just j <- fromIntE e = do
            i <- MaybeT $ lookupLoopVar v
            return (i*j)

        loopFactor _ =
            fail "Not a loop variable"

    toLocalDecl :: (Slice, SliceView) -> F m LocalDecl
    toLocalDecl (slice@(Slice v es isRef tau), SliceView v' n) = do
        maybe_view <- residualView slice n
        case maybe_view of
          Just (v'', es') -> return $ letviewD v' tau_v' v'' (sum es') (Just n)
          Nothing         -> return $ letviewD v' tau_v' v (sum es) (Just n)
      where
        tau_v' :: Type
        tau_v' | isRef     = refT $ arrKnownT n tau
               | otherwise = arrKnownT n tau

withSlicesExp :: MonadTc m
              => [Var]
              -> F m Exp
              -> F m Exp
withSlicesExp vs k = do
    (decls, e) <- withSlices vs k
    return $ localdeclsE decls e

withSlicesComp :: (IsLabel l, MonadTc m)
               => [Var]
               -> F m (Comp l)
               -> F m (Comp l)
withSlicesComp vs k = do
    (decls, comp) <- withSlices vs k
    cdecls        <- localdeclsC decls
    return $ cdecls <> comp

unSlice :: Exp -> Maybe ([Exp], Int)
unSlice e = do
    (es, i) <- go e
    return (sort es, i)
  where
    go :: Exp -> Maybe ([Exp], Int)
    go e | Just i <- fromIntE e =
        return ([], i)

    go (BinopE Add e1 e2 _) = do
        (es1, i) <- go e1
        (es2, j) <- go e2
        return (es1++es2, i+j)

    go e =
        return ([e], 0)

instance MonadTc m => TransformExp (F m) where
    expT (LetE decl e s) = do
        (decl', e') <- localDeclT decl $
                       withSlicesExp (binders decl) $
                       expT e
        return $ LetE decl' e' s

    expT e@CallE{} =
        return e

    expT (ForE ann v tau e1 e2 e3 s) = do
        e1' <- expT e1
        e2' <- expT e2
        e3' <- extendVars [(v, tau)] $
               extendLoopVar v e1 e2 $
               withSlicesExp [v] $
               expT e3
        return $ ForE ann v tau e1' e2' e3' s

    expT e@(IdxE (VarE v _) e2 len s)
      | Just (es, i) <- unSlice e2 = do
        (isRef, tau) <- lookupVar v >>= viewType
        maybe_v'     <- lookupView (Slice v es isRef tau) (i + fromMaybe 1 len)
        case maybe_v' of
          Nothing -> return e
          Just v' -> return $ IdxE (varE v') (intE i) len s
      where
        viewType :: Type -> F m (Bool, Type)
        viewType (ArrT _ tau _) =
            return (False, tau)

        viewType (RefT (ArrT _ tau _) _) =
            return (True, tau)

        viewType tau =
            faildoc $ nest 2 $ group $
            text "Expected array type but got:" <+/> ppr tau

    expT (BindE (TameV v) tau e1 e2 s) = do
        e1' <- expT e1
        e2' <- extendVars [(bVar v, tau)] $
               withSlicesExp [bVar v] $
               expT e2
        return $ BindE (TameV v) tau e1' e2' s

    expT e = transExp e

instance (IsLabel l, MonadTc m) => TransformComp l (F m) where
    declsT (LetD ldecl s : decls) k = do
        (ldecl', (ldecls', (decls', x))) <-
            localDeclT ldecl $
            withSlices (binders ldecl) $
            declsT decls k
        return ([LetD ldecl s | ldecl <- ldecl' : ldecls'] ++ decls', x)

    declsT decls k = transDecls decls k

    declT (LetFunD f iotas vbs tau_ret e l) m =
        extendVars [(bVar f, tau)] $ do
        e' <- extendLetFun f iotas vbs tau_ret $
              withSlicesExp (map fst vbs) $
              expT e
        x  <- m
        return (LetFunD f iotas vbs tau_ret e' l, x)
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    declT (LetFunCompD f iotas vbs tau_ret comp l) m =
        extendVars [(bVar f, tau)] $ do
        comp' <- extendLetFun f iotas vbs tau_ret $
                 withSlicesComp (map fst vbs) $
                 compT comp
        x     <- m
        return (LetFunCompD f iotas vbs tau_ret comp' l, x)
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    declT decl m = transDecl decl m

    stepsT (LetC l decl s : steps) = do
        (decl', comp') <- localDeclT decl $
                           withSlicesComp (binders decl) $
                           mkComp <$> stepsT steps
        return $ LetC l decl' s : unComp comp'

    stepsT (BindC l (TameV v) tau s : steps) = do
        comp' <- extendVars [(bVar v, tau)] $
                 withSlicesComp [bVar v] $
                 mkComp <$> stepsT steps
        return $ BindC l (TameV v) tau s : unComp comp'

    stepsT steps = transSteps steps

    stepT step@CallC{} =
        return step

    stepT (ForC l ann v tau e1 e2 c3 s) = do
        e1' <- expT e1
        e2' <- expT e2
        c3' <- extendVars [(v, tau)] $
               extendLoopVar v e1 e2 $
               withSlicesComp [v] $
               compT c3
        return $ ForC l ann v tau e1' e2' c3' s

    stepT step = transStep step
