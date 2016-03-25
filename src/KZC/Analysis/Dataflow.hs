{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.DataFlow
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Dataflow (
    BoundedSet(..),
    fromBoundedSet,

    DState(..),
    D,
    runD
  ) where

import Prelude hiding (mapM_, (<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            runStateT,
                            gets,
                            modify)
import Control.Monad.Trans (MonadTrans(..))
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Analysis.Abs
import KZC.Auto.Lint
import KZC.Auto.Syntax hiding (S)
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice
import KZC.Util.SetLike

data BoundedSet a = S (Set a)
                  | TopS
  deriving (Eq, Ord, Show)

fromBoundedSet :: Monad m => BoundedSet a -> m (Set a)
fromBoundedSet TopS  = fail "Top"
fromBoundedSet (S s) = return s

instance Ord a => Monoid (BoundedSet a) where
    mempty = S mempty

    _    `mappend` TopS = TopS
    TopS `mappend` _    = TopS
    S s1 `mappend` S s2 = S (s1 `mappend` s2)

instance Foldable BoundedSet where
    foldr _ z TopS   = z
    foldr f z (S xs) = Data.Foldable.foldr f z xs

instance Ord a => SetLike BoundedSet a where
    member _ TopS   = True
    member x (S xs) = Set.member x xs
    singleton x     = S (Set.singleton x)
    insert _ TopS   = TopS
    insert x (S xs) = S (Set.insert x xs)
    TopS <\\> _     = TopS
    _    <\\> TopS  = mempty
    S xs <\\> S ys  = S (xs Set.\\ ys)
    delete _ TopS   = TopS
    delete x (S xs) = S (Set.delete x xs)
    fromList xs     = S (Set.fromList xs)

instance Ord a => Poset (BoundedSet a) where
    _    <= TopS = True
    S s1 <= S s2 = s1 <= s2
    _    <= _    = False

instance Ord a => Lattice (BoundedSet a) where
    TopS `lub` _    = TopS
    _    `lub` TopS = TopS
    S s1 `lub` S s2 = S (s1 `Set.union` s2)

    TopS `glb` s    = s
    s    `glb` TopS = s
    S s1 `glb` S s2 = S (s1 `Set.intersection` s2)

instance Ord a => BoundedLattice (BoundedSet a) where
    top = TopS
    bot = S Set.empty

instance Pretty a => Pretty (BoundedSet a) where
    ppr TopS  = text "T"
    ppr (S s) = ppr s

type VarSet = BoundedSet Var

data DEnv = DEnv { flowvars :: VarSet }

defaultDEnv :: DEnv
defaultDEnv = DEnv { flowvars = mempty }

data DState = DState
    { usedefs :: Map Var VarSet -- ^ Maps a variable to the set of variables
                                -- used to define it.
    , usefree :: VarSet         -- ^ All used free variables.
    }

defaultDState :: DState
defaultDState = DState
    { usedefs = mempty
    , usefree = mempty
    }

instance Poset DState where
    d1 <= d2 = usedefs d1 <= usedefs d2 && usefree d1 <= usefree d2

instance Lattice DState where
    d1 `lub` d2 = DState
        { usedefs = usedefs d1 `lub` usedefs d2
        , usefree = usefree d1 `lub` usefree d2
        }

    d1 `glb` d2 = DState
        { usedefs = usedefs d1 `glb` usedefs d2
        , usefree = usefree d1 `glb` usefree d2
        }

newtype D m a = D { unD :: ReaderT DEnv (StateT DState m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadReader DEnv,
              MonadState DState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

runD :: MonadTc m => D m a -> m (a, DState)
runD m = runStateT (runReaderT (unD m) defaultDEnv) defaultDState

instance MonadTrans D where
    lift = D . lift . lift

-- | Look up the set of variables that influenced control flow to this point.
lookupControlFlowVars :: MonadTc m => D m VarSet
lookupControlFlowVars = asks flowvars

-- | Extend the set of variables that influenced control flow to this point.
extendControlFlowVars :: MonadTc m => VarSet -> D m VarSet -> D m VarSet
extendControlFlowVars vs m = do
  res <- local (\env -> env { flowvars = flowvars env <> vs }) m
  return $ res <> vs

-- | Purge the variable from all uses because it is going out of scope.
purgeVar :: MonadTc m => Var -> D m VarSet -> D m VarSet
purgeVar v m = do
    vs <- m
    modify $ \s ->
        s { usedefs = (Map.map (delete v) . Map.delete v) (usedefs s)
          , usefree = delete v (usefree s)
          }
    return $ delete v vs

-- | Look up all variables that contribute to the use of @v@.
lookupVarDef :: MonadTc m => Var -> D m VarSet
lookupVarDef v =
    maybe (singleton v) (<> singleton v) <$> gets (Map.lookup v . usedefs)

-- | Record the fact that @v@ depends on the set of variables @vs'@. Note that
-- @v@ also depends on the current set of control flow variables.
addUseDefs :: MonadTc m => Var -> VarSet -> D m ()
addUseDefs v vs' = do
    cfvs <- lookupControlFlowVars
    modify $ \s -> s { usedefs = Map.alter (f cfvs) v (usedefs s) }
  where
    f :: VarSet -> Maybe VarSet -> Maybe VarSet
    f cfvs Nothing   = Just $ vs' <> cfvs
    f cfvs (Just vs) = Just $ vs <> vs' <> cfvs

addUseFree :: MonadTc m => Var -> D m ()
addUseFree v = modify $ \s -> s { usefree = insert v (usefree s) }

instance ValDom VarSet where
    constDom         = mempty
    unopDom _ v      = v
    binopDom _ v1 v2 = v1 <> v2
    arrayDom vs      = mconcat vs
    idxDom _ v1 v2 _ = v1 <> v2
    structDom _ flds = mconcat (map snd flds)
    projDom _ v _    = v

instance MonadTc m => MonadAbs DState VarSet VarSet (D m) where
    iotaDom _ = return mempty

    varDom v = do
        addUseFree v
        lookupVarDef v

    letDom v vs body = purgeVar v $ do
        addUseFree v
        addUseDefs v vs
        body

    letrefDom v body = purgeVar v $
        body

    -- XXX ref arguments to a function may be modified using any of the
    -- arguments passed to the function as well as any variables that were
    -- lexically in scope at the point the function was defined. We have don't
    -- track the latter right now, so we are ignoring
    callDom _f _ivs args = do
        vs <- mconcat <$> mapM go args
        mapM_ (update vs) [r | RefA r <- args]
        return vs
      where
        go :: FunArg VarSet -> D m VarSet
        go (ValA vs) = return vs
        go (RefA r)  = derefDom r

        update :: VarSet -> Ref VarSet -> D m ()
        update vs r = assignDom r vs

    derefDom r =
        go r
      where
        go :: Ref VarSet -> D m VarSet
        go (VarR v)      = addUseFree v >> lookupVarDef v
        go (IdxR r vs _) = (<>) <$> go r <*> pure vs
        go (ProjR r _)   = go r

    assignDom r vs =
        go r vs
      where
        go :: Ref VarSet -> VarSet -> D m ()
        go (VarR v)        vs = addUseDefs v vs
        go (IdxR r vs_i _) vs = go r (vs <> vs_i)
        go (ProjR r _)     vs = go r vs

    printDom _ vs = return $ mconcat vs

    errorDom = return ()

    returnDom vs = return vs

    bindDom WildV _ body =
        body

    bindDom (TameV v) vs body = purgeVar (bVar v) $ do
        addUseFree (bVar v)
        addUseDefs (bVar v) vs
        body

    getA = get
    putA = put

    widenA _ m1 m2 = joinA m1 m2

    withCond vs m = extendControlFlowVars vs m
