{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Occ
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Occ (
    occProgram,
    occComp
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice

newtype OccEnv = Occ { unOcc :: Map Var OccInfo }
  deriving (Poset, Lattice, BranchLattice)

instance Monoid OccEnv where
    mempty = Occ mempty

    occ `mappend` occ' = occ `lub` occ'

lookupOccInfo :: Var -> OccEnv -> OccInfo
lookupOccInfo v env =
    fromMaybe Dead $ Map.lookup v (unOcc env)

newtype OccM m a = OccM { unOccM :: WriterT OccEnv m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadWriter OccEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans OccM where
    lift m = OccM $ lift m

runOccM :: MonadTc m => OccM m a -> m a
runOccM m = fst <$> runWriterT (unOccM m)

occVar :: MonadTc m => Var -> OccM m ()
occVar v = tell $ Occ (Map.singleton v Once)

collectOcc :: MonadTc m => OccM m a -> OccM m (OccEnv, a)
collectOcc m =
    censor (const mempty) $ do
    (x, occ) <- listen m
    return (occ, x)

-- | Return occurrence information for the given variable after running the
-- specified action, after which the variable is purged from the occurrence
-- environment.
withOccInfo :: MonadTc m => BoundVar -> OccM m a -> OccM m (OccInfo, a)
withOccInfo v m =
    censor f $ do
    (x, env) <- listen m
    return (lookupOccInfo (bVar v) env, x)
  where
    f :: OccEnv -> OccEnv
    f (Occ env) = Occ $ Map.delete (bVar v) env

updOccInfo :: BoundVar -> OccInfo -> BoundVar
updOccInfo v occ = v { bOccInfo = Just occ }

occProgram :: MonadTc m => Program l -> m (Program l)
occProgram = runOccM . programT

occComp :: MonadTc m => Comp l -> m (Comp l)
occComp = runOccM . compT

instance MonadTc m => TransformExp (OccM m) where
    localDeclT (LetLD v tau e s) m = do
        e'       <- expT e
        (occ, x) <- extendVars [(bVar v, tau)] $ withOccInfo v m
        return (LetLD (updOccInfo v occ) tau e' s, x)

    localDeclT (LetRefLD v tau e s) m = do
        e'       <- traverse expT e
        (occ, x) <- extendVars [(bVar v, refT tau)] $ withOccInfo v m
        return (LetRefLD (updOccInfo v occ) tau e' s, x)

    expT e@(VarE v _) = do
        occVar v
        return e

    expT e@(CallE f _ _ _) = do
        occVar f
        transExp e

    expT (IfE e1 e2 e3 s) = do
        e1'         <- expT e1
        (occ2, e2') <- collectOcc $ expT e2
        (occ3, e3') <- collectOcc $ expT e3
        tell $ occ2 `bub` occ3
        return $ IfE e1' e2' e3' s

    expT (BindE (TameV v) tau e1 e2 s) = do
        e1'        <- expT e1
        (occ, e2') <- extendVars [(bVar v, tau)] $
                      withOccInfo v $
                      expT e2
        return $ BindE (TameV (updOccInfo v occ)) tau e1' e2' s

    expT e =
        transExp e

instance MonadTc m => TransformComp l (OccM m) where
    declT (LetFunD f iotas vbs tau_ret e l) m =
        extendVars [(bVar f, tau)] $ do
        e'       <- extendLetFun f iotas vbs tau_ret $
                    expT e
        (occ, x) <- withOccInfo f m
        return (LetFunD (updOccInfo f occ) iotas vbs tau_ret e' l, x)
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    declT (LetExtFunD f iotas vbs tau_ret l) m = do
        (occ, x) <- extendExtFuns [(bVar f, tau)] $
                    withOccInfo f m
        return (LetExtFunD (updOccInfo f occ) iotas vbs tau_ret l, x)
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    declT (LetCompD v tau comp l) m = do
        comp'    <- extendLet v tau $
                    compT comp
        (occ, x) <- extendVars [(bVar v, tau)] $ withOccInfo v m
        return (LetCompD (updOccInfo v occ) tau comp' l, x)

    declT (LetFunCompD f iotas vbs tau_ret comp l) m =
        extendVars [(bVar f, tau)] $ do
        comp'    <- extendLetFun f iotas vbs tau_ret $
                    compT comp
        (occ, x) <- withOccInfo f m
        return (LetFunCompD (updOccInfo f occ) iotas vbs tau_ret comp' l, x)
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    declT decl m =
        transDecl decl m

    stepsT (BindC l (TameV v) tau s : steps) = do
        (occ, steps') <- extendVars [(bVar v, tau)] $
                         withOccInfo v $
                         stepsT steps
        return $ BindC l (TameV (updOccInfo v occ)) tau s : steps'

    stepsT steps =
        transSteps steps

    stepT step@(VarC _ v _) = do
        occVar v
        transStep step

    stepT step@(CallC _ f _ _ _) = do
        occVar f
        transStep step

    stepT (IfC l e1 c2 c3 s) = do
        e1'         <- expT e1
        (occ2, c2') <- collectOcc $ compT c2
        (occ3, c3') <- collectOcc $ compT c3
        tell $ occ2 `bub` occ3
        return $ IfC l e1' c2' c3' s

    stepT step =
        transStep step
