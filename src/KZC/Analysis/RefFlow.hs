{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.RefFlow
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.RefFlow (
    rfProgram
  ) where

import Prelude hiding ((<=))

import Control.Monad (when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor,
                             tell)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

data Ref = VarR !Var
         | QueueR
  deriving (Eq, Ord, Show)

instance Pretty Ref where
    ppr (VarR v) = ppr v
    ppr QueueR   = text "queue"

instance Located Ref where
    locOf (VarR v) = locOf v
    locOf _        = noLoc

data RFState = RFState
    { -- | Maps a variable to the refs used to define the variable
      varFlowsFrom :: !(Map Var (Set Ref))
    , -- | The set of variables whose ref source has been modified
      tainted :: !(Set Var)
    , -- | The set of tainted variables that have been used
      usedTainted :: !(Set Var)
    }

instance Monoid RFState where
    mempty = RFState
        { varFlowsFrom = mempty
        , tainted      = mempty
        , usedTainted  = mempty
        }

    x `mappend` y = RFState
        { varFlowsFrom = Map.unionWith (<>) (varFlowsFrom x) (varFlowsFrom y)
        , tainted      = tainted x <> tainted y
        , usedTainted  = usedTainted x <> usedTainted y
        }

type RefSet = Set Ref

newtype RF m a = RF { unRF :: StateT RFState (WriterT RefSet m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadWriter RefSet,
              MonadState RFState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadPlatform,
              MonadTrace,
              MonadTc)

runRF :: MonadTc m => RF m a -> m a
runRF m = fst <$> runWriterT (evalStateT (unRF m) mempty)

-- | @extendVarFlowsFrom v refs k@ specifies that the references in @ref@ flow
-- to the variable @v@ in the scoped computation @k@.
extendVarFlowsFrom :: MonadTc m => Var -> Set Ref -> RF m a -> RF m a
extendVarFlowsFrom v refs k = do
    putFlowVars v refs
    delimitScope v k

-- | Delimit scope of a variable.
delimitScope :: MonadTc m => Var -> RF m a -> RF m a
delimitScope v k = do
    x <- k
    modify $ \s -> s { varFlowsFrom = Map.delete v (varFlowsFrom s)
                     , tainted      = Set.delete v (tainted s)
                     , usedTainted  = Set.delete v (usedTainted s)
                     }
    return x

-- | @putFlowVars v refs@ specifies that the references in @ref@ flow to the
-- variable @v@.
putFlowVars :: forall m . MonadTc m => Var -> Set Ref -> RF m ()
putFlowVars v refs | Set.null refs =
    modify $ \s -> s { varFlowsFrom = Map.delete v (varFlowsFrom s) }

putFlowVars v refs =
    modify $ \s -> s { varFlowsFrom = Map.insert v refs (varFlowsFrom s) }

-- | Indicated that a ref was potentially modified.
refModified :: MonadTc m => Ref -> RF m ()
refModified r = do
    -- Find variables for which r is a ref source.
    flows  <- gets (Map.assocs . varFlowsFrom)
    let vs =  [v | (v, refs) <- flows, r `Set.member` refs]
    traceRefFlow $ nest 2 $
        text "Modification of" <+> ppr r <+> text "is tainting:" <+> ppr vs
    modify $ \s -> s { tainted = tainted s `Set.union` Set.fromList vs }

useVar :: MonadTc m => Var -> RF m ()
useVar v = do
    -- If the variable is tainted, mark it as being used while tainted.
    isTainted <- gets $ \s -> v `Set.member` tainted s
    when isTainted $ do
        traceRefFlow $ text "Use of" <+> ppr v <+> text "is tainted"
        modify $ \s -> s { usedTainted = Set.insert v (usedTainted s) }
    -- Mark the refs used to produce the value of the variable.
    tau <- lookupVar v
    if isRefT tau
      then tell $ Set.singleton (VarR v)
      else do refs <- fromMaybe mempty <$> gets (Map.lookup v . varFlowsFrom)
              tell refs

queueModified :: MonadTc m => RF m ()
queueModified = do
    refModified QueueR
    tell $ Set.singleton QueueR

-- | Collect the set of refs used to produce the result of the computation @k@.
collectUseInfo :: Monad m => RF m a -> RF m (a, RefSet)
collectUseInfo k =
    censor (const mempty) $
    listen k

-- | Throw away the set of refs used to produce the result of the computation
-- @k@.
voidUseInfo :: Monad m => RF m a -> RF m a
voidUseInfo = censor (const mempty)

updateTaint :: MonadTc m => BoundVar -> RF m a -> RF m (a, BoundVar)
updateTaint bv m =
    censor f $ do
    x              <- m
    usedAfterTaint <- gets $ \s -> Set.member (bVar bv) (usedTainted s)
    return (x, bv { bTainted = Just usedAfterTaint })
  where
    f :: RefSet -> RefSet
    f = Set.delete (VarR (bVar bv))

rfProgram :: MonadTc m => Program l -> m (Program l)
rfProgram = runRF . programT

instance MonadTc m => TransformExp (RF m) where
    localDeclT (LetLD v tau e1 s) k = do
      (e1', refs) <- collectUseInfo $ expT e1
      (x, v')     <- extendVars [(bVar v, tau)] $
                     extendVarFlowsFrom (bVar v) refs $
                     updateTaint v k
      return (LetLD v' tau e1' s, x)

    localDeclT (LetRefLD v tau maybe_e1 s) k = do
      maybe_e1' <- traverse (voidUseInfo . expT) maybe_e1
      x         <- extendVars [(bVar v, refT tau)] $
                   delimitScope (bVar v) k
      return (LetRefLD v tau maybe_e1' s, x)

    localDeclT decl@(LetTypeLD alpha kappa tau _) k = do
      x <- extendTyVars [(alpha, kappa)] $
           extendTyVarTypes [(alpha, tau)] k
      return (decl, x)

    localDeclT LetViewLD{} _ =
        faildoc $ text "Views not supported."

    expT e@(VarE v _) = do
        useVar v
        return e

    expT (IfE e1 e2 e3 s) = do
        e1'        <- expT e1
        (e2', e3') <- rfIf (expT e2) (expT e3)
        return $ IfE e1' e2' e3' s

    expT (CallE f iotas es s) = do
        e' <- CallE f iotas <$> mapM expT es <*> pure s
        mapM_ taintArg es
        return e'
      where
        taintArg :: Exp -> RF m ()
        taintArg e = do
            tau <- inferExp e
            when (isRefT tau) $ do
                v <- refPathRoot e
                refModified $ VarR v

    expT (AssignE e1 e2 s) = do
        e1'         <- expT e1
        (e2', refs) <- collectUseInfo $ expT e2
        v           <- refPathRoot e1
        refModified (VarR v)
        putFlowVars v refs
        return $ AssignE e1' e2' s

    expT (BindE WildV tau e1 e2 s) = do
        e1' <- voidUseInfo $ expT e1
        e2' <- expT e2
        return $ BindE WildV tau e1' e2' s

    expT (BindE (TameV v) tau e1 e2 s) = do
        (e1', refs) <- collectUseInfo $ expT e1
        (e2', v')   <- extendVars [(bVar v, tau)] $
                       extendVarFlowsFrom (bVar v) refs $
                       updateTaint v $
                       expT e2
        return $ BindE (TameV v') tau e1' e2' s

    expT e =
      transExp e

instance MonadTc m => TransformComp l (RF m) where
    stepsT [] =
        return []

    stepsT (LetC l decl s : steps) = do
        (decl', steps') <- localDeclT decl $ stepsT steps
        return $ LetC l decl' s : steps'

    stepsT (step : BindC l WildV tau s : steps) = do
        step'  <- voidUseInfo $ stepT step
        steps' <- stepsT steps
        return $ step' : BindC l WildV tau s : steps'

    stepsT (step : BindC l (TameV v) tau s : steps) = do
        (step', refs) <- collectUseInfo $ stepT step
        (steps', v')  <- extendVars [(bVar v, tau)] $
                         extendVarFlowsFrom (bVar v) refs $
                         updateTaint v $
                         stepsT steps
        return $ step' : BindC l (TameV v') tau s : steps'

    stepsT (step : steps) = do
        step'  <- voidUseInfo $ stepT step
        steps' <- stepsT steps
        return $ step' : steps'

    stepT c@(VarC _ v _) = do
        useVar v
        return c

    stepT (CallC l f iotas args s) = do
        -- We taint arguments /before/ we call 'rfArg' so that any arguments
        -- that may be derived from a ref dereference are actually dereferenced.
        -- See Note [Aliasing] in Cg.hs.
        mapM_ taintArg args
        CallC l f iotas <$> mapM argT args <*> pure s
      where
        taintArg :: Arg l -> RF m ()
        taintArg CompA{} =
            return ()

        taintArg (ExpA e) = do
            tau <- inferExp e
            when (isRefT tau) $ do
                v <- refPathRoot e
                refModified $ VarR v

    stepT (IfC l e1 c2 c3 s) = do
        e1'        <- expT e1
        (c2', c3') <- rfIf (compT c2) (compT c3)
        return $ IfC l e1' c2' c3' s

    stepT c@TakeC{} = do
        queueModified
        return c

    stepT c@TakesC{} = do
        queueModified
        return c

    stepT (EmitC l e s) =
        EmitC l <$> voidUseInfo (expT e) <*> pure s

    stepT (EmitsC l e s) =
        EmitsC l <$> voidUseInfo (expT e) <*> pure s

    stepT (ParC ann tau c1 c2 s) = do
        -- We need to make sure any refs modified in /either/ branch are seen as
        -- modified in both branches. If the two branches use the same source
        -- ref, we need to re-analyze them to look for use-after-modify. See
        -- Note [Aliasing] in Cg.hs.
        (c1', refs1) <- collectUseInfo $ compT c1
        (c2', refs2) <- collectUseInfo $ compT c2
        tell $ refs1 <> refs2
        if Set.null (refs1 `Set.intersection` refs2)
          then return $ ParC ann tau c1' c2' s
          else ParC ann tau <$> compT c1 <*> compT c2 <*> pure s

    stepT step =
        transStep step

rfIf :: Monad m
     => RF m a
     -> RF m a
     -> RF m (a, a)
rfIf k1 k2 = do
    s <- get
    (x, refs2) <- collectUseInfo k1
    s2 <- get
    put s
    (y, refs3) <- collectUseInfo k2
    s3 <- get
    tell $ refs2 <> refs3
    put $ s2 <> s3
    return (x, y)
