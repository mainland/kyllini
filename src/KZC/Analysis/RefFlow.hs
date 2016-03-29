{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.RefFlow
-- Copyright   :  (c) Drexel University 2016
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.RefFlow (
    refFlowModExp,
    refFlowModComp
  ) where

import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>))
import Control.Monad (void,
                      when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            execStateT,
                            gets,
                            modify)
import Data.Foldable (toList,
                      traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq

data Ref = VarR Var
         | QueueR
  deriving (Eq, Ord, Show)

-- | Return the set of variables bound somewhere in the given expression that
-- are defined using refs that are modified before some use of the defined
-- variable.
refFlowModExp :: MonadTc m => Exp -> m (Set Var)
refFlowModExp e = usedTainted <$> (execRF $ rfExp e)

-- | Return the set of variables bound somewhere in the given computation that
-- are defined using refs that are modified before some use of the defined
-- variable.
refFlowModComp :: MonadTc m => Comp l -> m (Set Var)
refFlowModComp c = usedTainted <$> (execRF $ rfComp c)

data RFEnv = RFEnv
    { -- | Maps a variable to the refs used to define the variable
      varFlowsFrom :: Map Var (Set Ref)
    }

defaultRFEnv :: RFEnv
defaultRFEnv  = RFEnv
    { varFlowsFrom = Map.empty }

data RFState = RFState
    { -- | Maps a reference to the variables it flows to.
      varsFlowTo :: Map Ref (Set Var)
    , -- | The set of variables whose ref source has been modified
      tainted :: Set Var
    , -- | The set of tainted variables that have been used
      usedTainted :: Set Var
    }

defaultRFState :: RFState
defaultRFState  = RFState
    { varsFlowTo  = Map.empty
    , tainted     = Set.empty
    , usedTainted = Set.empty
    }

newtype RF m a = RF { unRF :: ReaderT RFEnv (StateT RFState m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadReader RFEnv,
              MonadState RFState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

execRF :: MonadTc m => RF m a -> m RFState
execRF m = execStateT (runReaderT (unRF m) defaultRFEnv) defaultRFState

extendVarFlowsFrom :: forall m a . MonadTc m => Var -> Set Ref -> RF m a -> RF m a
extendVarFlowsFrom v vrefs k = do
    local (\env -> env { varFlowsFrom = Map.insert v vrefs (varFlowsFrom env) }) $ do
    mapM_ (\vref -> flowsTo vref v) (toList vrefs)
    k
  where
    flowsTo :: Ref -> Var -> RF m ()
    flowsTo vref v =
        modify $ \s ->
            s { varsFlowTo = Map.insert vref
                                        (Set.insert v (Map.findWithDefault mempty vref (varsFlowTo s)))
                                        (varsFlowTo s)
              }

askVarFlowsFrom :: MonadTc m => Var -> RF m (Set Ref)
askVarFlowsFrom v =
    maybe mempty id <$> asks (\env -> Map.lookup v (varFlowsFrom env))

-- | Indicated that a ref was potentially modified.
refModified :: MonadTc m => Ref -> RF m ()
refModified v = do
    flowsTo <- gets $ \s -> Map.lookup v (varsFlowTo s)
    case flowsTo of
      Nothing -> return ()
      Just vs -> modify $ \s -> s { tainted = tainted s `Set.union` vs }

useVar :: MonadTc m => Var -> RF m ()
useVar v = do
    isTainted <- gets $ \s -> v `Set.member` tainted s
    when isTainted $
        modify $ \s -> s { usedTainted = Set.insert v (usedTainted s) }

-- | Given an expression of type @ref \tau@, return the source variable of type
-- @ref@.
refRoot :: Monad m => Exp -> m Ref
refRoot (VarE v _)     = return $ VarR v
refRoot (IdxE e _ _ _) = refRoot e
refRoot (ProjE e _ _)  = refRoot e
refRoot e              = faildoc $ text "Not a reference:" <+> ppr e

rfLocalDecl :: forall m a . MonadTc m => LocalDecl -> RF m a -> RF m a
rfLocalDecl (LetLD v tau e1 _) k = do
    vs1 <- rfExp e1
    extendVars [(bVar v, tau)] $
      extendVarFlowsFrom (bVar v) vs1 $
      k

rfLocalDecl (LetRefLD v tau e1 _) k = do
    traverse_ rfExp e1
    extendVars [(bVar v, refT tau)] $
      k

rfExp :: forall m . MonadTc m => Exp -> RF m (Set Ref)
rfExp (ConstE {}) =
    return mempty

rfExp (VarE v _) = do
    useVar v
    tau <- lookupVar v
    if isRefT tau
      then return $ Set.singleton (VarR v)
      else askVarFlowsFrom v

rfExp (UnopE _ e _) =
    rfExp e

rfExp (BinopE _ e1 e2 _) = do
    Set.union <$> rfExp e1 <*> rfExp e2

rfExp (IfE e1 e2 e3 _) =
    Set.unions <$> mapM rfExp [e1, e2, e3]

rfExp (LetE decl e2 _) =
    rfLocalDecl decl $
    rfExp e2

rfExp (CallE _ _ es _) = do
    Set.unions <$> mapM rfArg es
  where
    rfArg :: Exp -> RF m (Set Ref)
    rfArg e = do
        tau <- inferExp e
        when (isRefT tau) $
            refRoot e >>= refModified
        rfExp e

rfExp (DerefE e _) =
    rfExp e

rfExp (AssignE e1 e2 _) = do
    void $ rfExp e1
    void $ rfExp e2
    v <- refRoot e1
    refModified v
    return mempty

rfExp (WhileE e1 e2 _) =
    Set.union <$> rfExp e1 <*> rfExp e2

rfExp (ForE _ v tau e1 e2 e3 _) = do
    vs1 <- Set.union <$> rfExp e1 <*> rfExp e2
    vs2 <- extendVars [(v, tau)] $ rfExp e3
    return $ vs1 `Set.union` vs2

rfExp (ArrayE es _) = do
    Set.unions <$> mapM rfExp es

rfExp (IdxE e1 e2 _ _) =
    Set.union <$> rfExp e1 <*> rfExp e2

rfExp (StructE _ flds _) =
    Set.unions <$> mapM (rfExp . snd) flds

rfExp (ProjE e _ _) =
    rfExp e

rfExp (PrintE _ es _) =
    Set.unions <$> mapM rfExp es

rfExp (ErrorE {}) =
    return mempty

rfExp (ReturnE _ e _) =
    rfExp e

rfExp (BindE WildV _ e1 e2 _) = do
    void $ rfExp e1
    rfExp e2

rfExp (BindE (TameV v) tau e1 e2 _) = do
    vs1 <- rfExp e1
    extendVars [(bVar v, tau)] $
      extendVarFlowsFrom (bVar v) vs1 $
      rfExp e2

rfExp (LutE e) =
    rfExp e

rfComp :: forall l m . MonadTc m => Comp l -> RF m (Set Ref)
rfComp (Comp steps) =
    rfSteps steps mempty

rfSteps :: MonadTc m => [Step l] -> Set Ref -> RF m (Set Ref)
rfSteps [] _ =
    return mempty

rfSteps (LetC _ decl _ : steps) _ =
    rfLocalDecl decl $
    rfSteps steps mempty

rfSteps (BindC _ WildV _ _ : steps) _ = do
    rfSteps steps mempty

rfSteps (BindC _ (TameV v) tau _ : steps) vs =
    extendVars [(bVar v, tau)] $
    extendVarFlowsFrom (bVar v) vs $
    rfSteps steps vs

rfSteps (step : steps) _ =
    rfStep step >>= rfSteps steps

rfStep :: forall l m . MonadTc m => Step l -> RF m (Set Ref)
rfStep (VarC _ v _) = do
    useVar v
    askVarFlowsFrom v

rfStep (CallC _ _ _ args _) =
    Set.unions <$> mapM rfArg args
  where
    rfArg :: Arg l -> RF m (Set Ref)
    rfArg (CompA comp) = do
        void $ rfComp comp
        return mempty

    rfArg (ExpA e) = do
        tau <- inferExp e
        when (isRefT tau) $
            refRoot e >>= refModified
        rfExp e

rfStep (IfC _ e c1 c2 _) =
    Set.unions <$> sequence [rfExp e, rfComp c1, rfComp c2]

rfStep (LetC {}) =
    faildoc $ text "Cannot rf let step."

rfStep (WhileC _ e c _) = do
    Set.union <$> rfExp e <*> rfComp c

rfStep (ForC _ _ v tau e1 e2 c _) = do
    vs1 <- Set.union <$> rfExp e1 <*> rfExp e2
    vs2 <- extendVars [(v, tau)] $ rfComp c
    return $ vs1 `Set.union` vs2

rfStep (LiftC _ e _) =
    rfExp e

rfStep (ReturnC _ e _) =
    rfExp e

rfStep (BindC {}) =
    faildoc $ text "Cannot rf bind step."

rfStep (TakeC {}) = do
    refModified QueueR
    return $ Set.singleton QueueR

rfStep (TakesC {}) = do
    refModified QueueR
    return $ Set.singleton QueueR

rfStep (EmitC _ e _) = do
    void $ rfExp e
    return mempty

rfStep (EmitsC _ e _) = do
    void $ rfExp e
    return mempty

rfStep (RepeatC _ _ c _) =
    rfComp c

rfStep (ParC _ _ c1 c2 _) =
    Set.union <$> rfComp c1 <*> rfComp c2

rfStep (LoopC {}) =
    faildoc $ text "rfStep: saw LoopC"
