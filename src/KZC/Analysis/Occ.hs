{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Occ
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Occ (
    OccM,
    runOccM,

    occProgram
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
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
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
    case Map.lookup v (unOcc env) of
      Nothing  -> Dead
      Just occ -> occ

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

-- | Return occurrence information for the given variable after running the
-- specified action, after which the variable is purged from the occurrence
-- environment.
withOccInfo :: MonadTc m => BoundVar -> OccM m a -> OccM m (a, OccInfo)
withOccInfo v m =
    censor f $ do
    (x, env) <- listen m
    return (x, lookupOccInfo (bVar v) env)
  where
    f :: OccEnv -> OccEnv
    f (Occ env) = Occ $ Map.delete (bVar v) env

updOccInfo :: BoundVar -> OccInfo -> BoundVar
updOccInfo v occ = v { bOccInfo = Just occ }

occProgram :: MonadTc m => Program l -> OccM m (Program l)
occProgram (Program decls comp tau) = do
  (decls', comp') <-
      occDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      occComp comp
  return $ Program decls' comp' tau

occDecls :: MonadTc m
         => [Decl l]
         -> OccM m a
         -> OccM m ([Decl l], a)
occDecls [] m = do
    x <- m
    return ([], x)

occDecls (d:ds) m = do
    (d', (ds', x)) <- occDecl d $ occDecls ds $ m
    return (d':ds', x)

occDecl :: MonadTc m
        => Decl l
        -> OccM m a
        -> OccM m (Decl l, a)
occDecl (LetD decl s) m = do
    (decl', x) <- occLocalDecl decl m
    return (LetD decl' s, x)

occDecl (LetFunD f iotas vbs tau_ret e l) m = do
    (x, e', occ) <-
        extendVars [(bVar f, tau)] $ do
        e' <- extendLetFun f iotas vbs tau_ret $
              occExp e
        (x, occ) <- withOccInfo f m
        return (x, e', occ)
    return (LetFunD (updOccInfo f occ) iotas vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

occDecl (LetExtFunD f iotas vbs tau_ret l) m = do
    (x, occ) <- extendVars [(bVar f, tau)] $
                withOccInfo f m
    return (LetExtFunD (updOccInfo f occ) iotas vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

occDecl decl@(LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (decl, x)

occDecl (LetCompD v tau comp l) m = do
    comp' <- extendLet v tau $
             occComp comp
    (x, occ) <- extendVars [(bVar v, tau)] $ withOccInfo v m
    return (LetCompD (updOccInfo v occ) tau comp' l, x)

occDecl (LetFunCompD f iotas vbs tau_ret comp l) m = do
    (x, comp', occ) <-
        extendVars [(bVar f, tau)] $ do
        comp' <- extendLetFun f iotas vbs tau_ret $
                 occComp comp
        (x, occ) <- withOccInfo f m
        return (x, comp', occ)
    return (LetFunCompD (updOccInfo f occ) iotas vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

occLocalDecl :: MonadTc m
             => LocalDecl
             -> OccM m a
             -> OccM m (LocalDecl, a)
occLocalDecl (LetLD v tau e s) m = do
    e'       <- occExp e
    (x, occ) <- extendVars [(bVar v, tau)] $ withOccInfo v m
    return (LetLD (updOccInfo v occ) tau e' s, x)

occLocalDecl (LetRefLD v tau e s) m = do
    e' <- traverse occExp e
    (x, occ) <- extendVars [(bVar v, refT tau)] $ withOccInfo v m
    return (LetRefLD (updOccInfo v occ) tau e' s, x)

occComp :: MonadTc m => Comp l -> OccM m (Comp l)
occComp (Comp steps) = Comp <$> occSteps steps

occSteps :: MonadTc m => [Step l] -> OccM m [Step l]
occSteps [] =
    return []

occSteps (LetC l decl s : steps) = do
    (decl', steps') <- occLocalDecl decl $ occSteps steps
    return $ LetC l decl' s : steps'

occSteps (step@(BindC _ WildV _ _) : steps) =
    (:) <$> pure step <*> occSteps steps

occSteps (BindC l (TameV v) tau s : steps) = do
    (steps', occ) <- extendVars [(bVar v, tau)] $
                     withOccInfo v $
                     occSteps steps
    return $ BindC l (TameV (updOccInfo v occ)) tau s : steps'

occSteps (step : steps) =
    (:) <$> occStep step <*> occSteps steps

occStep :: forall l m . MonadTc m => Step l -> OccM m (Step l)
occStep step@(VarC _ v _) = do
    occVar v
    return step

occStep (CallC l f iotas args s) = do
    occVar f
    args' <- mapM occArg args
    return $ CallC l f iotas args' s
  where
    occArg :: Arg l -> OccM m (Arg l)
    occArg (ExpA e)  = ExpA  <$> occExp e
    occArg (CompA c) = CompA <$> occComp c

occStep (IfC l e c1 c2 s) =
    IfC l <$> occExp e <*> occComp c1 <*> occComp c2 <*> pure s

occStep (LetC {}) =
    faildoc $ text "Cannot occ let step."

occStep (WhileC l e c s) = do
    WhileC l <$> occExp e <*> occComp c <*> pure s

occStep (ForC l ann v tau e1 e2 c s) = do
    ForC l ann v tau <$> occExp e1 <*> occExp e2 <*> occComp c <*> pure s

occStep (LiftC l e s) =
    LiftC l <$> occExp e <*> pure s

occStep (ReturnC l e s) =
    ReturnC l <$> occExp e <*> pure s

occStep (BindC {}) =
    faildoc $ text "Cannot occ bind step."

occStep step@(TakeC {}) =
    return step

occStep step@(TakesC {}) =
    return step

occStep (EmitC l e s) =
    EmitC l <$> occExp e <*> pure s

occStep (EmitsC l e s) =
    EmitsC l <$> occExp e <*> pure s

occStep (RepeatC l ann c s) =
    RepeatC l ann <$> occComp c <*> pure s

occStep (ParC ann tau c1 c2 s) = do
    ParC ann tau <$> occComp c1 <*> occComp c2 <*> pure s

occStep (LoopC {}) =
    faildoc $ text "occStep: saw LoopC"

occExp :: MonadTc m => Exp -> OccM m Exp
occExp e@(ConstE {}) =
    return e

occExp e@(VarE v _) = do
    occVar v
    return e

occExp (UnopE op e s) =
    UnopE op <$> occExp e <*> pure s

occExp (BinopE op e1 e2 s) =
    BinopE op <$> occExp e1 <*> occExp e2 <*> pure s

occExp (IfE e1 e2 e3 s) =
    IfE <$> occExp e1 <*> occExp e2 <*> occExp e3 <*> pure s

occExp (LetE decl e s) = do
    (decl', e') <- occLocalDecl decl $ occExp e
    return $ LetE decl' e' s

occExp (CallE f iotas es s) = do
    occVar f
    es' <- mapM occExp es
    return $ CallE f iotas es' s

occExp (DerefE e s) =
    DerefE <$> occExp e <*> pure s

occExp (AssignE e1 e2 s) =
    AssignE <$> occExp e1 <*> occExp e2 <*> pure s

occExp (WhileE e1 e2 s) =
    WhileE <$> occExp e1 <*> occExp e2 <*> pure s

occExp (ForE ann v tau e1 e2 e3 s) =
    ForE ann v tau <$> occExp e1 <*> occExp e2 <*> occExp e3 <*> pure s

occExp (ArrayE es s) =
    ArrayE <$> mapM occExp es <*> pure s

occExp (IdxE e1 e2 len s) =
    IdxE <$> occExp e1 <*> occExp e2 <*> pure len <*> pure s

occExp (StructE struct flds s) =
    StructE struct <$> (zip (map fst flds) <$> mapM (occExp . snd) flds) <*> pure s

occExp (ProjE e f s) =
    ProjE <$> occExp e <*> pure f <*> pure s

occExp (PrintE nl es s) =
    PrintE nl <$> mapM occExp es <*> pure s

occExp e@(ErrorE {}) =
    return e

occExp (ReturnE ann e s) =
    ReturnE ann <$> occExp e <*> pure s

occExp (BindE WildV tau e1 e2 s) = do
    e1' <- occExp e1
    e2' <- occExp e2
    return $ BindE WildV tau e1' e2' s

occExp (BindE (TameV v) tau e1 e2 s) = do
    e1'        <- occExp e1
    (e2', occ) <- extendVars [(bVar v, tau)] $
                  withOccInfo v $
                  occExp e2
    return $ BindE (TameV (updOccInfo v occ)) tau e1' e2' s

occExp (LutE e) =
    occExp e
