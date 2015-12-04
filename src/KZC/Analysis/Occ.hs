{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      :  KZC.Analysis.Occ
-- Copyright   :  (c) Drexel University 2015
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Occ (
    OccM,
    runOccM,

    occProgram
  ) where

import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..))
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Traversable (traverse)
import Text.PrettyPrint.Mainland

import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Lint
import KZC.Monad
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

newtype OccM a = OccM { unOccM :: ReaderT TcEnv (WriterT OccEnv KZC) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TcEnv,
              MonadWriter OccEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runOccM :: OccM a -> TcEnv -> KZC a
runOccM m env = fst <$> runWriterT (runReaderT (unOccM m) env)

instance MonadTc OccM where
    askTc       = OccM $ ask
    localTc f m = OccM $ local f (unOccM m)

occVar :: Var -> OccM ()
occVar v = tell $ Occ (Map.singleton v Once)

-- | Return occurrence information for the given variable after running the
-- specified action, after which the variable is purged from the occurrence
-- environment.
withOccInfo :: BoundVar -> OccM a -> OccM (a, OccInfo)
withOccInfo v m =
    censor f $ do
    (x, env) <- listen m
    return (x, lookupOccInfo (bVar v) env)
  where
    f :: OccEnv -> OccEnv
    f (Occ env) = Occ $ Map.delete (bVar v) env

updOccInfo :: BoundVar -> OccInfo -> BoundVar
updOccInfo v occ = v { bOccInfo = Just occ }

occProgram :: LProgram -> OccM LProgram
occProgram (Program decls comp tau) = do
  (decls', comp') <-
      occDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      occComp comp
  return $ Program decls' comp' tau

occDecls :: [LDecl]
         -> OccM a
         -> OccM ([LDecl], a)
occDecls [] m = do
    x <- m
    return ([], x)

occDecls (d:ds) m = do
    (d', (ds', x)) <- occDecl d $ occDecls ds $ m
    return (d':ds', x)

occDecl :: LDecl
        -> OccM a
        -> OccM (LDecl, a)
occDecl (LetD v tau e s) m = do
    e'       <- occExp e
    (x, occ) <- extendVars [(bVar v, tau)] $ withOccInfo v m
    return (LetD (updOccInfo v occ) tau e' s, x)

occDecl (LetRefD v tau e s) m = do
    e'       <- traverse occExp e
    (x, occ) <- extendVars [(bVar v, refT tau)] $ withOccInfo v m
    return (LetRefD (updOccInfo v occ) tau e' s, x)

occDecl (LetFunD f iotas vbs tau_ret e l) m = do
    (x, e', occ) <-
        extendVars [(bVar f, tau)] $ do
        e' <- extendIVars (iotas `zip` repeat IotaK) $
              extendVars vbs $
              inSTScope tau_ret $
              inLocalScope $
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
    comp' <- inSTScope tau $
             inLocalScope $
             occComp comp
    (x, occ) <- extendVars [(bVar v, tau)] $ withOccInfo v m
    return (LetCompD (updOccInfo v occ) tau comp' l, x)

occDecl (LetFunCompD f iotas vbs tau_ret comp l) m = do
    (x, comp', occ) <-
        extendVars [(bVar f, tau)] $ do
        comp' <- extendIVars (iotas `zip` repeat IotaK) $
                 extendVars vbs $
                 inSTScope tau_ret $
                 inLocalScope $
                 occComp comp
        (x, occ) <- withOccInfo f m
        return (x, comp', occ)
    return (LetFunCompD (updOccInfo f occ) iotas vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

occLocalDecl :: LocalDecl
             -> OccM a
             -> OccM (LocalDecl, a)
occLocalDecl (LetLD v tau e s) m = do
    e'       <- occExp e
    (x, occ) <- extendVars [(bVar v, tau)] $ withOccInfo v m
    return (LetLD (updOccInfo v occ) tau e' s, x)

occLocalDecl (LetRefLD v tau e s) m = do
    e' <- traverse occExp e
    (x, occ) <- extendVars [(bVar v, refT tau)] $ withOccInfo v m
    return (LetRefLD (updOccInfo v occ) tau e' s, x)

occComp :: LComp -> OccM LComp
occComp (Comp steps) = Comp <$> occSteps steps

occSteps :: [LStep] -> OccM [LStep]
occSteps [] =
    return []

occSteps (LetC l decl s : steps) = do
    (decl', steps') <- occLocalDecl decl $ occSteps steps
    return $ LetC l decl' s : steps'

occSteps (step@(BindC _ bv _) : steps) =
    extendBindVars [bv] $
    (:) <$> pure step <*> occSteps steps

occSteps (step : steps) =
    (:) <$> occStep step <*> occSteps steps

occStep :: LStep -> OccM LStep
occStep step@(VarC _ v _) = do
    occVar v
    return step

occStep (CallC l f iotas es s) = do
    occVar f
    es' <- mapM occExp es
    return $ CallC l f iotas es' s

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

occExp :: Exp -> OccM Exp
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

occExp (BindE bv e1 e2 s) = do
    e1' <- occExp e1
    e2' <- extendBindVars [bv] $ occExp e2
    return $ BindE bv e1' e2' s
