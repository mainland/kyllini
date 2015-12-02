{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      :  KZC.Optimize.Simplify
-- Copyright   :  (c) Drexel University 2015
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Simplify (
    SimplM,
    runSimplM,

    simplProgram
  ) where

import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..))
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Data.IORef
import Data.Traversable (traverse)
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Trace
import KZC.Uniq

newtype SimplM a = SimplM { unSimplM :: ReaderT TcEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TcEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runSimplM :: SimplM a -> TcEnv -> KZC a
runSimplM m env = runReaderT (unSimplM m) env

instance MonadTc SimplM where
    askTc       = SimplM $ ask
    localTc f m = SimplM $ local f (unSimplM m)

simplProgram :: LProgram -> SimplM LProgram
simplProgram (Program decls comp tau) = do
  (decls', comp') <-
      simplDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      simplComp comp
  return $ Program decls' comp' tau

simplDecls :: [LDecl]
           -> SimplM a
           -> SimplM ([LDecl], a)
simplDecls [] m = do
    x <- m
    return ([], x)

simplDecls (d:ds) m = do
    (maybe_d', (ds', x)) <- simplDecl d $ simplDecls ds $ m
    return (maybe ds' (:ds') maybe_d', x)

simplDecl :: LDecl
          -> SimplM a
          -> SimplM (Maybe LDecl, a)
simplDecl (LetD decl s) m = do
    (maybe_decl', x) <- simplLocalDecl decl m
    case maybe_decl' of
      Nothing    -> return (Nothing, x)
      Just decl' -> return (Just (LetD decl' s), x)

simplDecl (LetFunD f _ _ _ _ _) m | bOccInfo f == Just Dead =
    (,) <$> pure Nothing <*> m

simplDecl (LetFunD f iotas vbs tau_ret e l) m = do
    (x, e') <-
        extendVars [(bVar f, tau)] $ do
        e' <- extendIVars (iotas `zip` repeat IotaK) $
              extendVars vbs $
              inSTScope tau_ret $
              inLocalScope $
              simplExp e
        x <- m
        return (x, e')
    return (Just $ LetFunD f iotas vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

simplDecl (LetExtFunD f _ _ _ _) m | bOccInfo f == Just Dead =
    (,) <$> pure Nothing <*> m

simplDecl (LetExtFunD f iotas vbs tau_ret l) m = do
    x <- extendVars [(bVar f, tau)] m
    return (Just $ LetExtFunD f iotas vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

simplDecl decl@(LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (Just decl, x)

simplDecl (LetCompD v _ _ _) m | bOccInfo v == Just Dead =
    (,) <$> pure Nothing <*> m

simplDecl (LetCompD v tau comp l) m = do
    comp' <- inSTScope tau $
             inLocalScope $
             simplComp comp
    x     <- extendVars [(bVar v, tau)]  m
    return (Just $ LetCompD v tau comp' l, x)

simplDecl (LetFunCompD f _ _ _ _ _) m | bOccInfo f == Just Dead =
    (,) <$> pure Nothing <*> m

simplDecl (LetFunCompD f iotas vbs tau_ret comp l) m = do
    (x, comp') <-
        extendVars [(bVar f, tau)] $ do
        comp' <- extendIVars (iotas `zip` repeat IotaK) $
                 extendVars vbs $
                 inSTScope tau_ret $
                 inLocalScope $
                 simplComp comp
        x     <- m
        return (x, comp')
    return (Just $ LetFunCompD f iotas vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

simplLocalDecl :: LocalDecl
               -> SimplM a
               -> SimplM (Maybe LocalDecl, a)
simplLocalDecl (LetLD v _ _ _) m | bOccInfo v == Just Dead =
    (,) <$> pure Nothing <*> m

simplLocalDecl (LetLD v tau e s) m = do
    e' <- simplExp e
    x  <- extendVars [(bVar v, tau)] m
    return (Just $ LetLD v tau e' s, x)

simplLocalDecl (LetRefLD v _ _ _) m | bOccInfo v == Just Dead =
    (,) <$> pure Nothing <*> m

simplLocalDecl (LetRefLD v tau e s) m = do
    e' <- traverse simplExp e
    x  <- extendVars [(bVar v, refT tau)] m
    return (Just $ LetRefLD v tau e' s, x)

simplComp :: LComp -> SimplM LComp
simplComp (Comp steps) = Comp <$> simplSteps steps

simplSteps :: [LStep] -> SimplM [LStep]
simplSteps [] =
    return []

simplSteps (LetC l decl s : steps) = do
    (maybe_decl', steps') <- simplLocalDecl decl $ simplSteps steps
    case maybe_decl' of
      Nothing    -> return steps
      Just decl' -> return $ LetC l decl' s : steps'

simplSteps (step@(BindC _ wv tau _) : steps) =
    extendWildVars [(wv, tau)] $
    (:) <$> pure step <*> simplSteps steps

simplSteps (step : steps) =
    (:) <$> simplStep step <*> simplSteps steps

simplStep :: LStep -> SimplM LStep
simplStep step@(VarC {}) =
    return step

simplStep (CallC l f iotas args s) = do
    args' <- mapM simplArg args
    return $ CallC l f iotas args' s
  where
    simplArg :: LArg -> SimplM LArg
    simplArg (ExpA e)  = ExpA  <$> simplExp e
    simplArg (CompA c) = CompA <$> simplComp c

simplStep (IfC l e c1 c2 s) =
    IfC l <$> simplExp e <*> simplComp c1 <*> simplComp c2 <*> pure s

simplStep (LetC {}) =
    faildoc $ text "Cannot occ let step."

simplStep (WhileC l e c s) = do
    WhileC l <$> simplExp e <*> simplComp c <*> pure s

simplStep (ForC l ann v tau e1 e2 c s) = do
    ForC l ann v tau <$> simplExp e1 <*> simplExp e2 <*> simplComp c <*> pure s

simplStep (LiftC l e s) =
    LiftC l <$> simplExp e <*> pure s

simplStep (ReturnC l e s) =
    ReturnC l <$> simplExp e <*> pure s

simplStep (BindC {}) =
    faildoc $ text "Cannot occ bind step."

simplStep step@(TakeC {}) =
    return step

simplStep step@(TakesC {}) =
    return step

simplStep (EmitC l e s) =
    EmitC l <$> simplExp e <*> pure s

simplStep (EmitsC l e s) =
    EmitsC l <$> simplExp e <*> pure s

simplStep (RepeatC l ann c s) =
    RepeatC l ann <$> simplComp c <*> pure s

simplStep (ParC ann tau c1 c2 s) = do
    ParC ann tau <$> simplComp c1 <*> simplComp c2 <*> pure s

simplStep (LoopC {}) =
    faildoc $ text "simplStep: saw LoopC"

simplExp :: Exp -> SimplM Exp
simplExp e@(ConstE {}) =
    return e

simplExp e@(VarE {}) =
    return e

simplExp (UnopE op e s) =
    UnopE op <$> simplExp e <*> pure s

simplExp (BinopE op e1 e2 s) =
    BinopE op <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (IfE e1 e2 e3 s) =
    IfE <$> simplExp e1 <*> simplExp e2 <*> simplExp e3 <*> pure s

simplExp (LetE decl e s) = do
    (maybe_decl', e') <- simplLocalDecl decl $ simplExp e
    case maybe_decl' of
      Nothing    -> return e'
      Just decl' -> return $ LetE decl' e' s

simplExp (CallE f iotas es s) = do
    es' <- mapM simplExp es
    return $ CallE f iotas es' s

simplExp (DerefE e s) =
    DerefE <$> simplExp e <*> pure s

simplExp (AssignE e1 e2 s) =
    AssignE <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (WhileE e1 e2 s) =
    WhileE <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (ForE ann v tau e1 e2 e3 s) =
    ForE ann v tau <$> simplExp e1 <*> simplExp e2 <*> simplExp e3 <*> pure s

simplExp (ArrayE es s) =
    ArrayE <$> mapM simplExp es <*> pure s

simplExp (IdxE e1 e2 len s) =
    IdxE <$> simplExp e1 <*> simplExp e2 <*> pure len <*> pure s

simplExp (StructE struct flds s) =
    StructE struct <$> (zip (map fst flds) <$> mapM (simplExp . snd) flds) <*> pure s

simplExp (ProjE e f s) =
    ProjE <$> simplExp e <*> pure f <*> pure s

simplExp (PrintE nl es s) =
    PrintE nl <$> mapM simplExp es <*> pure s

simplExp e@(ErrorE {}) =
    return e

simplExp (ReturnE ann e s) =
    ReturnE ann <$> simplExp e <*> pure s

simplExp (BindE wv tau e1 e2 s) = do
    e1' <- simplExp e1
    e2' <- extendWildVars [(wv, tau)] $ simplExp e2
    return $ BindE wv tau e1' e2' s
