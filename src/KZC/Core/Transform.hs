-- |
-- Module      : KZC.Core.Transform
-- Copyright   : (c) 2016 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module KZC.Core.Transform (
    Transform(..),

    transProgram,
    transDecls,
    transDecl,
    transLocalDecl,
    transComp,
    transSteps,
    transStep,
    transArg,
    transExp
  ) where

import Text.PrettyPrint.Mainland

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error

class MonadTc m => Transform m where
    programT :: Program l -> m (Program l)
    programT = transProgram

    declsT :: Transform m => [Decl l] -> m a -> m ([Decl l], a)
    declsT = transDecls

    declT :: Transform m => Decl l -> m a -> m (Decl l, a)
    declT = transDecl

    localDeclT :: LocalDecl -> m a -> m (LocalDecl, a)
    localDeclT = transLocalDecl

    compT :: Comp l -> m (Comp l)
    compT = transComp

    stepsT :: [Step l] -> m [Step l]
    stepsT = transSteps

    stepT :: Step l -> m (Step l)
    stepT = transStep

    argT :: Arg l -> m (Arg l)
    argT = transArg

    expT :: Exp -> m Exp
    expT = transExp

transProgram :: Transform m => Program l -> m (Program l)
transProgram (Program decls comp tau) = do
  (decls', comp') <-
      declsT decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      compT comp
  return $ Program decls' comp' tau

transDecls :: Transform m => [Decl l] -> m a -> m ([Decl l], a)
transDecls [] m = do
    x <- m
    return ([], x)

transDecls (d:ds) m = do
    (d', (ds', x)) <- declT d $ declsT ds m
    return (d':ds', x)

transDecl :: Transform m => Decl l -> m a -> m (Decl l, a)
transDecl (LetD decl s) m = do
    (decl', x) <- localDeclT decl m
    return (LetD decl' s, x)

transDecl (LetFunD f iotas vbs tau_ret e l) m =
    extendVars [(bVar f, tau)] $ do
    e' <- extendLetFun f iotas vbs tau_ret $
          expT e
    x  <- m
    return (LetFunD f iotas vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl (LetExtFunD f iotas vbs tau_ret l) m = do
    x <- extendVars [(bVar f, tau)] m
    return (LetExtFunD f iotas vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl decl@(LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (decl, x)

transDecl (LetCompD v tau comp l) m = do
    comp' <- extendLet v tau $
             compT comp
    x     <- extendVars [(bVar v, tau)] m
    return (LetCompD v tau comp' l, x)

transDecl (LetFunCompD f iotas vbs tau_ret comp l) m =
    extendVars [(bVar f, tau)] $ do
    comp' <- extendLetFun f iotas vbs tau_ret $
             compT comp
    x     <- m
    return (LetFunCompD f iotas vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transLocalDecl :: Transform m => LocalDecl -> m a -> m (LocalDecl, a)
transLocalDecl (LetLD v tau e s) m = do
    e' <- expT e
    x  <- extendVars [(bVar v, tau)] m
    return (LetLD v tau e' s, x)

transLocalDecl (LetRefLD v tau e s) m = do
    e' <- traverse expT e
    x  <- extendVars [(bVar v, refT tau)] m
    return (LetRefLD v tau e' s, x)

transComp :: Transform m => Comp l -> m (Comp l)
transComp (Comp steps) = Comp <$> stepsT steps

transSteps :: Transform m => [Step l] -> m [Step l]
transSteps [] =
    return []

transSteps (LetC l decl s : steps) = do
    (decl', steps') <- localDeclT decl $ stepsT steps
    return $ LetC l decl' s : steps'

transSteps (step@(BindC _ WildV _ _) : steps) =
    (:) <$> pure step <*> stepsT steps

transSteps (BindC l (TameV v) tau s : steps) = do
    steps' <- extendVars [(bVar v, tau)] $
              stepsT steps
    return $ BindC l (TameV v) tau s : steps'

transSteps (step : steps) =
    (:) <$> stepT step <*> stepsT steps

transStep :: Transform m => Step l -> m (Step l)
transStep step@VarC{} =
    pure step

transStep (CallC l f iotas args s) =
    CallC l f <$> pure iotas <*> mapM argT args <*> pure s

transStep (IfC l e c1 c2 s) =
    IfC l <$> expT e <*> compT c1 <*> compT c2 <*> pure s

transStep LetC{} =
    faildoc $ text "Cannot trans let step."

transStep (WhileC l e c s) =
    WhileC l <$> expT e <*> compT c <*> pure s

transStep (ForC l ann v tau e1 e2 c s) =
    ForC l ann v tau <$> expT e1
                     <*> expT e2
                     <*> extendVars [(v, tau)] (compT c)
                     <*> pure s

transStep (LiftC l e s) =
    LiftC l <$> expT e <*> pure s

transStep (ReturnC l e s) =
    ReturnC l <$> expT e <*> pure s

transStep BindC{} =
    faildoc $ text "Cannot trans bind step."

transStep step@TakeC{} =
    return step

transStep step@TakesC{} =
    return step

transStep (EmitC l e s) =
    EmitC l <$> expT e <*> pure s

transStep (EmitsC l e s) =
    EmitsC l <$> expT e <*> pure s

transStep (RepeatC l ann c s) =
    RepeatC l ann <$> compT c <*> pure s

transStep (ParC ann tau c1 c2 s) =
    ParC ann tau <$> compT c1 <*> compT c2 <*> pure s

transStep LoopC{} =
    faildoc $ text "transStep: saw LoopC"

transArg :: Transform m => Arg l -> m (Arg l)
transArg (ExpA e)  = ExpA  <$> expT e
transArg (CompA c) = CompA <$> compT c

transExp :: Transform m => Exp -> m Exp
transExp e@ConstE{} =
    pure e

transExp e@VarE{} =
    pure e

transExp (UnopE op e s) =
    UnopE op <$> expT e <*> pure s

transExp (BinopE op e1 e2 s) =
    BinopE op <$> expT e1 <*> expT e2 <*> pure s

transExp (IfE e1 e2 e3 s) =
    IfE <$> expT e1 <*> expT e2 <*> expT e3 <*> pure s

transExp (LetE decl e s) = do
    (decl', e') <- localDeclT decl $ expT e
    return $ LetE decl' e' s

transExp (CallE f iotas es s) =
    CallE f iotas <$> mapM expT es <*> pure s

transExp (DerefE e s) =
    DerefE <$> expT e <*> pure s

transExp (AssignE e1 e2 s) =
    AssignE <$> expT e1 <*> expT e2 <*> pure s

transExp (WhileE e1 e2 s) =
    WhileE <$> expT e1 <*> expT e2 <*> pure s

transExp (ForE ann v tau e1 e2 e3 s) =
    ForE ann v tau <$> expT e1
                   <*> expT e2
                   <*> extendVars [(v, tau)] (expT e3)
                   <*> pure s

transExp (ArrayE es s) =
    ArrayE <$> mapM expT es <*> pure s

transExp (IdxE e1 e2 len s) =
    IdxE <$> expT e1 <*> expT e2 <*> pure len <*> pure s

transExp (StructE struct flds s) =
    StructE struct <$> (zip fs <$> mapM expT es) <*> pure s
  where
    (fs, es) = unzip flds

transExp (ProjE e f s) =
    ProjE <$> expT e <*> pure f <*> pure s

transExp (PrintE nl es s) =
    PrintE nl <$> mapM expT es <*> pure s

transExp e@ErrorE{} =
    return e

transExp (ReturnE ann e s) =
    ReturnE ann <$> expT e <*> pure s

transExp (BindE WildV tau e1 e2 s) =
    BindE WildV tau <$> expT e1 <*> expT e2 <*> pure s

transExp (BindE (TameV v) tau e1 e2 s) =
    BindE (TameV v) tau <$> expT e1
                        <*> extendVars [(bVar v, tau)] (expT e2)
                        <*> pure s

transExp (LutE e) =
    LutE <$> expT e
