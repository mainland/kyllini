{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : KZC.Core.Transform
-- Copyright   : (c) 2016-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Core.Transform (
    TransformExp(..),
    TransformComp(..),

    transProgram,
    transDecls,
    transDecl,
    transLocalDecl,
    transComp,
    transSteps,
    transStep,
    transArg,
    transConst,
    transExp,
    transType,
    transField
  ) where

import Data.Maybe (fromMaybe)
import Text.PrettyPrint.Mainland

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Util.Error

{- Note [Generic Transformations]

The two type classes @TransformExp@ and @TransformComp@ provide a framework for
generic transforms over core language terms. Because transformations are often
type-directed and types may be transformed as well, we maintain the invariant
that the type environment contains only /untransformed/ types.
-}

class MonadTc m => TransformExp m where
    typeT :: Type -> m Type
    typeT = transType

    omegaT :: Omega -> m Omega
    omegaT = transOmega

    viewT :: View -> m View
    viewT = transView

    localDeclT :: LocalDecl -> m a -> m (LocalDecl, a)
    localDeclT = transLocalDecl

    constT :: Const -> m Const
    constT = transConst

    expT :: Exp -> m Exp
    expT = transExp

    genT :: Gen -> m Gen
    genT = transGen

class TransformExp m => TransformComp l m where
    programT :: Program l -> m (Program l)
    programT = transProgram

    mainT :: Main l -> m (Main l)
    mainT = transMain

    declsT :: [Decl l] -> m a -> m ([Decl l], a)
    declsT = transDecls

    declT :: Decl l -> m a -> m (Decl l, a)
    declT = transDecl

    compT :: Comp l -> m (Comp l)
    compT = transComp

    stepsT :: [Step l] -> m [Step l]
    stepsT = transSteps

    stepT :: Step l -> m (Step l)
    stepT = transStep

    argT :: Arg l -> m (Arg l)
    argT = transArg

transProgram :: TransformComp l m => Program l -> m (Program l)
transProgram (Program imports decls main) = do
    (decls', main') <- declsT decls $
                       traverse mainT main
    return $ Program imports decls' main'

transMain :: TransformComp l m => Main l -> m (Main l)
transMain (Main comp tau) = do
    comp' <- inSTScope tau $
             inLocalScope $
             withLocContext comp (text "In definition of main") $
             compT comp
    tau'  <- typeT tau
    return $ Main comp' tau'

transDecls :: TransformComp l m => [Decl l] -> m a -> m ([Decl l], a)
transDecls [] m = do
    x <- m
    return ([], x)

transDecls (d:ds) m = do
    (d', (ds', x)) <- declT d $ declsT ds m
    return (d':ds', x)

transDecl :: TransformComp l m => Decl l -> m a -> m (Decl l, a)
transDecl (StructD s tvks flds l) m = do
    flds' <- mapM transField flds
    x     <- extendStructs [StructDef s tvks flds l] m
    return (StructD s tvks flds' l, x)

transDecl (LetD decl s) m = do
    (decl', x) <- localDeclT decl m
    return (LetD decl' s, x)

transDecl (LetFunD f tvks vbs tau_ret e l) m = do
    vbs'     <- mapM transField vbs
    tau_ret' <- typeT tau_ret
    extendVars [(bVar f, tau)] $ do
      e' <- extendLetFun f tvks vbs tau_ret $
            expT e
      x  <- m
      return (LetFunD f tvks vbs' tau_ret' e' l, x)
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

transDecl (LetExtFunD f tvks vbs tau_ret l) m = do
    vbs'     <- mapM transField vbs
    tau_ret' <- typeT tau_ret
    x        <- extendExtFuns [(bVar f, tau)] m
    return (LetExtFunD f tvks vbs' tau_ret' l, x)
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

transDecl (LetCompD v tau comp l) m = do
    tau'  <- typeT tau
    comp' <- extendLet v tau $
             compT comp
    x     <- extendVars [(bVar v, tau)] m
    return (LetCompD v tau' comp' l, x)

transDecl (LetFunCompD f tvks vbs tau_ret comp l) m = do
    vbs'     <- mapM transField vbs
    tau_ret' <- typeT tau_ret
    extendVars [(bVar f, tau)] $ do
      comp' <- extendLetFun f tvks vbs tau_ret $
               compT comp
      x     <- m
      return (LetFunCompD f tvks vbs' tau_ret' comp' l, x)
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

transComp :: TransformComp l m => Comp l -> m (Comp l)
transComp comp = do
    steps' <- stepsT (unComp comp)
    return comp{ unComp = steps' }

transSteps :: TransformComp l m => [Step l] -> m [Step l]
transSteps [] =
    return []

transSteps (LetC l decl s : steps) = do
    (decl', steps') <- localDeclT decl $ stepsT steps
    return $ LetC l decl' s : steps'

transSteps (BindC l WildV tau s : steps) =
    (:) <$> (BindC l WildV <$> typeT tau <*> pure s)
        <*> stepsT steps

transSteps (BindC l (TameV v) tau s : steps) =
    (:) <$> (BindC l (TameV v) <$> typeT tau <*> pure s)
        <*> extendVars [(bVar v, tau)] (stepsT steps)

transSteps (step : steps) =
    (:) <$> stepT step <*> stepsT steps

transStep :: TransformComp l m => Step l -> m (Step l)
transStep step@VarC{} =
    pure step

transStep (CallC l f taus args s) =
    CallC l f <$> mapM typeT taus <*> mapM argT args <*> pure s

transStep (IfC l e c1 c2 s) =
    IfC l <$> expT e <*> compT c1 <*> compT c2 <*> pure s

transStep LetC{} =
    faildoc $ text "Cannot trans let step."

transStep (WhileC l e c s) =
    WhileC l <$> expT e <*> compT c <*> pure s

transStep (ForC l ann v tau gint c s) =
    ForC l ann v tau <$> traverse expT gint
                     <*> extendVars [(v, tau)] (compT c)
                     <*> pure s

transStep (LiftC l e s) =
    LiftC l <$> expT e <*> pure s

transStep (ReturnC l e s) =
    ReturnC l <$> expT e <*> pure s

transStep BindC{} =
    faildoc $ text "Cannot trans bind step."

transStep (TakeC l tau s) =
    TakeC l <$> typeT tau <*> pure s

transStep (TakesC l n tau s) =
    TakesC l n <$> typeT tau <*> pure s

transStep (EmitC l e s) =
    EmitC l <$> expT e <*> pure s

transStep (EmitsC l e s) =
    EmitsC l <$> expT e <*> pure s

transStep (RepeatC l ann c s) =
    RepeatC l ann <$> compT c <*> pure s

transStep (ParC ann b c1 c2 sloc) = do
    (s, a, c) <- askSTIndices
    ParC ann <$> typeT b
             <*> localSTIndices (Just (s, a, b)) (compT c1)
             <*> localSTIndices (Just (b, b, c)) (compT c2)
             <*> pure sloc

transArg :: TransformComp l m => Arg l -> m (Arg l)
transArg (ExpA e)  = ExpA  <$> expT e
transArg (CompA c) = CompA <$> compT c

transType :: TransformExp m => Type -> m Type
transType tau@UnitT{}   = pure tau
transType tau@BoolT{}   = pure tau
transType tau@IntT{}    = pure tau
transType tau@FixT{}    = pure tau
transType tau@FloatT{}  = pure tau
transType tau@StringT{} = pure tau
transType tau@StructT{} = pure tau

transType (ArrT tau1 tau2 s) =
    ArrT <$> typeT tau1 <*> typeT tau2 <*> pure s

transType (ST omega tau1 tau2 tau3 s) =
    ST <$> omegaT omega <*> typeT tau1 <*> typeT tau2 <*> typeT tau3 <*> pure s

transType (RefT tau s) =
    RefT <$> typeT tau <*> pure s

transType (FunT taus tau s) =
    FunT <$> mapM typeT taus <*> typeT tau <*> pure s

transType tau@NatT{} =
    pure tau

transType (ForallT tvks tau s) =
    ForallT tvks <$> extendTyVars tvks (typeT tau) <*> pure s

transType tau@(TyVarT alpha _s) =
    fromMaybe tau <$> maybeLookupTyVarType alpha

transOmega :: TransformExp m => Omega -> m Omega
transOmega T       = pure T
transOmega (C tau) = C <$> typeT tau

transField :: TransformExp m => (a, Type) -> m (a, Type)
transField (x, tau) = (,) <$> pure x <*> typeT tau

transFieldConst :: TransformExp m => (a, Const) -> m (a, Const)
transFieldConst (x, c) = (,) <$> pure x <*> constT c

transLocalDecl :: TransformExp m => LocalDecl -> m a -> m (LocalDecl, a)
transLocalDecl (LetLD v tau e s) m = do
    e'   <- expT e
    tau' <- typeT tau
    x    <- extendVars [(bVar v, tau)] m
    return (LetLD v tau' e' s, x)

transLocalDecl (LetRefLD v tau e s) m = do
    e'   <- traverse expT e
    tau' <- typeT tau
    x    <- extendVars [(bVar v, refT tau)] m
    return (LetRefLD v tau' e' s, x)

transLocalDecl (LetViewLD v tau vw s) m = do
    vw'  <- viewT vw
    tau' <- typeT tau
    x    <- extendVars [(bVar v, tau)] m
    return (LetViewLD v tau' vw' s, x)

transView :: TransformExp m => View -> m View
transView (IdxVW v e len s) =
    IdxVW v <$> expT e <*> pure len <*> pure s

transConst :: TransformExp m => Const -> m Const
transConst c@UnitC{}        = return c
transConst c@BoolC{}        = return c
transConst c@FixC{}         = return c
transConst c@IntC{}         = return c
transConst c@FloatC{}       = return c
transConst c@StringC{}      = return c
transConst (ArrayC v)       = ArrayC <$> traverse constT v
transConst (ReplicateC i c) = ReplicateC i <$> constT c
transConst (EnumC tau)      = EnumC <$> typeT tau

transConst (StructC struct taus fs) =
    StructC struct <$> mapM typeT taus <*> mapM transFieldConst fs

transExp :: TransformExp m => Exp -> m Exp
transExp (ConstE c s) =
    ConstE <$> constT c <*> pure s

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

transExp (CallE f taus es s) =
    CallE f <$> mapM typeT taus <*> mapM expT es <*> pure s

transExp (DerefE e s) =
    DerefE <$> expT e <*> pure s

transExp (AssignE e1 e2 s) =
    AssignE <$> expT e1 <*> expT e2 <*> pure s

transExp (WhileE e1 e2 s) =
    WhileE <$> expT e1 <*> expT e2 <*> pure s

transExp (ForE ann v tau gint e s) = do
    tau' <- typeT tau
    ForE ann v tau' <$> traverse expT gint
                    <*> extendVars [(v, tau)] (expT e)
                    <*> pure s

transExp (ArrayE es s) =
    ArrayE <$> mapM expT es <*> pure s

transExp (IdxE e1 e2 len s) =
    IdxE <$> expT e1 <*> expT e2 <*> pure len <*> pure s

transExp (StructE struct taus flds s) =
    StructE struct taus <$> (zip fs <$> mapM expT es) <*> pure s
  where
    (fs, es) = unzip flds

transExp (ProjE e f s) =
    ProjE <$> expT e <*> pure f <*> pure s

transExp (CastE tau e s) =
    CastE <$> typeT tau <*> expT e <*> pure s

transExp (BitcastE tau e s) =
    BitcastE <$> typeT tau <*> expT e <*> pure s

transExp (PrintE nl es s) =
    PrintE nl <$> mapM expT es <*> pure s

transExp e@ErrorE{} =
    return e

transExp (ReturnE ann e s) =
    ReturnE ann <$> expT e <*> pure s

transExp (BindE WildV tau e1 e2 s) = do
    tau' <- typeT tau
    BindE WildV tau' <$> expT e1 <*> expT e2 <*> pure s

transExp (BindE (TameV v) tau e1 e2 s) = do
    tau' <- typeT tau
    BindE (TameV v) tau' <$> expT e1
                         <*> extendVars [(bVar v, tau)] (expT e2)
                         <*> pure s

transExp (LutE sz e) =
    LutE sz <$> expT e

transExp (GenE e gs s) =
    checkGenerators gs $ \_ ->
    GenE <$> expT e <*> mapM genT gs <*> pure s

transGen :: TransformExp m => Gen -> m Gen
transGen (GenG v tau c s)    = GenG v <$> typeT tau <*> pure c <*> pure s
transGen (GenRefG v tau c s) = GenRefG v <$> typeT tau <*> pure c <*> pure s
