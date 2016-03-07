{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Auto.Comp
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Auto.Comp (
    varC,
    callC,
    ifC,
    ifC',
    letC,
    letDC,
    letDC',
    whileC,
    forC,
    liftC,
    returnC,
    bindC,
    bindC',
    takeC,
    takesC,
    emitC,
    emitsC,
    repeatC,
    parC,

    mapCompLabels,
    uniquifyCompLabels
  ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Reader
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map

import KZC.Auto.Syntax
import KZC.Label
import KZC.Uniq

varC :: MonadUnique m => Var -> m LComp
varC v = do
    l <- genLabel "vark"
    return $ Comp [VarC l v (srclocOf v)]

callC :: MonadUnique m => Var -> [Iota] -> [LArg] -> m LComp
callC f is args = do
    l <- genLabel "callk"
    return $ Comp [CallC l f is args (f `srcspan` is `srcspan` args)]

ifC :: MonadUnique m => Exp -> LComp -> LComp -> m LComp
ifC e thenc elsec = do
    l <- genLabel "ifk"
    return $ ifC' l e thenc elsec

ifC' :: Label -> Exp -> LComp -> LComp -> LComp
ifC' l e thenc elsec = Comp [IfC l e thenc elsec (e `srcspan` thenc `srcspan` elsec)]

letC :: MonadUnique m => Var -> Type -> Exp -> m LComp
letC v tau e = letDC $ LetLD (mkBoundVar v) tau e (v `srcspan` e)

letDC :: MonadUnique m => LocalDecl -> m LComp
letDC decl = do
    l <- genLabel "letk"
    return $ Comp [LetC l decl (srclocOf decl)]

letDC' :: Label -> LocalDecl -> LComp
letDC' l decl = Comp [LetC l decl (srclocOf decl)]

whileC :: MonadUnique m => Exp -> LComp -> m LComp
whileC e c  = do
    l <- genLabel "whilek"
    return $ Comp [WhileC l e c (e `srcspan` c)]

forC :: MonadUnique m => UnrollAnn -> Var -> Type -> Exp -> Exp -> LComp -> m LComp
forC ann v tau e1 e2 c = do
    l <- genLabel "fork"
    return $ Comp [ForC l ann v tau e1 e2 c (v `srcspan` tau `srcspan` e1 `srcspan` e2 `srcspan` c)]

liftC :: MonadUnique m  => Exp -> m LComp
liftC e = do
    l <- genLabel "liftk"
    return $ Comp [LiftC l e (srclocOf e)]

returnC :: MonadUnique m => Exp -> m LComp
returnC e = do
    l <- genLabel "returnk"
    return $ Comp [ReturnC l e (srclocOf e)]

bindC :: MonadUnique m => WildVar -> Type -> m LComp
bindC wv tau = do
    l <- genLabel "bindk"
    return $ Comp [BindC l wv tau (srclocOf tau)]

bindC' :: Label -> WildVar -> Type -> LComp
bindC' l wv tau = Comp [BindC l wv tau (srclocOf tau)]

takeC ::  MonadUnique m => Type -> m LComp
takeC tau = do
    l <- genLabel "takek"
    return $ Comp [TakeC l tau (srclocOf tau)]

takesC :: MonadUnique m => Int -> Type -> m LComp
takesC i tau = do
    l <- genLabel "takesk"
    return $ Comp [TakesC l i tau (srclocOf tau)]

emitC :: MonadUnique m => Exp -> m LComp
emitC e = do
    l <- genLabel "emitk"
    return $ Comp [EmitC l e (srclocOf e)]

emitsC :: MonadUnique m => Exp -> m LComp
emitsC e = do
    l <- genLabel "emitk"
    return $ Comp [EmitsC l e (srclocOf e)]

repeatC :: MonadUnique m => VectAnn -> LComp -> m LComp
repeatC ann c = do
    l <- genLabel "repeatk"
    return $ Comp [RepeatC l ann c (srclocOf c)]

parC :: MonadUnique m => PipelineAnn -> Type -> LComp -> LComp -> m LComp
parC ann tau c1 c2 =
    return $ Comp [ParC ann tau c1 c2 (c1 `srcspan` c2)]

type M l1 l2 m a = ReaderT (Map l1 l2) m a

mapCompLabels :: forall l1 l2 m . (Applicative m, MonadUnique m, IsLabel l1)
              => (l1 -> m l2) -> Comp l1 -> m (Comp l2)
mapCompLabels f comp =
    runReaderT (mlComp comp) Map.empty
  where
    mlComp :: Comp l1 -> M l1 l2 m (Comp l2)
    mlComp (Comp steps) = Comp <$> mlSteps steps

    mlArg :: Arg l1 -> M l1 l2 m (Arg l2)
    mlArg (ExpA e)  = pure $ ExpA e
    mlArg (CompA c) = CompA <$> mlComp c

    mlSteps :: [Step l1] -> M l1 l2 m [Step l2]
    mlSteps [] =
        return []

    mlSteps (VarC l v s : steps) =
        ml l $ \l' ->
        (:) <$> pure (VarC l' v s) <*> mlSteps steps

    mlSteps (CallC l v iotas args s : steps) =
        ml l $ \l' ->
        (:) <$> (CallC l' v iotas <$> mapM mlArg args <*> pure s) <*> mlSteps steps

    mlSteps (IfC l e c1 c2 s : steps) =
        ml l $ \l' -> do
        c1' <- mlComp c1
        c2' <- mlComp c2
        (:) <$> pure (IfC l' e c1' c2' s) <*> mlSteps steps

    mlSteps (LetC l decl s : steps) =
        ml l $ \l' ->
        (:) <$> pure (LetC l' decl s) <*> mlSteps steps

    mlSteps (WhileC l e c s : steps) =
        ml l $ \l' -> do
        step'  <- WhileC l' e <$> mlComp c <*> pure s
        steps' <- mlSteps steps
        return $ step' : steps'

    mlSteps (ForC l ann v tau e1 e2 c s : steps) =
        ml l $ \l' -> do
        step'  <- ForC l' ann v tau e1 e2 <$> mlComp c <*> pure s
        steps' <- mlSteps steps
        return $ step' : steps'

    mlSteps (LiftC l e s : steps) =
        ml l $ \l' ->
        (:) <$> pure (LiftC l' e s) <*> mlSteps steps

    mlSteps (ReturnC l e s : steps) =
        ml l $ \l' ->
        (:) <$> pure (ReturnC l' e s) <*> mlSteps steps

    mlSteps (BindC l wv tau s : steps) =
        ml l $ \l' ->
        (:) <$> pure (BindC l' wv tau s) <*> mlSteps steps

    mlSteps (TakeC l tau s : steps) =
        ml l $ \l' ->
        (:) <$> pure (TakeC l' tau s) <*> mlSteps steps

    mlSteps (TakesC l i tau s : steps) =
        ml l $ \l' ->
        (:) <$> pure (TakesC l' i tau s) <*> mlSteps steps

    mlSteps (EmitC l tau s : steps) =
        ml l $ \l' ->
        (:) <$> pure (EmitC l' tau s) <*> mlSteps steps

    mlSteps (EmitsC l tau s : steps) =
        ml l $ \l' ->
        (:) <$> pure (EmitsC l' tau s) <*> mlSteps steps

    mlSteps (RepeatC l ann c s : steps) =
        ml l $ \l' -> do
        step'  <- RepeatC l' ann <$> mlComp c <*> pure s
        steps' <- mlSteps steps
        return $ step' : steps'

    mlSteps (ParC ann tau c1 c2 s : steps) = do
        step'  <- ParC ann tau <$> mlComp c1 <*> mlComp c2 <*> pure s
        steps' <- mlSteps steps
        return $ step' : steps'

    mlSteps (LoopC {} : _) =
        fail "mapCompLabels: saw LoopC"

    ml :: l1 -> (l2 -> M l1 l2 m a) -> M l1 l2 m a
    ml l k = do
        l' <- lift $ f l
        local (\env -> Map.insert l l' env) $ k l'

uniquifyCompLabels :: forall m . (Applicative m, MonadUnique m)
                   => Comp Label -> m (Comp Label)
uniquifyCompLabels comp = mapCompLabels uniquifyLabel comp
