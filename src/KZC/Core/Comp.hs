{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Comp
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Core.Comp (
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

    mapMCompLabels,
    uniquifyCompLabels
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Loc

import KZC.Core.Syntax
import KZC.Label
import KZC.Uniq

varC :: (IsLabel l, MonadUnique m) => Var -> m (Comp l)
varC v = do
    l <- gensym "vark"
    return $ Comp [VarC l v (srclocOf v)]

callC :: (IsLabel l, MonadUnique m) => Var -> [Iota] -> [Arg l] -> m (Comp l)
callC f is args = do
    l <- gensym "callk"
    return $ Comp [CallC l f is args (f `srcspan` is `srcspan` args)]

ifC :: (IsLabel l, MonadUnique m) => Exp -> Comp l -> Comp l -> m (Comp l)
ifC e thenc elsec = do
    l <- gensym "ifk"
    return $ ifC' l e thenc elsec

ifC' :: l -> Exp -> Comp l -> Comp l -> Comp l
ifC' l e thenc elsec = Comp [IfC l e thenc elsec (e `srcspan` thenc `srcspan` elsec)]

letC :: (IsLabel l, MonadUnique m) => Var -> Type -> Exp -> m (Comp l)
letC v tau e = letDC $ LetLD (mkBoundVar v) tau e (v `srcspan` e)

letDC :: (IsLabel l, MonadUnique m) => LocalDecl -> m (Comp l)
letDC decl = do
    l <- gensym "letk"
    return $ Comp [LetC l decl (srclocOf decl)]

letDC' :: l -> LocalDecl -> Comp l
letDC' l decl = Comp [LetC l decl (srclocOf decl)]

whileC :: (IsLabel l, MonadUnique m) => Exp -> Comp l -> m (Comp l)
whileC e c  = do
    l <- gensym "whilek"
    return $ Comp [WhileC l e c (e `srcspan` c)]

forC :: (IsLabel l, MonadUnique m) => UnrollAnn -> Var -> Type -> Exp -> Exp -> Comp l -> m (Comp l)
forC ann v tau e1 e2 c = do
    l <- gensym "fork"
    return $ Comp [ForC l ann v tau e1 e2 c (v `srcspan` tau `srcspan` e1 `srcspan` e2 `srcspan` c)]

liftC :: (IsLabel l, MonadUnique m)  => Exp -> m (Comp l)
liftC e = do
    l <- gensym "liftk"
    return $ Comp [LiftC l e (srclocOf e)]

returnC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
returnC e = do
    l <- gensym "returnk"
    return $ Comp [ReturnC l e (srclocOf e)]

bindC :: (IsLabel l, MonadUnique m) => WildVar -> Type -> m (Comp l)
bindC wv tau = do
    l <- gensym "bindk"
    return $ Comp [BindC l wv tau (srclocOf tau)]

bindC' :: l -> WildVar -> Type -> Comp l
bindC' l wv tau = Comp [BindC l wv tau (srclocOf tau)]

takeC ::  (IsLabel l, MonadUnique m) => Type -> m (Comp l)
takeC tau = do
    l <- gensym "takek"
    return $ Comp [TakeC l tau (srclocOf tau)]

takesC :: (IsLabel l, MonadUnique m) => Int -> Type -> m (Comp l)
takesC i tau = do
    l <- gensym "takesk"
    return $ Comp [TakesC l i tau (srclocOf tau)]

emitC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
emitC e = do
    l <- gensym "emitk"
    return $ Comp [EmitC l e (srclocOf e)]

emitsC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
emitsC e = do
    l <- gensym "emitk"
    return $ Comp [EmitsC l e (srclocOf e)]

repeatC :: (IsLabel l, MonadUnique m) => VectAnn -> Comp l -> m (Comp l)
repeatC ann c = do
    l <- gensym "repeatk"
    return $ Comp [RepeatC l ann c (srclocOf c)]

parC :: MonadUnique m => PipelineAnn -> Type -> Comp l -> Comp l -> m (Comp l)
parC ann tau c1 c2 =
    return $ Comp [ParC ann tau c1 c2 (c1 `srcspan` c2)]

mapMCompLabels :: forall l1 l2 m . (Applicative m, MonadUnique m, Ord l1)
              => (l1 -> m l2) -> Comp l1 -> m (Comp l2)
mapMCompLabels f = mlComp
  where
    mlComp :: Comp l1 -> m (Comp l2)
    mlComp (Comp steps) = Comp <$> mlSteps steps

    mlArg :: Arg l1 ->  m (Arg l2)
    mlArg (ExpA e)  = pure $ ExpA e
    mlArg (CompA c) = CompA <$> mlComp c

    mlSteps :: [Step l1] ->  m [Step l2]
    mlSteps []           = return []
    mlSteps (step:steps) = (:) <$> mlStep step <*> mlSteps steps

    mlStep :: Step l1 ->  m (Step l2)
    mlStep (VarC l v s) =
        VarC <$> f l <*> pure v <*> pure s

    mlStep (CallC l v iotas args s) =
        CallC <$> f l <*> pure v <*> pure iotas <*> mapM mlArg args <*> pure s

    mlStep (IfC l e c1 c2 s) =
        IfC <$> f l <*> pure e <*> mlComp c1 <*> mlComp c2 <*> pure s

    mlStep (LetC l decl s) =
        LetC <$> f l <*> pure decl <*> pure s

    mlStep (WhileC l e c s) =
        WhileC <$> f l <*> pure e <*> mlComp c <*> pure s

    mlStep (ForC l ann v tau e1 e2 c s) =
        ForC <$> f l
             <*> pure ann
             <*> pure v
             <*> pure tau
             <*> pure e1
             <*> pure e2
             <*> mlComp c
             <*> pure s

    mlStep (LiftC l e s) =
        LiftC <$> f l <*> pure e <*> pure s

    mlStep (ReturnC l e s) =
        ReturnC <$> f l <*> pure e <*> pure s

    mlStep (BindC l wv tau s) =
        BindC <$> f l <*> pure wv <*> pure tau <*> pure s

    mlStep (TakeC l tau s) =
        TakeC <$> f l <*> pure tau <*> pure s

    mlStep (TakesC l i tau s) =
        TakesC <$> f l <*> pure i <*> pure tau <*> pure s

    mlStep (EmitC l tau s) =
        EmitC <$> f l <*> pure tau <*> pure s

    mlStep (EmitsC l tau s) =
        EmitsC <$> f l <*> pure tau <*> pure s

    mlStep (RepeatC l ann c s) =
        RepeatC <$> f l <*> pure ann <*> mlComp c <*> pure s

    mlStep (ParC ann tau c1 c2 s) =
        ParC ann tau <$> mlComp c1 <*> mlComp c2 <*> pure s

    mlStep LoopC{} =
        fail "mapMCompLabels: saw LoopC"

uniquifyCompLabels :: forall l m . (IsLabel l, Applicative m, MonadUnique m)
                   => Comp l -> m (Comp l)
uniquifyCompLabels = mapMCompLabels uniquify
