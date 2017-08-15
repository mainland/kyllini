{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Comp
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Core.Comp (
    varC,
    callC,
    ifC,
    letC,
    letrefC,
    localdeclC,
    localdeclsC,
    whileC,
    forC,
    forGenC,
    liftC,
    returnC,
    bindC,
    takeC,
    takesC,
    emitC,
    emitsC,
    repeatC,
    parC
  ) where

import Data.Loc

import KZC.Core.Syntax
import KZC.Label
import KZC.Util.Uniq

varC :: (IsLabel l, MonadUnique m) => Var -> m (Comp l)
varC v = do
    l <- gensym "vark"
    return $ mkComp [VarC l v (srclocOf v)]

callC :: (IsLabel l, MonadUnique m) => Var -> [Type] -> [Arg l] -> m (Comp l)
callC f taus args = do
    l <- gensym "callk"
    return $ mkComp [CallC l f taus args (f `srcspan` taus `srcspan` args)]

ifC :: (IsLabel l, MonadUnique m) => Exp -> Comp l -> Comp l -> m (Comp l)
ifC e thenc elsec = do
    l <- gensym "ifk"
    return $ mkComp [IfC l e thenc elsec (e `srcspan` thenc `srcspan` elsec)]

letC :: (IsLabel l, MonadUnique m) => Var -> Type -> Exp -> m (Comp l)
letC v tau e = localdeclC $ LetLD (mkBoundVar v) tau e (v `srcspan` e)

letrefC :: (IsLabel l, MonadUnique m) => Var -> Type -> Maybe Exp -> m (Comp l)
letrefC v tau e = localdeclC $ LetRefLD (mkBoundVar v) tau e (v `srcspan` e)

localdeclC :: (IsLabel l, MonadUnique m) => LocalDecl -> m (Comp l)
localdeclC decl = do
    l <- gensym "letk"
    return $ mkComp [LetC l decl (srclocOf decl)]

localdeclsC :: (IsLabel l, MonadUnique m) => [LocalDecl] -> m (Comp l)
localdeclsC decls = mconcat <$> mapM localdeclC decls

whileC :: (IsLabel l, MonadUnique m) => Exp -> Comp l -> m (Comp l)
whileC e c  = do
    l <- gensym "whilek"
    return $ mkComp [WhileC l e c (e `srcspan` c)]

forC :: (IsLabel l, MonadUnique m) => UnrollAnn -> Var -> Type -> Exp -> Exp -> Comp l -> m (Comp l)
forC ann v tau e1 e2 c =
    forGenC ann v tau gint c
  where
    gint :: GenInterval Exp
    gint = StartLen e1 e2 (e1 `srcspan` e2)

forGenC :: (IsLabel l, MonadUnique m) => UnrollAnn -> Var -> Type -> GenInterval Exp -> Comp l -> m (Comp l)
forGenC ann v tau gint c = do
    l <- gensym "fork"
    return $ mkComp [ForC l ann v tau gint c (v `srcspan` tau `srcspan` gint `srcspan` c)]

liftC :: (IsLabel l, MonadUnique m)  => Exp -> m (Comp l)
liftC e = do
    l <- gensym "liftk"
    return $ mkComp [LiftC l e (srclocOf e)]

returnC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
returnC e = do
    l <- gensym "returnk"
    return $ mkComp [ReturnC l e (srclocOf e)]

bindC :: (IsLabel l, MonadUnique m) => WildVar -> Type -> m (Comp l)
bindC wv tau = do
    l <- gensym "bindk"
    return $ mkComp [BindC l wv tau (srclocOf tau)]

takeC ::  (IsLabel l, MonadUnique m) => Type -> m (Comp l)
takeC tau = do
    l <- gensym "takek"
    return $ mkComp [TakeC l tau (srclocOf tau)]

takesC :: (IsLabel l, MonadUnique m) => Nat -> Type -> m (Comp l)
takesC n tau = do
    l <- gensym "takesk"
    return $ mkComp [TakesC l n tau (srclocOf tau)]

emitC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
emitC e = do
    l <- gensym "emitk"
    return $ mkComp [EmitC l e (srclocOf e)]

emitsC :: (IsLabel l, MonadUnique m) => Exp -> m (Comp l)
emitsC e = do
    l <- gensym "emitk"
    return $ mkComp [EmitsC l e (srclocOf e)]

repeatC :: (IsLabel l, MonadUnique m) => VectAnn Nat -> Comp l -> m (Comp l)
repeatC ann c = do
    l <- gensym "repeatk"
    return $ mkComp [RepeatC l ann c (srclocOf c)]

parC :: MonadUnique m => PipelineAnn -> Type -> Comp l -> Comp l -> m (Comp l)
parC ann tau c1 c2 =
    return $ mkComp [ParC ann tau c1 c2 (c1 `srcspan` c2)]
