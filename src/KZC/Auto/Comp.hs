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
    letC',
    liftC,
    returnC,
    bindC,
    bindC',
    gotoC,
    repeatC,
    takeC,
    takesC,
    emitC,
    emitsC,
    parC,

    compLabel,
    compUsedLabels,

    genLabel
  ) where

import Data.Loc
import Data.Symbol
import qualified Data.Set as Set
import Data.Set (Set)

import KZC.Auto.Syntax
import KZC.Lint.Monad
import KZC.Uniq

varC :: Located a => Var -> a -> Tc r s LComp
varC v a = do
    l <- genLabel "vark"
    return $ Comp [VarC l v (srclocOf a)]

callC :: Located a => Var -> [Iota] -> [Exp] -> a -> Tc r s LComp
callC f is es a = do
    l <- genLabel "callk"
    return $ Comp [CallC l f is es (srclocOf a)]

ifC :: Located a => Exp -> LComp -> LComp -> a -> Tc r s LComp
ifC e thenc elsec a = do
    l <- genLabel "ifk"
    return $ ifC' l e thenc elsec a

ifC' :: Located a => Label -> Exp -> LComp -> LComp -> a -> LComp
ifC' l e thenc elsec a = Comp [IfC l e thenc elsec (srclocOf a)]

letC :: Located a => LocalDecl -> a -> Tc r s LComp
letC decl a = do
    l <- genLabel "letk"
    return $ Comp [LetC l decl (srclocOf a)]

letC' :: Located a => Label -> LocalDecl -> a -> LComp
letC' l decl a = Comp [LetC l decl (srclocOf a)]

liftC :: Located a => Exp -> a -> Tc r s LComp
liftC e a = do
    l <- genLabel "liftk"
    return $ Comp [LiftC l e (srclocOf a)]

returnC :: Located a => Exp -> a -> Tc r s LComp
returnC e a = do
    l <- genLabel "returnk"
    return $ Comp [ReturnC l e (srclocOf a)]

bindC :: Located a => BindVar -> a -> Tc r s LComp
bindC bv a = do
    l <- genLabel "bindk"
    return $ Comp [BindC l bv (srclocOf a)]

bindC' :: Located a => Label -> BindVar -> a -> LComp
bindC' l bv a = Comp [BindC l bv (srclocOf a)]

gotoC :: Located a => Label -> a -> Tc r s LComp
gotoC l a = return $ Comp [GotoC l (srclocOf a)]

repeatC :: Located a => Label -> a -> Tc r s LComp
repeatC l a = return $ Comp [RepeatC l (srclocOf a)]

takeC :: Located a => Type -> a -> Tc r s LComp
takeC tau a = do
    l <- genLabel "takek"
    return $ Comp [TakeC l tau (srclocOf a)]

takesC :: Located a => Int -> Type -> a -> Tc r s LComp
takesC i tau a = do
    l <- genLabel "takesk"
    return $ Comp [TakesC l i tau (srclocOf a)]

emitC :: Located a => Exp -> a -> Tc r s LComp
emitC e a = do
    l <- genLabel "emitk"
    return $ Comp [EmitC l e (srclocOf a)]

emitsC :: Located a => Exp -> a -> Tc r s LComp
emitsC e a = do
    l <- genLabel "emitk"
    return $ Comp [EmitsC l e (srclocOf a)]

parC :: Located a => PipelineAnn -> Type -> LComp -> LComp -> a -> Tc r s LComp
parC ann tau c1 c2 a =
    return $ Comp [ParC ann tau c1 c2 (srclocOf a)]

compLabel :: Comp l -> Tc r s l
compLabel (Comp [])       = fail "compLabel: empty computation"
compLabel (Comp (step:_)) = stepLabel step

compUsedLabels :: forall l . Ord l => Comp l -> Set l
compUsedLabels comp =
    go (unComp comp)
  where
    go :: [Step l] -> Set l
    go []                  = Set.empty
    go (GotoC l _:steps)   = Set.insert l (go steps)
    go (RepeatC l _:steps) = Set.insert l (go steps)
    go (_:steps)           = go steps

stepLabel :: Step l -> Tc r s l
stepLabel (VarC l _ _)         = return l
stepLabel (CallC l _ _ _ _)    = return l
stepLabel (IfC l _ _ _ _)      = return l
stepLabel (LetC l _ _)         = return l
stepLabel (LiftC l _ _)        = return l
stepLabel (ReturnC l _ _)      = return l
stepLabel (BindC l _ _)        = return l
stepLabel (GotoC l _)          = return l
stepLabel (RepeatC l _)        = return l
stepLabel (TakeC l _ _)        = return l
stepLabel (TakesC l _ _ _)     = return l
stepLabel (EmitC l _ _)        = return l
stepLabel (EmitsC l _ _)       = return l
stepLabel (ParC _ _ _ right _) = compLabel right

genLabel :: String -> Tc r s Label
genLabel s = do
    Uniq u <- newUnique
    return $ Label (intern (s ++ "__" ++ show u))
