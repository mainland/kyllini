{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Auto.Comp
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Auto.Comp (
    (.>>.),
    (.>>=.),

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
    doneC,

    compLabel,

    genLabel
  ) where

import Control.Monad.Free
import Data.Loc
import Data.Symbol

import KZC.Auto.Syntax
import KZC.Lint.Monad
import KZC.Uniq

infixl 1 .>>., .>>=.

(.>>.) :: Tc r s (LComp c) -> Tc r s (LComp c) -> Tc r s (LComp c)
m1 .>>. m2 = do
    m1' <- m1
    m2' <- m2
    return $ m1' >> m2'

(.>>=.) :: Tc r s (LComp c) -> Tc r s (c -> LComp c) -> Tc r s (LComp c)
m .>>=. k = do
    m' <- m
    k' <- k
    return $ m' >>= k'

varC :: Located a => Var -> a -> Tc r s (LComp c)
varC v a = do
    l <- genLabel "vark"
    return $ liftF $ VarC l v id (srclocOf a)

callC :: Located a => Var -> [Iota] -> [Exp] -> a -> Tc r s (LComp c)
callC f is es a = do
    l <- genLabel "callk"
    return $ liftF $ CallC l f is es id (srclocOf a)

ifC :: Located a => Exp -> LComp c -> LComp c -> a -> Tc r s (LComp c)
ifC ce thenc elsec a = do
    l       <- genLabel "ifk"
    done_th <- doneC a
    done_el <- doneC a
    return $ wrap $ IfC l ce (thenc >>= done_th) (elsec >>= done_el) return (srclocOf a)

ifC' :: Located a => Label -> Exp -> LComp c -> LComp c -> a -> LComp c
ifC' l ce thenc elsec a =
    wrap $ IfC l ce thenc elsec return (srclocOf a)

letC :: Located a => LocalDecl -> a -> Tc r s (LComp c)
letC decl a = do
    l <- genLabel "letk"
    return $ liftF $ LetC l decl undefined (srclocOf a)

letC' :: Located a => Label -> LocalDecl -> a -> LComp c
letC' l decl a = liftF $ LetC l decl undefined (srclocOf a)

liftC :: Located a => Exp -> a -> Tc r s (LComp c)
liftC e a = do
    l <- genLabel "liftk"
    return $ liftF $ LiftC l e id (srclocOf a)

returnC :: Located a => Exp -> a -> Tc r s (LComp c)
returnC e a = do
    l <- genLabel "returnk"
    return $ liftF $ ReturnC l e id (srclocOf a)

bindC :: Located a => BindVar -> a -> Tc r s (c -> LComp c)
bindC bv a = do
    l <- genLabel "bindk"
    return $ \c -> liftF $ BindC l bv c undefined (srclocOf a)

bindC' :: Located a => Label -> BindVar -> a -> (c -> LComp c)
bindC' l bv a = \c -> liftF $ BindC l bv c undefined (srclocOf a)

gotoC :: Located a => Label -> a -> Tc r s (LComp c)
gotoC l a =
    return $ wrap $ GotoC l (srclocOf a)

repeatC :: Located a => Label -> a -> Tc r s (LComp c)
repeatC l a =
    return $ wrap $ RepeatC l (srclocOf a)

takeC :: Located a => Type -> a -> Tc r s (LComp c)
takeC tau a = do
    l <- genLabel "takek"
    return $ liftF $ TakeC l tau id (srclocOf a)

takesC :: Located a => Int -> Type -> a -> Tc r s (LComp c)
takesC i tau a = do
    l <- genLabel "takesk"
    return $ liftF $ TakesC l i tau id (srclocOf a)

emitC :: Located a => Exp -> a -> Tc r s (LComp c)
emitC e a = do
    l <- genLabel "emitk"
    return $ liftF $ EmitC l e undefined (srclocOf a)

emitsC :: Located a => Exp -> a -> Tc r s (LComp c)
emitsC e a = do
    l <- genLabel "emitk"
    return $ liftF $ EmitsC l e undefined (srclocOf a)

parC :: Located a => PipelineAnn -> Type -> LComp c -> LComp c -> a -> Tc r s (LComp c)
parC ann tau c1 c2 a = do
    done_left  <- doneC a
    done_right <- doneC a
    return $ wrap $ ParC ann tau (c1 >>= done_left) (c2 >>= done_right) return (srclocOf a)

doneC :: Located a => a -> Tc r s (c -> LComp c)
doneC a = do
  l <- genLabel "donek"
  return $ \c -> liftF $ DoneC l c (srclocOf a)

compLabel :: forall c r s . LComp c -> Tc r s Label
compLabel (Pure {})   = fail "compLabel: saw Pure"
compLabel (Free comp) = comp0Label comp
  where
    comp0Label :: Comp0 Label c (Comp Label c) -> Tc r s Label
    comp0Label (VarC l _ _ _)         = return l
    comp0Label (CallC l _ _ _ _ _)    = return l
    comp0Label (IfC l _ _ _ _ _)      = return l
    comp0Label (LetC l _ _ _)         = return l
    comp0Label (LiftC l _ _ _)        = return l
    comp0Label (ReturnC l _ _ _)      = return l
    comp0Label (BindC l _ _ _ _)      = return l
    comp0Label (GotoC l _)            = return l
    comp0Label (RepeatC l _)          = return l
    comp0Label (TakeC l _ _ _)        = return l
    comp0Label (TakesC l _ _ _ _)     = return l
    comp0Label (EmitC l _ _ _)        = return l
    comp0Label (EmitsC l _ _ _)       = return l
    comp0Label (ParC _ _ _ right _ _) = compLabel right
    comp0Label (DoneC l _ _)          = return l

genLabel :: String -> Tc r s Label
genLabel s = do
    Uniq u <- newUnique
    return $ Label (intern (s ++ "__" ++ show u))
