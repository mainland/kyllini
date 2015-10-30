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

    reLabel
  ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Reader
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint.Mainland

import KZC.Auto.Syntax
import KZC.Label
import KZC.Uniq

varC :: (Located a, MonadUnique m)
     => Var -> a -> m LComp
varC v a = do
    l <- genLabel "vark"
    return $ Comp [VarC l v (srclocOf a)]

callC :: (Located a, MonadUnique m)
      => Var -> [Iota] -> [Exp] -> a -> m LComp
callC f is es a = do
    l <- genLabel "callk"
    return $ Comp [CallC l f is es (srclocOf a)]

ifC :: (Located a, MonadUnique m)
    => Exp -> LComp -> LComp -> a -> m LComp
ifC e thenc elsec a = do
    l <- genLabel "ifk"
    return $ ifC' l e thenc elsec a

ifC' :: Located a
     => Label -> Exp -> LComp -> LComp -> a -> LComp
ifC' l e thenc elsec a = Comp [IfC l e thenc elsec (srclocOf a)]

letC :: (Located a, MonadUnique m)
     => LocalDecl -> a -> m LComp
letC decl a = do
    l <- genLabel "letk"
    return $ Comp [LetC l decl (srclocOf a)]

letC' :: Located a
      => Label -> LocalDecl -> a -> LComp
letC' l decl a = Comp [LetC l decl (srclocOf a)]

liftC :: (Located a, MonadUnique m)
      => Exp -> a -> m LComp
liftC e a = do
    l <- genLabel "liftk"
    return $ Comp [LiftC l e (srclocOf a)]

returnC :: (Located a, MonadUnique m)
        => Exp -> a -> m LComp
returnC e a = do
    l <- genLabel "returnk"
    return $ Comp [ReturnC l e (srclocOf a)]

bindC :: (Located a, MonadUnique m)
      => BindVar -> a -> m LComp
bindC bv a = do
    l <- genLabel "bindk"
    return $ Comp [BindC l bv (srclocOf a)]

bindC' :: Located a
       => Label -> BindVar -> a -> LComp
bindC' l bv a = Comp [BindC l bv (srclocOf a)]

gotoC :: (Located a, MonadUnique m)
      => Label -> a -> m LComp
gotoC l a = return $ Comp [GotoC l (srclocOf a)]

repeatC :: (Located a, MonadUnique m)
        => Label -> a -> m LComp
repeatC l a = return $ Comp [RepeatC l (srclocOf a)]

takeC :: (Located a, MonadUnique m)
      => Type -> a -> m LComp
takeC tau a = do
    l <- genLabel "takek"
    return $ Comp [TakeC l tau (srclocOf a)]

takesC :: (Located a, MonadUnique m)
       => Int -> Type -> a -> m LComp
takesC i tau a = do
    l <- genLabel "takesk"
    return $ Comp [TakesC l i tau (srclocOf a)]

emitC :: (Located a, MonadUnique m)
      => Exp -> a -> m LComp
emitC e a = do
    l <- genLabel "emitk"
    return $ Comp [EmitC l e (srclocOf a)]

emitsC :: (Located a, MonadUnique m)
       => Exp -> a -> m LComp
emitsC e a = do
    l <- genLabel "emitk"
    return $ Comp [EmitsC l e (srclocOf a)]

parC :: (Located a, MonadUnique m)
     => PipelineAnn -> Type -> LComp -> LComp -> a -> m LComp
parC ann tau c1 c2 a =
    return $ Comp [ParC ann tau c1 c2 (srclocOf a)]

type Re m a = ReaderT (Map Label Label) m a

reLabel :: forall m . (Applicative m, MonadUnique m)
        => Comp Label
        -> m (Comp Label)
reLabel comp =
    runReaderT (rlComp comp) Map.empty
  where
    rlComp :: Comp Label -> Re m (Comp Label)
    rlComp (Comp steps) = Comp <$> rlSteps steps

    rlSteps :: [Step Label] -> Re m [Step Label]
    rlSteps [] =
        return []

    rlSteps (IfC l e c1 c2 s : steps) =
        rl l $ \l' -> do
        step'  <- IfC l' e <$> rlComp c1 <*> rlComp c2 <*> pure s
        steps' <- rlSteps steps
        return $ step' : steps'

    rlSteps (ParC ann tau c1 c2 s : steps) = do
        step'  <- ParC ann tau <$> rlComp c1 <*> rlComp c2 <*> pure s
        steps' <- rlSteps steps
        return $ step' : steps'

    rlSteps (GotoC l s : steps) = do
        theta  <- ask
        step'  <- case Map.lookup l theta of
                    Just l' -> return $ GotoC l' s
                    Nothing -> faildoc $ text "Label" <+> ppr l <+> text "not in scope"
        steps' <- rlSteps steps
        return $ step' : steps'

    rlSteps (RepeatC l s : steps) = do
        theta  <- ask
        step'  <- case Map.lookup l theta of
                    Just l' -> return $ RepeatC l' s
                    Nothing -> faildoc $ text "Label" <+> ppr l <+> text "not in scope"
        steps' <- rlSteps steps
        return $ step' : steps'

    rlSteps (step : steps) = do
        l <- stepLabel step
        rl l $ \l' -> do
        let step' = setStepLabel l' step
        steps' <- rlSteps steps
        return $ step' : steps'
      where

    rl :: Label -> (Label -> Re m a) -> Re m a
    rl l k = do
        l' <- uniquifyLabel l
        local (\env -> Map.insert l l' env) $ k l'
