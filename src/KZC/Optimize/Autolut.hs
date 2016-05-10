{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Autolut
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Autolut (
    AutoM,
    runAutoM,

    autolutProgram
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Analysis.Lut (lutInfo,
                         shouldLUT)
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Trace
import KZC.Uniq

newtype AutoM m a = AutoM { unAutoM :: m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans AutoM where
    lift = AutoM

runAutoM :: MonadTc m => AutoM m a -> m a
runAutoM = unAutoM

autolutProgram :: (IsLabel l, MonadTc m)
               => Program l
               -> AutoM m (Program l)
autolutProgram (Program decls comp tau) =
    autoDecls decls $ \decls' ->
    Program decls' <$> autoComp comp <*> pure tau

autoDecls :: (IsLabel l, MonadTc m)
          => [Decl l]
          -> ([Decl l] -> AutoM m a)
          -> AutoM m a
autoDecls [] k =
    k []

autoDecls (decl:decls) k =
    autoDecl  decl  $ \decl'  ->
    autoDecls decls $ \decls' ->
    k (decl' : decls')

autoDecl :: (IsLabel l, MonadTc m)
         => Decl l
         -> (Decl l -> AutoM m a)
         -> AutoM m a
autoDecl (LetD ldecl l) k =
    autoLocalDecl ldecl $ \ldecl' ->
    k $ LetD ldecl' l

autoDecl (LetFunD f ivs vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    e' <- extendLetFun f ivs vbs tau_ret $
          autoE e
    k $ LetFunD f ivs vbs tau_ret e' l
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

autoDecl decl@(LetExtFunD f ivs vbs tau_ret l) k =
    extendExtFuns [(bVar f, tau)] $
    k decl
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

autoDecl decl@(LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k decl

autoDecl (LetCompD v tau comp l) k = do
    comp' <- autoComp comp
    extendVars [(bVar v, tau)] $
      k $ LetCompD v tau comp' l

autoDecl (LetFunCompD f ivs vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    comp' <- inSTScope tau_ret $
             inLocalScope $
             autoComp comp
    k $ LetFunCompD f ivs vbs tau_ret comp' l
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

autoLocalDecl :: MonadTc m
              => LocalDecl
              -> (LocalDecl -> AutoM m a)
              -> AutoM m a
autoLocalDecl (LetLD v tau e l) k = do
    e' <- autoE e
    extendVars [(bVar v, tau)] $
      k $ LetLD v tau e' l

autoLocalDecl (LetRefLD v tau e l) k = do
    e' <- traverse autoE e
    extendVars [(bVar v, refT tau)] $
      k $ LetRefLD v tau e' l

autoComp :: (IsLabel l, MonadTc m) => Comp l -> AutoM m (Comp l)
autoComp (Comp steps) =
    Comp <$> autoSteps steps

autoSteps :: forall l m . (IsLabel l, MonadTc m)
          => [Step l]
          -> AutoM m [Step l]
autoSteps [] =
    return []

autoSteps (LetC l ldecl s : k) =
    autoLocalDecl ldecl $ \ldecl' ->
    (LetC l ldecl' s :) <$> autoSteps k

autoSteps (step@(BindC _ wv tau _) : k) =
    extendWildVars [(wv, tau)] $
    (step :) <$> autoSteps k

autoSteps (step : k) =
    (:) <$> autoStep step <*> autoSteps k
  where
    autoStep :: Step l -> AutoM m (Step l)
    autoStep step@VarC{} =
        pure step

    autoStep (CallC l v is args s) =
        CallC l v is <$> traverse autoArg args <*> pure s

    autoStep (IfC l e c1 c2 s) =
        IfC l <$> autoE e <*> autoComp c1 <*> autoComp c2 <*> pure s

    autoStep LetC{} =
        panicdoc $ text "autoStep: saw LetC"

    autoStep (WhileC l e comp s) =
        WhileC l <$> autoE e <*> autoComp comp <*> pure s

    autoStep (ForC l ann v tau e1 e2 comp s) =
        ForC l ann v tau <$> autoE e1
                         <*> autoE e2
                         <*>  extendVars [(v, tau)] (autoComp comp)
                         <*> pure s

    autoStep (LiftC l e s) =
        LiftC l <$> autoE e <*> pure s

    autoStep (ReturnC l e s) =
        ReturnC l <$> autoE e <*> pure s

    autoStep BindC{} =
        panicdoc $ text "autoStep: saw BindC"

    autoStep step@TakeC{} =
        pure step

    autoStep step@TakesC{} =
        pure step

    autoStep (EmitC l e s) =
        EmitC l <$> autoE e <*> pure s

    autoStep (EmitsC l e s) =
        EmitsC l <$> autoE e <*> pure s

    autoStep (RepeatC l ann comp s) =
        RepeatC l ann <$> autoComp comp <*> pure s

    autoStep (ParC ann tau c1 c2 s) =
        ParC ann tau <$> autoComp c1 <*> autoComp c2 <*> pure s

    autoStep step@LoopC{} =
        pure step

autoArg :: (IsLabel l, MonadTc m) => Arg l -> AutoM m (Arg l)
autoArg (ExpA e)     = ExpA <$> autoE e
autoArg (CompA comp) = CompA <$> autoComp comp

autoE :: forall m . MonadTc m
      => Exp
     -> AutoM m Exp
autoE e = do
    traceAutoLUT $ nest 2 $ text "Attempting to LUT:" </> ppr e
    maybe_info <- fmap Right (lutInfo e)
                    `catch` \(ex :: SomeException) -> return (Left ex)
    case maybe_info of
      Left  err  -> do traceAutoLUT $ text "Error:" <+> (text . show) err
                       go e
      Right info -> do traceAutoLUT $ ppr info
                       should <- shouldLUT info e
                       if should
                         then do traceAutoLUT $ nest 2 $ text "Creating LUT for:" </> ppr e
                                 return $ LutE e
                         else go e
  where
    go :: Exp -> AutoM m Exp
    go e@ConstE{} =
        pure e

    go e@VarE{} =
        pure e

    go (UnopE op e s) =
        UnopE op <$> autoE e <*> pure s

    go (BinopE op e1 e2 s) =
        BinopE op <$> autoE e1 <*> autoE e2 <*> pure s

    go (IfE e1 e2 e3 s) =
        IfE <$> autoE e1 <*> autoE e2 <*> autoE e3 <*> pure s

    go (LetE ldecl e l) =
        autoLocalDecl ldecl $ \ldecl' ->
        LetE ldecl' <$> autoE e <*> pure l

    go (CallE v is es s) =
        CallE v is <$> traverse autoE es <*> pure s

    go e@DerefE{} =
        pure e

    go (AssignE e1 e2 s) =
        AssignE e1 <$> autoE e2 <*> pure s

    go (WhileE e1 e2 s) =
        WhileE <$> autoE e1 <*> autoE e2 <*> pure s

    go (ForE ann v tau e1 e2 e3 s) =
        ForE ann v tau <$> autoE e1
                       <*> autoE e2
                       <*> extendVars [(v, tau)] (autoE e3)
                       <*> pure s

    go (ArrayE es s) =
        ArrayE <$> traverse autoE es <*> pure s

    go (IdxE e1 e2 len s) =
        IdxE <$> autoE e1 <*> autoE e2 <*> pure len <*> pure s

    go (StructE sname flds s) =
        StructE sname <$> traverse mapField flds <*> pure s
      where
        mapField :: (Field, Exp) -> AutoM m (Field, Exp)
        mapField (f, e) = (,) <$> pure f <*> autoE e

    go (ProjE e f s) =
        ProjE <$> autoE e <*> pure f <*> pure s

    go (PrintE nl es s) =
        PrintE nl <$> traverse autoE es <*> pure s

    go e@ErrorE{} =
        pure e

    go (ReturnE ann e s) =
        ReturnE ann <$> autoE e <*> pure s

    go (BindE wv tau e1 e2 s) =
        BindE wv tau <$> autoE e1
                     <*> extendWildVars [(wv, tau)] (autoE e2)
                     <*> pure s

    go e@LutE{} =
        pure e
