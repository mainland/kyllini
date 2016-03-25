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

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.Trans.Error (runErrorT)
import Data.IORef
import Data.Traversable (traverse)
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Analysis.Lut (lutInfo,
                         shouldLUT)
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Trace
import KZC.Uniq

data AutoEnv = AutoEnv
    { autoTcEnv :: !TcEnv }

defaultAutoEnv :: TcEnv -> AutoEnv
defaultAutoEnv tcenv = AutoEnv tcenv

newtype AutoM a = AutoM { unAutoM :: ReaderT AutoEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader AutoEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runAutoM :: AutoM a -> TcEnv -> KZC a
runAutoM m tcenv =
    runReaderT (unAutoM m) (defaultAutoEnv tcenv)

instance MonadTc AutoM where
    askTc = AutoM $ asks autoTcEnv
    localTc f m =
        AutoM $ local (\env -> env { autoTcEnv = f (autoTcEnv env) }) $
        unAutoM m

autolutProgram :: IsLabel l => Program l -> AutoM (Program l)
autolutProgram (Program decls comp tau) =
    autoDecls decls $ \decls' ->
    Program decls' <$> autoComp comp <*> pure tau

autoDecls :: IsLabel l
          => [Decl l]
          -> ([Decl l] -> AutoM a)
          -> AutoM a
autoDecls [] k =
    k []

autoDecls (decl:decls) k =
    autoDecl  decl  $ \decl'  ->
    autoDecls decls $ \decls' ->
    k (decl' : decls')

autoDecl :: IsLabel l
         => Decl l
         -> (Decl l -> AutoM a)
         -> AutoM a
autoDecl (LetD ldecl l) k =
    autoLocalDecl ldecl $ \ldecl' -> do
    k $ LetD ldecl' l

autoDecl (LetFunD f iotas vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    e' <- extendIVars (iotas `zip` repeat IotaK) $
          extendVars vbs $
          autoE e
    k $ LetFunD f iotas vbs tau_ret e' l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

autoDecl decl@(LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(bVar f, tau)] $
    k decl
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

autoDecl decl@(LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k decl

autoDecl (LetCompD v tau comp l) k = do
    comp' <- autoComp comp
    extendVars [(bVar v, tau)] $ do
    k $ LetCompD v tau comp' l

autoDecl (LetFunCompD f iotas vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    comp' <- extendIVars (iotas `zip` repeat IotaK) $
             extendVars vbs $
             autoComp comp
    k $ LetFunCompD f iotas vbs tau_ret comp' l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

autoLocalDecl :: LocalDecl
              -> (LocalDecl -> AutoM a)
              -> AutoM a
autoLocalDecl (LetLD v tau e l) k = do
    e' <- autoE e
    extendVars [(bVar v, tau)] $ do
    k $ LetLD v tau e' l

autoLocalDecl (LetRefLD v tau e l) k = do
    e' <- traverse autoE e
    extendVars [(bVar v, refT tau)] $ do
    k $ LetRefLD v tau e' l

autoComp :: IsLabel l => Comp l -> AutoM (Comp l)
autoComp (Comp steps) =
    Comp <$> autoSteps steps

autoSteps :: forall l . IsLabel l => [Step l] -> AutoM [Step l]
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
    autoStep :: Step l -> AutoM (Step l)
    autoStep step@(VarC {}) =
        pure step

    autoStep (CallC l v is args s) =
        CallC l v is <$> traverse autoArg args <*> pure s

    autoStep (IfC l e c1 c2 s) =
        IfC l <$> autoE e <*> autoComp c1 <*> autoComp c2 <*> pure s

    autoStep (LetC {}) =
        panicdoc $ text "autoStep: saw LetC"

    autoStep (WhileC l e comp s) =
        WhileC l <$> autoE e <*> autoComp comp <*> pure s

    autoStep (ForC l ann v tau e1 e2 comp s) =
        ForC l ann v tau <$> autoE e1 <*> autoE e2 <*> autoComp comp <*> pure s

    autoStep (LiftC l e s) =
        LiftC l <$> autoE e <*> pure s

    autoStep (ReturnC l e s) =
        ReturnC l <$> autoE e <*> pure s

    autoStep (BindC {}) =
        panicdoc $ text "autoStep: saw BindC"

    autoStep step@(TakeC {}) =
        pure step

    autoStep step@(TakesC {}) =
        pure step

    autoStep (EmitC l e s) =
        EmitC l <$> autoE e <*> pure s

    autoStep (EmitsC l e s) =
        EmitsC l <$> autoE e <*> pure s

    autoStep (RepeatC l ann comp s) =
        RepeatC l ann <$> autoComp comp <*> pure s

    autoStep (ParC ann tau c1 c2 s) =
        ParC ann tau <$> autoComp c1 <*> autoComp c2 <*> pure s

    autoStep step@(LoopC {}) =
        pure step

autoArg :: IsLabel l => Arg l -> AutoM (Arg l)
autoArg (ExpA e)     = ExpA <$> autoE e
autoArg (CompA comp) = CompA <$> autoComp comp

autoE :: Exp -> AutoM Exp
autoE e = do
    traceAutoLUT $ nest 2 $ text "Attempting to LUT:" </> ppr e
    maybe_info <- runErrorT $ lutInfo e
    case maybe_info of
      Left  err  -> do traceAutoLUT $ text "Error:" <+> ppr err
                       go e
      Right info -> do traceAutoLUT $ ppr info
                       should <- shouldLUT e
                       if should
                         then do traceAutoLUT $ nest 2 $ text "Creating LUT for:" </> ppr e
                                 return $ LutE e
                         else go e
  where
    go :: Exp -> AutoM Exp
    go e@(ConstE {}) =
        pure e

    go e@(VarE {}) =
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

    go e@(DerefE {}) =
        pure e

    go (AssignE e1 e2 s) =
        AssignE e1 <$> autoE e2 <*> pure s

    go (WhileE e1 e2 s) =
        WhileE <$> autoE e1 <*> autoE e2 <*> pure s

    go (ForE ann v tau e1 e2 e3 s) =
        ForE ann v tau <$> autoE e1 <*> autoE e2 <*> autoE e3 <*> pure s

    go (ArrayE es s) =
        ArrayE <$> traverse autoE es <*> pure s

    go (IdxE e1 e2 len s) =
        IdxE <$> autoE e1 <*> autoE e2 <*> pure len <*> pure s

    go (StructE sname flds s) =
        StructE sname <$> traverse mapField flds <*> pure s
      where
        mapField :: (Field, Exp) -> AutoM (Field, Exp)
        mapField (f, e) = (,) <$> pure f <*> autoE e

    go (ProjE e f s) =
        ProjE <$> autoE e <*> pure f <*> pure s

    go (PrintE nl es s) =
        PrintE nl <$> traverse autoE es <*> pure s

    go e@(ErrorE {}) =
        pure e

    go (ReturnE ann e s) =
        ReturnE ann <$> autoE e <*> pure s

    go (BindE wv tau e1 e2 s) =
        BindE wv tau  <$> autoE e1 <*> autoE e2 <*> pure s

    go e@(LutE {}) =
        pure e
