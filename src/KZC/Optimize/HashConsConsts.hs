{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.HashConsConsts
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.HashConsConsts (
    HCM,
    runHCM,

    hashConsConsts
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Foldable (toList)
import Data.List (partition)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence ((|>)
                     ,Seq)
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Trace
import KZC.Uniq

data HCState = HCState
    { hconsTopConsts :: !(Seq (Var, Const))
    , hconsConstMap  :: !(Map Const Var)
    }

defaultHCState :: HCState
defaultHCState = HCState
    { hconsTopConsts = mempty
    , hconsConstMap  = mempty
    }

newtype HCM m a = HCM { unHCM :: StateT HCState m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState HCState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans HCM where
    lift m = HCM $ lift m

runHCM :: MonadTc m => HCM m a -> m a
runHCM m = evalStateT (unHCM m) defaultHCState

useConst :: forall m . MonadTc m
         => Const
         -> HCM m Exp
useConst c =
    gets (Map.lookup c . hconsConstMap) >>= go
  where
    go :: Maybe Var -> HCM m Exp
    go (Just v) =
        return $ varE v

    go Nothing = do
        v <- gensym "constarr"
        modify $ \s -> s { hconsTopConsts = hconsTopConsts s |> (v, c)
                         , hconsConstMap  = Map.insert c v (hconsConstMap s)
                         }
        return $ varE v

hashConsConsts :: forall l m . (IsLabel l, MonadTc m)
               => Program l
               -> HCM m (Program l)
hashConsConsts (Program decls comp tau) =
    hconsDecls decls $ \decls' -> do
    comp' <- hconsComp comp
    let (structDecls, otherDecls) = partition isStructD decls'
    constDecls <- gets hconsTopConsts >>= mapM topConst . toList
    return $ Program (structDecls ++ constDecls ++ otherDecls) comp' tau
  where
    topConst :: (Var, Const) -> HCM m (Decl l)
    topConst (v, c) = do
        tau <- inferConst noLoc c
        return $ LetD (letD v tau (constE c)) noLoc

hconsDecls :: (IsLabel l, MonadTc m)
           => [Decl l]
           -> ([Decl l] -> HCM m a)
           -> HCM m a
hconsDecls [] k =
    k []

hconsDecls (decl:decls) k =
    hconsDecl  decl  $ \decl'  ->
    hconsDecls decls $ \decls' ->
    k (decl' : decls')

hconsDecl :: (IsLabel l, MonadTc m)
          => Decl l
          -> (Decl l -> HCM m a)
          -> HCM m a
hconsDecl (LetD ldecl l) k =
    hconsLocalDecl True ldecl $ \ldecl' ->
    k $ LetD ldecl' l

hconsDecl (LetFunD f ivs vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    e' <- extendLetFun f ivs vbs tau_ret $
          hconsE False e
    k $ LetFunD f ivs vbs tau_ret e' l
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

hconsDecl decl@(LetExtFunD f ivs vbs tau_ret l) k =
    extendExtFuns [(bVar f, tau)] $
    k decl
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

hconsDecl decl@(LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k decl

hconsDecl (LetCompD v tau comp l) k = do
    comp' <- hconsComp comp
    extendVars [(bVar v, tau)] $
      k $ LetCompD v tau comp' l

hconsDecl (LetFunCompD f ivs vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    comp' <- inSTScope tau_ret $
             inLocalScope $
             hconsComp comp
    k $ LetFunCompD f ivs vbs tau_ret comp' l
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

hconsLocalDecl :: MonadTc m
               => Bool
               -> LocalDecl
               -> (LocalDecl -> HCM m a)
               -> HCM m a
hconsLocalDecl bind (LetLD v tau e l) k = do
    e' <- hconsE bind e
    extendVars [(bVar v, tau)] $
      k $ LetLD v tau e' l

hconsLocalDecl bind (LetRefLD v tau e l) k = do
    e' <- traverse (hconsE bind) e
    extendVars [(bVar v, refT tau)] $
      k $ LetRefLD v tau e' l

hconsComp :: (IsLabel l, MonadTc m) => Comp l -> HCM m (Comp l)
hconsComp (Comp steps) =
    Comp <$> hconsSteps steps

hconsSteps :: forall l m . (IsLabel l, MonadTc m)
           => [Step l]
           -> HCM m [Step l]
hconsSteps [] =
    return []

hconsSteps (LetC l ldecl s : k) =
    hconsLocalDecl False ldecl $ \ldecl' ->
    (LetC l ldecl' s :) <$> hconsSteps k

hconsSteps (step@(BindC _ wv tau _) : k) =
    extendWildVars [(wv, tau)] $
    (step :) <$> hconsSteps k

hconsSteps (step : k) =
    (:) <$> hconsStep step <*> hconsSteps k
  where
    hconsStep :: Step l -> HCM m (Step l)
    hconsStep step@VarC{} =
        pure step

    hconsStep (CallC l v is args s) =
        CallC l v is <$> traverse hconsArg args <*> pure s

    hconsStep (IfC l e c1 c2 s) =
        IfC l <$> hconsE False e <*> hconsComp c1 <*> hconsComp c2 <*> pure s

    hconsStep LetC{} =
        panicdoc $ text "hconsStep: saw LetC"

    hconsStep (WhileC l e comp s) =
        WhileC l <$> hconsE False e <*> hconsComp comp <*> pure s

    hconsStep (ForC l ann v tau e1 e2 comp s) =
        ForC l ann v tau <$> hconsE False e1
                         <*> hconsE False e2
                         <*> extendVars [(v, tau)] (hconsComp comp)
                         <*> pure s

    hconsStep (LiftC l e s) =
        LiftC l <$> hconsE False e <*> pure s

    hconsStep (ReturnC l e s) =
        ReturnC l <$> hconsE False e <*> pure s

    hconsStep BindC{} =
        panicdoc $ text "hconsStep: saw BindC"

    hconsStep step@TakeC{} =
        pure step

    hconsStep step@TakesC{} =
        pure step

    hconsStep (EmitC l e s) =
        EmitC l <$> hconsE False e <*> pure s

    hconsStep (EmitsC l e s) =
        EmitsC l <$> hconsE False e <*> pure s

    hconsStep (RepeatC l ann comp s) =
        RepeatC l ann <$> hconsComp comp <*> pure s

    hconsStep (ParC ann tau c1 c2 s) =
        ParC ann tau <$> hconsComp c1 <*> hconsComp c2 <*> pure s

    hconsStep step@LoopC{} =
        pure step

hconsArg :: (IsLabel l, MonadTc m) => Arg l -> HCM m (Arg l)
hconsArg (ExpA e)     = ExpA <$> hconsE False e
hconsArg (CompA comp) = CompA <$> hconsComp comp

hconsE :: forall m . MonadTc m
       => Bool
       -> Exp
       -> HCM m Exp
hconsE = go
  where
    go :: Bool -> Exp -> HCM m Exp
    go False (ConstE c@ArrayC{} _) =
        useConst c

    go _ e@ConstE{} =
        pure e

    go _ e@VarE{} =
        pure e

    go _ (UnopE op e s) =
        UnopE op <$> hconsE False e <*> pure s

    go _ (BinopE op e1 e2 s) =
        BinopE op <$> hconsE False e1 <*> hconsE False e2 <*> pure s

    go _ (IfE e1 e2 e3 s) =
        IfE <$> hconsE False e1 <*> hconsE False e2 <*> hconsE False e3 <*> pure s

    go _ (LetE ldecl e l) =
        hconsLocalDecl False ldecl $ \ldecl' ->
        LetE ldecl' <$> hconsE True e <*> pure l

    go _ (CallE v is es s) =
        CallE v is <$> traverse (hconsE False) es <*> pure s

    go _ e@DerefE{} =
        pure e

    go _ (AssignE e1 e2 s) =
        AssignE e1 <$> hconsE False e2 <*> pure s

    go _ (WhileE e1 e2 s) =
        WhileE <$> hconsE False e1 <*> hconsE False e2 <*> pure s

    go _ (ForE ann v tau e1 e2 e3 s) =
        ForE ann v tau <$> hconsE False e1
                       <*> hconsE False e2
                       <*> extendVars [(v, tau)] (hconsE False e3)
                       <*> pure s

    go _ (ArrayE es s) =
        ArrayE <$> traverse (hconsE False) es <*> pure s

    go _ (IdxE e1 e2 len s) =
        IdxE <$> hconsE False e1 <*> hconsE False e2 <*> pure len <*> pure s

    go _ (StructE sname flds s) =
        StructE sname <$> traverse mapField flds <*> pure s
      where
        mapField :: (Field, Exp) -> HCM m (Field, Exp)
        mapField (f, e) = (,) <$> pure f <*> hconsE False e

    go _ (ProjE e f s) =
        ProjE <$> hconsE False e <*> pure f <*> pure s

    go _ (PrintE nl es s) =
        PrintE nl <$> traverse (hconsE False) es <*> pure s

    go _ e@ErrorE{} =
        pure e

    go _ (ReturnE ann e s) =
        ReturnE ann <$> hconsE False e <*> pure s

    go _ (BindE wv tau e1 e2 s) =
        BindE wv tau <$> hconsE False e1
                     <*> extendWildVars [(wv, tau)] (hconsE False e2)
                     <*> pure s

    go _ e@LutE{} =
        pure e
