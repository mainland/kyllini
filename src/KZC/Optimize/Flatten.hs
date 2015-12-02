{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Auto.Flatten
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Flatten (
    Fl,
    evalFl,

    flattenProgram
  ) where

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.Reader
import Data.List (foldl')
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Label
import KZC.Lint.Monad
import KZC.Monad
import KZC.Name
import KZC.Trace
import KZC.Vars

type Fl a = ReaderT FlEnv Tc a

data CompBinding = CompB Var [IVar] [(Var, Type)] Type LComp

data FlEnv = FlEnv
    { compBindings :: Map Var CompBinding }

defaultFlEnv :: FlEnv
defaultFlEnv = FlEnv
    { compBindings = mempty }

evalFl :: Fl a -> TcEnv -> KZC a
evalFl m tcenv = runTc (runReaderT m defaultFlEnv) tcenv

extend :: forall k v a . Ord k
       => (FlEnv -> Map k v)
       -> (FlEnv -> Map k v -> FlEnv)
       -> [(k, v)]
       -> Fl a
       -> Fl a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (FlEnv -> Map k v)
         -> Fl v
         -> k
         -> Fl v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

extendCompBindings :: [(Var, CompBinding)] -> Fl a -> Fl a
extendCompBindings cbs m =
    extend compBindings (\env x -> env { compBindings = x }) cbs m

lookupCompBinding :: Var -> Fl CompBinding
lookupCompBinding v = do
    CompB v ivs vbs tau comp <- lookupBy compBindings onerr v
    comp' <- uniquifyCompLabels comp
    return $ CompB v ivs vbs tau comp'
  where
    onerr = faildoc $ text "Computation" <+> ppr v <+> text "not in scope"

-- | 'flattenProgram' flattens the @main@ computation, inlining all
-- calls/invocations of sub-computations. After the flattening phase, we will
-- not see a 'VarC' or 'CallC' computation in @main@.
flattenProgram :: LProgram -> Fl LProgram
flattenProgram (Program decls comp tau) =
  flattenDecls decls $
  inSTScope tau $
  inLocalScope $ do
  comp' <- withLocContext comp (text "In definition of main") $
           flattenComp comp
  return $ Program decls comp' tau

flattenDecls :: [LDecl] -> Fl a -> Fl a
flattenDecls [] k =
    k

flattenDecls (decl:decls) k =
    flattenDecl decl $ flattenDecls decls k

flattenDecl :: LDecl -> Fl a -> Fl a
flattenDecl (LetD v tau _ _) k =
    extendVars [(bVar v, tau)] k

flattenDecl (LetFunD f iotas vbs tau_ret _ l) k =
    extendVars [(bVar f, tau)] k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

flattenDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(bVar f, tau)] k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

flattenDecl (LetRefD v tau _ _) k =
    extendVars [(bVar v, refT tau)] k

flattenDecl (LetStructD s flds l) k =
    extendStructs [StructDef s flds l] k

flattenDecl (LetCompD v tau comp _) k =
    extendVars [(bVar v, tau)] $
    extendCompBindings [(bVar v, CompB (bVar v) [] [] tau comp)] $
    k

flattenDecl (LetFunCompD f ivs vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $
    extendCompBindings [(bVar f, CompB (bVar f) ivs vbs tau comp)] $
    k
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

flattenLocalDecl :: LocalDecl -> Fl a -> Fl a
flattenLocalDecl (LetLD v tau _ _) k =
    extendVars [(bVar v, tau)] k

flattenLocalDecl (LetRefLD v tau _ _) k =
    extendVars [(bVar v, refT tau)] k

flattenComp :: LComp -> Fl LComp
flattenComp (Comp steps) = Comp <$> flattenSteps steps

flattenSteps :: [LStep] -> Fl [LStep]
flattenSteps [] =
    return []

flattenSteps (step@(LetC _ decl _) : steps) =
    flattenLocalDecl decl $
    (:) <$> pure step <*> flattenSteps steps

flattenSteps (step@(BindC _ bv _) : steps) =
    extendBindVars [bv] $
    (:) <$> pure step <*> flattenSteps steps

flattenSteps (step : steps) =
    (++) <$> flattenStep step <*> flattenSteps steps

flattenStep :: LStep -> Fl [LStep]
flattenStep (VarC l' v _) = do
    (step:steps) <- flattenVarC v
    l            <- stepLabel step
    return $ setStepLabel l' step : subst1 (l /-> l') steps

flattenStep (CallC l' f iotas es _) = do
    (step:steps) <- flattenCallC f iotas es
    l            <- stepLabel step
    return $ setStepLabel l' step : subst1 (l /-> l') steps

flattenStep (IfC l e c1 c2 s) = do
    step <- IfC l e <$> flattenComp c1 <*> flattenComp c2 <*> pure s
    return [step]

flattenStep (LetC {}) =
    faildoc $ text "Cannot flatten let step."

flattenStep (WhileC l e c s) = do
    step <- WhileC l e <$> flattenComp c <*> pure s
    return [step]

flattenStep (ForC l ann v tau e1 e2 c s) = do
    step <- ForC l ann v tau e1 e2 <$> flattenComp c <*> pure s
    return [step]

flattenStep step@(LiftC {}) =
    return [step]

flattenStep step@(ReturnC {}) =
    return [step]

flattenStep (BindC {}) =
    faildoc $ text "Cannot flatten bind step."

flattenStep step@(TakeC {}) =
    return [step]

flattenStep step@(TakesC {}) =
    return [step]

flattenStep step@(EmitC {}) =
    return [step]

flattenStep step@(EmitsC {}) =
    return [step]

flattenStep (RepeatC l ann c s) = do
    step <- RepeatC l ann <$> flattenComp c <*> pure s
    return [step]

flattenStep (ParC ann tau c1 c2 s) = do
    step <- ParC ann tau <$> flattenComp c1 <*> flattenComp c2 <*> pure s
    return [step]

flattenStep (LoopC {}) =
    faildoc $ text "flattenStep: saw LoopC"

flattenVarC :: Var -> Fl [LStep]
flattenVarC v = do
    CompB _ _ _ _ comp <- lookupCompBinding v
    theta              <- instantiateSTScope
    let steps          =  (subst1 theta) (unComp comp)
    flattenSteps steps
  where
    instantiateSTScope :: Fl (Map TyVar Type)
    instantiateSTScope = do
        ST _ _ s  a  b  _ <- lookupVar v
        (s', a', b')      <- askSTIndTypes
        return $ Map.fromList [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']]

flattenCallC :: Var -> [Iota] -> [Exp] -> Fl [LStep]
flattenCallC f iotas es = do
    traceFlatten $ text "flattenCallC:" <+> ppr f
    CompB _ ivs vbs _ comp <- lookupCompBinding f
    extendIVars (ivs `zip` repeat IotaK) $ do
    extendVars vbs $ do
    traceFlatten $ text "flattenCallC:" <+> ppr vbs
    let theta1 =  Map.fromList (ivs `zip` iotas)
    theta2     <- instantiateSTScope
    let steps  =  (subst1 theta2 . subst1 theta1) (unComp comp)
    flattenArgs (map fst vbs `zip` es) $
      withLocContext comp (text "In definition of" <+> ppr f) $
      flattenSteps steps
  where
    instantiateSTScope :: Fl (Map TyVar Type)
    instantiateSTScope = do
        FunT _ _ (ST _ _ s a b _) _ <- lookupVar f
        (s', a', b')                <- askSTIndTypes
        return $ Map.fromList [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']]

flattenArgs :: [(Var, Exp)] -> Fl [LStep] -> Fl [LStep]
flattenArgs [] k =
    k

flattenArgs (arg:args) k =
    flattenArg arg $ flattenArgs args k

flattenArg :: (Var, Exp) -> Fl [LStep] -> Fl [LStep]
flattenArg (v, e) k = do
    tau <- inferExp e
    go tau e
  where
    sloc :: SrcLoc
    sloc = srclocOf e

    go tau e | isPureishT tau = do
        v'    <- mkUniqVar (namedString v) (locOf v)
        l1    <- genLabel "arg_return"
        l2    <- genLabel "arg_bind"
        steps <- k
        return $ unComp $ Comp [ReturnC l1 e sloc, BindC l2 (BindV v' tau) sloc] <> subst1 (v /-> varE v') (Comp steps)

    go tau (CallE f iotas es _) = do
        comp <- Comp <$> flattenCallC f iotas es
        extendCompBindings [(v, CompB v [] [] tau comp)] k

    go tau (VarE v _) = do
        comp <- Comp <$> flattenVarC v
        extendCompBindings [(v, CompB v [] [] tau comp)] k

    go tau e = do
        v'    <- mkUniqVar (namedString v) (locOf v)
        l1    <- genLabel "arg_lift"
        l2    <- genLabel "arg_bind"
        steps <- k
        return $ unComp $ Comp [LiftC l1 e sloc, BindC l2 (BindV v' tau) sloc] <> subst1 (v /-> varE v') (Comp steps)
