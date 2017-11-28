{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.LambdaLift
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.LambdaLift (
    runLift,

    liftProgram
  ) where

import Control.Monad.Exception (MonadException(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Foldable (toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq,
                      (|>))

import KZC.Config
import KZC.Expr.Lint
import KZC.Expr.Smart
import KZC.Expr.Syntax
import KZC.Fuel
import KZC.Platform
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

data LiftEnv = LiftEnv
    { funFvs :: Map Var (Var, [Var]) }

defaultLiftEnv :: LiftEnv
defaultLiftEnv = LiftEnv
    { funFvs = mempty }

data LiftState = LiftState
    { topdecls :: !(Seq Decl) }

defaultLiftState :: LiftState
defaultLiftState = LiftState
    { topdecls = mempty }

newtype LiftM m a = LiftM { unLiftM:: ReaderT LiftEnv (StateT LiftState m) a }
    deriving (Functor, Applicative, Monad,
              MonadReader LiftEnv,
              MonadState LiftState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadFuel,
              MonadPlatform,
              MonadTrace,
              MonadTc)

instance MonadTrans LiftM where
    lift  = LiftM . lift . lift

-- | Evaluate a 'Lift' action and return a list of 'C.Definition's.
runLift :: MonadTc m => LiftM m a -> m a
runLift m = evalStateT (runReaderT (unLiftM m) defaultLiftEnv) defaultLiftState

lookupFvs :: MonadTc m => Var -> LiftM m (Set Var)
lookupFvs v = do
  maybe_fvs <- asks (Map.lookup v . funFvs)
  case maybe_fvs of
    Nothing      -> return mempty
    Just (_, vs) -> return (Set.fromList vs)

lookupFunFvs :: MonadTc m => Var -> LiftM m (Var, [Var])
lookupFunFvs f = do
  maybe_fvs <- asks (Map.lookup f . funFvs)
  case maybe_fvs of
    Nothing       -> return (f, mempty)
    Just (f', vs) -> return (f', vs)

extendFunFvs :: MonadTc m => [(Var, (Var, [Var]))] -> LiftM m a -> LiftM m a
extendFunFvs = extendEnv funFvs (\env x -> env { funFvs = x })

withDecl :: MonadTc m => Decl -> (Maybe Decl -> LiftM m a) -> LiftM m a
withDecl decl k = do
  atTop <- isInTopScope
  if atTop
    then do appendTopDecl decl
            k Nothing
    else k (Just decl)

appendTopDecl :: MonadTc m => Decl -> LiftM m ()
appendTopDecl decl =
    modify $ \s -> s { topdecls = topdecls s |> decl }

getTopDecls :: MonadTc m => LiftM m [Decl]
getTopDecls = gets (toList . topdecls)

liftProgram :: MonadTc m => Program -> LiftM m Program
liftProgram (Program imports decls) = do
    []     <- liftDecls decls $ return []
    decls' <- getTopDecls
    return $ Program imports decls'

liftDecls :: forall m . MonadTc m => [Decl] -> LiftM m [Decl] -> LiftM m [Decl]
liftDecls [] k =
    k

liftDecls (decl:decls) k =
    liftDecl decl k'
  where
    k' :: Maybe Decl -> LiftM m [Decl]
    k' Nothing     = liftDecls decls k
    k' (Just decl) = (decl :) <$> liftDecls decls k

liftDecl :: MonadTc m => Decl -> (Maybe Decl -> LiftM m a) -> LiftM m a
liftDecl (StructD struct l) k =
    extendStructs [struct] $ do
    appendTopDecl $ StructD struct l
    k Nothing

liftDecl decl@(LetD v tau e l) k | isPureT tau =
    extendFunFvs [(v, (v, []))] $ do
    e' <- extendLet v tau $
          withSummaryContext decl $
          withFvContext e $
          liftExp e
    extendVars [(v, tau)] $
      withDecl (LetD v tau e' l) k

liftDecl decl@(LetD v tau e l) k = do
    v'   <- uniquifyLifted v
    fvbs <- nonFunFvs decl
    extendFunFvs [(v, (v', map fst fvbs))] $ do
      e' <- extendLet v tau $
            withSummaryContext decl $
            withFvContext e $
            liftExp e
      extendVars [(v, tau)] $ do
        if null fvbs
          then appendTopDecl $ LetD v' tau e' l
          else appendTopDecl $ LetFunD v' [] fvbs tau e' l
        k Nothing

liftDecl decl@(LetRefD v tau maybe_e l) k = do
    maybe_e' <-  withSummaryContext decl $
                 case maybe_e of
                   Nothing -> return Nothing
                   Just e -> Just <$> inLocalScope (liftExp e)
    extendVars [(v, refT tau)] $
      withDecl (LetRefD v tau maybe_e' l) k

liftDecl decl@(LetTypeD alpha kappa _ _) k =
    extendTyVars [(alpha, kappa)] $
    withDecl decl k

liftDecl decl@(LetFunD f ns vbs tau_ret e l) k =
    extendVars [(f, tau)] $ do
    f'   <- uniquifyLifted f
    fvbs <- nonFunFvs decl
    extendFunFvs [(f, (f', map fst fvbs))] $ do
      e' <- withSummaryContext decl $
            extendLetFun f ns vbs tau_ret $
            withFvContext e $
            liftExp e
      appendTopDecl $ LetFunD f' ns (fvbs ++ vbs) tau_ret e' l
      k Nothing
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

liftDecl (LetExtFunD f ns vbs tau_ret l) k =
    extendExtFuns [(f, tau)] $
    extendFunFvs [(f, (f, []))] $ do
    appendTopDecl $ LetExtFunD f ns vbs tau_ret l
    k Nothing
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

nonFunFvs :: MonadTc m => Decl -> LiftM m [(Var, Type)]
nonFunFvs decl = do
    vs        <- (fvs decl <\\>) <$> askTopVars
    recurFvs  <- mapM lookupFvs (Set.toList vs)
    let allVs =  Set.toList $ Set.unions (vs : recurFvs)
    tau_allVs <- mapM lookupVar allVs
    return [(v, tau) | (v, tau) <- allVs `zip` tau_allVs, not (isFunT tau)]

uniquifyLifted :: MonadTc m => Var -> LiftM m Var
uniquifyLifted f = do
    atTop <- isInTopScope
    if atTop
      then return f
      else uniquify f

liftExp :: forall m . MonadTc m => Exp -> LiftM m Exp
liftExp e@ConstE{} =
    pure e

liftExp (VarE v l) = do
    (v', fvs) <- lookupFunFvs v
    if null fvs
      then return $ VarE v' l
      else return $ CallE v' [] (map varE fvs) l

liftExp e@UnopE{} =
    pure e

liftExp e@BinopE{} =
    pure e

liftExp (IfE e1 e2 e3 l) =
    IfE <$> liftExp e1 <*> liftExp e2 <*> liftExp e3 <*> pure l

liftExp (LetE d e l) =
    liftDecl d k
  where
    k :: Maybe Decl -> LiftM m Exp
    k Nothing     = liftExp e
    k (Just decl) = LetE decl <$> liftExp e <*> pure l

liftExp (CallE f taus args l) = do
    (f', fvs) <- lookupFunFvs f
    return $ CallE f' taus (map varE fvs ++ args) l

liftExp (DerefE e l) =
    DerefE <$> liftExp e <*> pure l

liftExp (AssignE e1 e2 l) =
    AssignE <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp e@LowerE{} =
    pure e

liftExp (WhileE e1 e2 l) =
    WhileE <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp (ForE ann v tau int e l) =
    ForE ann v tau <$> traverse liftExp int
                   <*> extendVars [(v, tau)] (liftExp e)
                   <*> pure l

liftExp (ArrayE es l) =
    ArrayE <$> mapM liftExp es <*> pure l

liftExp (IdxE e1 e2 len l) =
    IdxE <$> liftExp e1 <*> liftExp e2 <*> pure len <*> pure l

liftExp (StructE s taus flds l) =
    StructE s taus <$> mapM liftField flds <*> pure l
  where
    liftField :: (Field, Exp) -> LiftM m (Field, Exp)
    liftField (f, e) = (,) <$> pure f <*> liftExp e

liftExp (ProjE e f l) =
    ProjE <$> liftExp e <*> pure f <*> pure l

liftExp (CastE tau e l) =
    CastE tau <$> liftExp e <*> pure l

liftExp (BitcastE tau e l) =
    BitcastE tau <$> liftExp e <*> pure l

liftExp (PrintE nl es l) =
    PrintE nl <$> mapM liftExp es <*> pure l

liftExp e@ErrorE{} =
    pure e

liftExp (ReturnE ann e l) =
    ReturnE ann <$> liftExp e <*> pure l

liftExp (BindE v tau e1 e2 l) =
    BindE v tau <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp e@TakeE{} =
    pure e

liftExp e@TakesE{} =
    pure e

liftExp (EmitE e l) =
    EmitE <$> liftExp e <*> pure l

liftExp (EmitsE e l) =
    EmitsE <$> liftExp e <*> pure l

liftExp (RepeatE ann e l) =
    RepeatE ann <$> liftExp e <*> pure l

liftExp (ParE ann tau e1 e2 l) =
    ParE ann  tau <$> liftExp e1 <*> liftExp e2 <*> pure l
