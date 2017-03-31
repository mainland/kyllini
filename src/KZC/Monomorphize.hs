{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  KZC.Monomorphize
-- Copyright   :  (c) 2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Monomorphize (
    monomorphizeProgram
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.Ref (MonadRef(..))
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
import Data.IORef
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq,
                      (|>))
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Util.Error
import KZC.Util.Pretty
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

-- | Generate a monomorphized version of a function. Called with all type
-- arguments /not/ of kind Nat.
type FunGen l m = [Type] -> MonoM l m Var

-- | Cache of monomorphized versions of a function.
type Cache = IORef (Map [Type] Var)

data MonoEnv l m = MonoEnv
    { funGens   :: Map Var (FunGen l m)
    , funCaches :: Map Var Cache
    }

defaultMonoEnv :: MonoEnv l m
defaultMonoEnv = MonoEnv
    { funGens   = mempty
    , funCaches = mempty
    }

newtype MonoState l = MonoState { topdecls :: Seq (Decl l) }

defaultMonoState :: MonoState l
defaultMonoState = MonoState { topdecls = mempty }

newtype MonoM l m a = MonoM { unMonoM:: ReaderT (MonoEnv l m) (StateT (MonoState l) m) a }
    deriving (Functor, Applicative, Monad,
              MonadReader (MonoEnv l m),
              MonadState (MonoState l),
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace,
              MonadTc)

deriving instance MonadRef IORef m => MonadRef IORef (MonoM l m)

instance MonadTrans (MonoM l) where
    lift  = MonoM . lift . lift

-- | Evaluate a 'Mono' action and return a list of 'C.Definition's.
runMono :: MonadTcRef m => MonoM l m a -> m a
runMono m = evalStateT (runReaderT (unMonoM m) defaultMonoEnv) defaultMonoState

extendFun :: MonadTcRef m => Var -> FunGen l m -> MonoM l m a -> MonoM l m a
extendFun f fgen k = do
  cacheRef <- newRef mempty
  local (\env -> env { funGens   = Map.insert f fgen (funGens env)
                     , funCaches = Map.insert f cacheRef (funCaches env)
                     })
        k

lookupFunGen :: MonadTcRef m => Var -> MonoM l m (FunGen l m)
lookupFunGen f = do
    maybe_fgen <- asks (Map.lookup f . funGens)
    case maybe_fgen of
      Nothing   -> faildoc $ text "Unknown function" <+> enquote (ppr f)
      Just fgen -> return fgen

lookupFunCache :: MonadTcRef m => Var -> MonoM l m Cache
lookupFunCache f = do
    maybe_cache <- asks (Map.lookup f . funCaches)
    case maybe_cache of
      Nothing    -> faildoc $ text "Unknown function" <+> enquote (ppr f)
      Just cache -> return cache

lookupFun :: MonadTcRef m => Var -> [Type] -> MonoM l m Var
lookupFun f taus = do
    cacheRef <- lookupFunCache f
    cache    <- readRef cacheRef
    case Map.lookup taus cache of
      Just f' -> return f'
      Nothing -> do fgen <- lookupFunGen f
                    f'   <- fgen taus
                    writeRef cacheRef (Map.insert taus f' cache)
                    return f'

appendTopDecl :: MonadTcRef m => Decl l -> MonoM l m ()
appendTopDecl decl =
    modify $ \s -> s { topdecls = topdecls s |> decl }

getTopDecls :: MonadTcRef m => MonoM l m [Decl l]
getTopDecls = gets (toList . topdecls)

monomorphizeProgram :: forall l m . (IsLabel l, MonadTcRef m)
                    => Program l
                    -> m (Program l)
monomorphizeProgram = runMono . monomorphize
  where
    monomorphize :: Program l -> MonoM l m (Program l)
    monomorphize = programT

{- Note [Monomorphization]

We statically monomorphize code by specializing all functions for each type at
which they are applied. We only consider the types that are /not/ or kind Nat
during type application, because type variables of kind Nat have runtime
significance, e.g., in the C back-end, they are passed a function parameters.

When compiling computation functions, we also have to handle type application of
the return ST type. The function @instSTTypes@ handles this for us. When looking
up a computation function's monomorphized version, we use these types as well as
the types from the explicit type application.
-}

instance MonadTcRef m => TransformExp (MonoM l m) where
    expT (CallE f taus args s) = do
        (tvks, _, _tau_ret) <- lookupVar f >>= unFunT
        splitNatArgs tvks taus $ \nonNatTaus natTaus -> do
          taus' <- mapM typeT nonNatTaus
          f'    <- lookupFun f taus'
          CallE f' natTaus <$> mapM expT args <*> pure s

    expT e = transExp e

instance MonadTcRef m => TransformComp l (MonoM l m) where
    programT prog = do
        Program imports decls main <- transProgram prog
        decls' <- getTopDecls
        return $ Program imports (decls <> decls') main

    declsT (LetFunD f tvks vbs tau_ret e l : decls) k =
        extendVars [(bVar f, tau)] $
        extendFun (bVar f) fgen $
        declsT decls k
      where
        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

        fgen :: FunGen l m
        fgen taus =
            splitNatParams tvks taus $ \tvks' ->
            withInstantiatedTyVars tau_ret $ do
            vbs'     <- mapM transField vbs
            tau_ret' <- typeT tau_ret
            e'       <- extendVars vbs' $
                        expT e
            f'       <- monoFunName (bVar f) taus
            appendTopDecl $ LetFunD (f { bVar = f' }) tvks' vbs' tau_ret' e' l
            return f'

    declsT decls@(LetExtFunD f _tvks _vbs _tau_ret _l : _) k =
        extendFun (bVar f) fgen $
        transDecls decls k
      where
        fgen :: FunGen l m
        fgen _taus = return (bVar f)

    declsT (LetFunCompD f tvks vbs tau_ret c l : decls) k =
        extendVars [(bVar f, tau)] $
        extendFun (bVar f) fgen $
        declsT decls k
      where
        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

        fgen :: FunGen l m
        fgen taus =
            splitNatParams tvks taus $ \tvks' ->
            withInstantiatedTyVars tau_ret $ do
            vbs'     <- mapM transField vbs
            tau_ret' <- typeT tau_ret >>= instST
            c'       <- extendVars vbs' $
                        compT c
            f'       <- monoFunName (bVar f) taus
            appendTopDecl $ LetFunCompD (f { bVar = f' }) tvks' vbs' tau_ret' c' l
            return f'

    declsT decls k = transDecls decls k

    stepT (CallC l f taus args s) = do
        (tvks, _, tau_ret) <- lookupVar f >>= unFunT
        splitNatArgs tvks taus $ \nonNatTaus natTaus -> do
          taus'    <- mapM typeT nonNatTaus
          taus2    <- typeT tau_ret >>= instSTTypes
          f'       <- lookupFun f (taus' ++ taus2)
          CallC l f' natTaus <$> mapM argT args <*> pure s

    stepT s = transStep s

-- | Generate a name for the monomorphized version of a function.
monoFunName :: MonadTc m => Var -> [Type] -> m Var
monoFunName f taus = do
    theta     <- askTyVarTypeSubst
    let taus' = subst theta mempty taus
    return $ mkVar . flip displayS "" . renderCompact $ fname taus'
  where
    fname :: [Type] -> Doc
    fname taus = cat $ punctuate (char '_') $ ppr f : map (pprPrec appPrec1) taus

-- | Return the types at which an ST type in the current ST context is
-- instantiated.
instSTTypes :: MonadTc m => Type -> MonoM l m [Type]
instSTTypes tau_ret =
    withInstantiatedTyVars tau_ret $
    case tau_ret of
      ForallT tvks ST{} _ -> mapM (lookupTyVarType . fst) tvks
      _                   -> return []

-- | Split function type arguments into those of kind Nat and those not of kind
-- Nat.
splitNatArgs :: MonadTc m
             => [Tvk]
             -> [Type]
             -> ([Type] -> [Type] -> m a)
             -> m a
splitNatArgs tvks taus k =
    k nonNatTaus natTaus
  where
    nonNatTaus :: [Type]
    nonNatTaus = [tau | ((_alpha, kappa), tau) <- tvks `zip` taus,
                        not (isNatK kappa)]

    natTaus :: [Type]
    natTaus = [tau | ((_alpha, kappa), tau) <- tvks `zip` taus,
                     isNatK kappa]

-- | Apply type parameters /not/ of kind Nat, and call the continuation with all
-- type variables of kind Nat.
splitNatParams :: MonadTc m
               => [Tvk]
               -> [Type]
               -> ([Tvk] -> m a)
               -> m a
splitNatParams tvks taus k =
    extendTyVarTypes (map fst nonNatTvks `zip` taus) $
    k natTvks
  where
    natTvks, nonNatTvks :: [Tvk]
    (natTvks, nonNatTvks) = partition (\(_, kappa) -> isNatK kappa) tvks
