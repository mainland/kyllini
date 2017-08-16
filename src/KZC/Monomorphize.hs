{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Text.PrettyPrint.Mainland.Class

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Pretty
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

-- | Generate a monomorphized version of a thing.
type MonoGen l m a = [Type] -> MonoM l m a

type FunGen l m = MonoGen l m Var

type StructGen l m = MonoGen l m Struct

-- | Cache of monomorphized things.
type Cache a = IORef (Map [Type] a)

data MonoEnv l m = MonoEnv
    { structGens :: Map Struct (MonoGen l m Struct, Cache Struct)
    , funGens    :: Map Var (MonoGen l m Var, Cache Var)
    }

defaultMonoEnv :: MonoEnv l m
defaultMonoEnv = MonoEnv
    { structGens = mempty
    , funGens    = mempty
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
              MonadPlatform,
              MonadTrace,
              MonadTc)

deriving instance MonadRef IORef m => MonadRef IORef (MonoM l m)

instance MonadTrans (MonoM l) where
    lift  = MonoM . lift . lift

-- | Evaluate a 'Mono' action and return a list of 'C.Definition's.
runMono :: MonadTcRef m => MonoM l m a -> m a
runMono m = evalStateT (runReaderT (unMonoM m) defaultMonoEnv) defaultMonoState

extendStruct :: MonadTcRef m
             => Struct
             -> StructGen l m
             -> MonoM l m a
             -> MonoM l m a
extendStruct struct sgen k = do
  cacheRef <- newRef mempty
  local (\env -> env { structGens = Map.insert struct (sgen, cacheRef) (structGens env) }) k

extendFun :: MonadTcRef m
          => Var
          -> FunGen l m
          -> MonoM l m a
          -> MonoM l m a
extendFun f fgen k = do
  cacheRef <- newRef mempty
  local (\env -> env { funGens = Map.insert f (fgen, cacheRef) (funGens env) }) k

lookupMono :: (Ord a, Pretty a, MonadTcRef m)
           => Doc
           -> (MonoEnv l m -> Map a (MonoGen l m a, Cache a))
           -> a
           -> [Type]
           -> MonoM l m a
lookupMono desc proj x taus = do
    maybe_gen       <- asks (Map.lookup x . proj)
    (gen, cacheRef) <- case maybe_gen of
                         Nothing  -> faildoc $ text "Unknown" <+> desc <+> enquote (ppr x)
                         Just gen -> return gen
    cache           <- readRef cacheRef
    case Map.lookup taus cache of
      Just x' -> return x'
      Nothing -> do x'   <- gen taus
                    writeRef cacheRef (Map.insert taus x' cache)
                    return x'

lookupMonoFun :: MonadTcRef m => Var -> [Type] -> MonoM l m Var
lookupMonoFun = lookupMono (text "function") funGens

lookupMonoStruct :: MonadTcRef m => Struct -> [Type] -> MonoM l m Struct
lookupMonoStruct = lookupMono (text "struct") structGens

appendTopDecl :: MonadTcRef m => Decl l -> MonoM l m ()
appendTopDecl decl =
    modify $ \s -> s { topdecls = topdecls s |> decl }

getTopDecls :: MonadTcRef m => MonoM l m [Decl l]
getTopDecls = do
    decls <- gets (toList . topdecls)
    modify $ \s -> s { topdecls = mempty }
    return decls

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
    typeT (StructT struct taus@(_:_) s) = do
        taus'   <- mapM typeT taus
        struct' <- lookupMonoStruct struct taus'
        return $ StructT struct' [] s

    typeT tau = transType tau

    constT (StructC struct taus@(_:_) flds) = do
        taus'   <- mapM typeT taus
        struct' <- lookupMonoStruct struct taus'
        return $ StructC struct' [] flds

    constT c = transConst c

    expT (CallE f taus@(_:_) args s) = do
        (tvks, _, _tau_ret) <- lookupVar f >>= unFunT
        taus' <- mapM typeT taus
        splitNatArgs tvks taus' $ \nonNatTaus natTaus -> do
          f' <- lookupMonoFun f nonNatTaus
          CallE f' natTaus <$> mapM expT args <*> pure s

    expT (StructE struct taus@(_:_) flds s) = do
        taus'   <- mapM typeT taus
        struct' <- lookupMonoStruct struct taus'
        return $ StructE struct' [] flds s

    expT e = transExp e

mkStructGen :: MonadTcRef m => StructDef -> StructGen l m
mkStructGen (StructDef struct tvks flds l) taus = do
    taus' <- mapM typeT taus
    extendTyVarTypes (map fst tvks `zip` taus') $ do
      struct' <- monoStructName struct taus
      flds'   <- mapM transField flds
      appendTopDecl $ StructD struct' [] flds' l
      return struct'

instance (IsLabel l, MonadTcRef m) => TransformComp l (MonoM l m) where
    programT prog =
        extendStruct "Complex" (mkStructGen (complexStructDef)) $  do
        Program imports decls main <- transProgram prog
        decls' <- getTopDecls
        return $ Program imports (decls <> decls') main

    declsT [] m = do
        x     <- m
        decls <- getTopDecls
        return (decls, x)

    declsT (StructD struct tvks@(_:_) flds l : decls) k =
        extendStructs [StructDef struct tvks flds l] $
        extendStruct struct (mkStructGen (StructDef struct tvks flds l)) $
        declsT decls k

    declsT (LetFunD f tvks@(_:_) vbs tau_ret e l : decls) k =
        extendVars [(bVar f, tau)] $
        extendFun (bVar f) fgen $
        declsT decls k
      where
        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

        fgen :: FunGen l m
        fgen taus =
            splitNatParams tvks taus $ \tvks' ->
            withMonoInstantiatedTyVars tau_ret $ do
            vbs'     <- mapM transField vbs
            tau_ret' <- typeT tau_ret
            e'       <- extendVars vbs $
                        expT e
            f'       <- monoFunName f taus
            appendTopDecl $ LetFunD f' tvks' vbs' tau_ret' e' l
            return (bVar f')

    declsT (LetExtFunD f tvks@(_:_) vbs tau_ret l : decls) k =
        extendVars [(bVar f, tau)] $
        extendFun (bVar f) fgen $ do
        vbs'     <- mapM transField vbs
        tau_ret' <- typeT tau_ret
        appendTopDecl $ LetExtFunD f tvks vbs' tau_ret' l
        declsT decls k
      where
        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

        fgen :: FunGen l m
        fgen _taus = return (bVar f)

    -- We must transform /all/ computation functions because we need to
    -- eliminate polymorphism in the return type, which may exist even if the
    -- function doesn't take any type arguments.
    declsT (decl@(LetFunCompD f tvks vbs tau_ret c l) : decls) k =
        extendVars [(bVar f, tau)] $
        extendFun (bVar f) fgen $
        declsT decls k
      where
        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

        fgen :: FunGen l m
        fgen taus = withSummaryContext decl $
            splitNatParams tvks taus $ \tvks' ->
            withMonoInstantiatedTyVars tau_ret $ do
            vbs'     <- mapM transField vbs
            tau_ret' <- instST tau_ret >>= typeT
            c'       <- extendVars vbs $
                        compT c
            f'       <- monoFunName f taus
            appendTopDecl $ LetFunCompD f' tvks' vbs' tau_ret' c' l
            return (bVar f')

    declsT (d:ds) m = do
        (d', (ds1, ds2, x)) <-
            declT d $ do
            ds1      <- getTopDecls
            (ds2, x) <- declsT ds m
            return (ds1, ds2, x)
        return (ds1 ++ d':ds2, x)

    -- We must transform all calls to computation functions for the reason noted
    -- just above.
    stepT (CallC l f taus args s) = do
        (tvks, _, tau_ret) <- lookupVar f >>= unFunT
        taus' <- mapM typeT taus
        splitNatArgs tvks taus' $ \nonNatTaus natTaus -> do
          stTaus <- extendTyVarTypes (map fst tvks `zip` taus') $
                    typeT tau_ret >>= instSTTypes
          f'     <- lookupMonoFun f (nonNatTaus ++ stTaus)
          CallC l f' natTaus <$> mapM argT args <*> pure s

    stepT s = transStep s

-- | Generate a name for the monomorphized version of a function.
monoStructName :: MonadTc m => Struct -> [Type] -> m Struct
monoStructName struct [] =
    return struct

monoStructName struct taus = do
    struct' <- monoName struct taus
    return $ mkStruct struct'

-- | Generate a name for the monomorphized version of a function.
monoFunName :: MonadTc m => BoundVar -> [Type] -> m BoundVar
monoFunName f [] =
    return f

monoFunName f taus = do
    f' <- monoName (bVar f) taus
    return f { bVar = mkVar f' }

-- | Generate a name for the monomorphized version of a thing.
monoName :: (Pretty a, MonadTc m) => a -> [Type] -> m String
monoName x taus = do
    theta     <- askTyVarTypeSubst
    let taus' =  subst theta mempty taus
    return $ flip displayS "" . renderCompact $ fname taus'
  where
    fname :: [Type] -> Doc
    fname taus = ppr x <> char '_' <> monoTypes taus

    monoType :: Type -> Doc
    monoType (StructT struct taus _) =
        ppr struct <> char '_' <> monoTypes taus

    monoType tau =
        pprPrec appPrec1 tau

    monoTypes :: [Type] -> Doc
    monoTypes = cat . punctuate (char '_') . map monoType

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context. We can't use
-- @withInstantiatedTyVars@ because it doesn't translate types after
-- instantiation.
withMonoInstantiatedTyVars :: TransformExp m => Type -> m a -> m a
withMonoInstantiatedTyVars tau@(ForallT tvks (ST _ s a b _) _) k = do
    ST _ s' a' b' _ <- instST tau >>= typeT
    extendTyVarTypes [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b'], alpha `elem` alphas] k
  where
    alphas :: [TyVar]
    alphas = map fst tvks

withMonoInstantiatedTyVars _tau k =
    k

-- | Return the types at which an ST type in the current ST context is
-- instantiated.
instSTTypes :: (MonadTcRef m, TransformExp (MonoM l m))
            => Type
            -> MonoM l m [Type]
instSTTypes tau_ret =
    withMonoInstantiatedTyVars tau_ret $
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
