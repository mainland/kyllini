{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.Monad (
    Ti(..),
    runTi,
    liftTi,
    withTi,

    localExp,
    askCurrentExp,

    localValCtxType,
    askValCtxType,
    withValCtx,
    tellValCtx,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,

    extendVars,
    lookupVar,

    askEnvMtvs,

    extendTyVars,
    lookupTyVar,

    extendIVars,
    lookupIVar,

    withExpContext,

    readTv,
    writeTv,
    newMetaTv,
    newMetaTvT,

    relevantBindings,
    sanitizeTypes,

    metaTvs,

    Compress(..)
  ) where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State
import Data.Foldable (toList)
import Data.IORef
import Data.Loc
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)
import Text.PrettyPrint.Mainland

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.State
import KZC.Check.Types
import qualified KZC.Core.Syntax as C
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env
import KZC.Util.SetLike
import KZC.Vars

newtype Ti a = Ti { unTi :: ReaderT TiEnv (StateT TiState KZC) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TiEnv,
              MonadState TiState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runTi :: Ti a -> TiEnv -> TiState -> KZC (a, TiState)
runTi m r s = runStateT (runReaderT (unTi m) r) s

-- | Run a @Ti@ computation in the @KZC@ monad and update the @Ti@ environment.
liftTi :: forall a . Ti a -> KZC a
liftTi m = do
    eref   <- asks tienvref
    sref   <- asks tistateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTi (m' eref sref) env state
    return a
  where
    m' :: IORef TiEnv -> IORef TiState -> Ti a
    m' eref sref = do
        x <- m
        ask >>= writeRef eref
        get >>= writeRef sref
        return x

-- | Run a @Ti@ computation in the @KZC@ monad without updating the
-- @Ti@ environment.
withTi :: forall a . Ti a -> KZC a
withTi m = do
    eref   <- asks tienvref
    sref   <- asks tistateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTi (m' sref) env state
    return a
  where
    m' :: IORef TiState -> Ti a
    m' sref = do
        x <- m
        get >>= writeRef sref
        return x

-- | Specify the current expression we are working with.
localExp :: Z.Exp -> Ti a -> Ti a
localExp e = local (\env -> env { curexp = Just e })

-- | ASk the current expression we are working with. We use this to list
-- relevant bindings in error messages.
askCurrentExp :: Ti (Maybe Z.Exp)
askCurrentExp = asks curexp

-- | Specify the type of the computational context in which we need to produce a
-- value.
localValCtxType :: Type -> Ti a -> Ti a
localValCtxType tau m = local (\env -> env { valCtxType = tau }) m

-- | Ask the type of the computational context in which we need to produce a
-- value.
askValCtxType :: Ti Type
askValCtxType = asks valCtxType

-- | Given a computation that produces a 'C.Exp', return a new computation that
-- produces the same 'C.Exp' modified to incorporate the value context.
withValCtx :: Ti C.Exp -> Ti C.Exp
withValCtx mce = do
    old_valctx <- gets valctx
    modify $ \s -> s { valctx = id }
    ce <- mce
    f  <- gets valctx
    modify $ \s -> s { valctx = old_valctx }
    return $ f ce

-- | Specify a function for adding necessary value context to a 'C.Exp'
-- representing a computation.
tellValCtx :: (C.Exp -> C.Exp) -> Ti ()
tellValCtx f = modify $ \s -> s { valctx = valctx s . f }

extendStructs :: [StructDef] -> Ti a -> Ti a
extendStructs ss m =
    extendEnv structs
        (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: Z.Struct -> Ti StructDef
lookupStruct s =
    lookupEnv structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: Z.Struct -> Ti (Maybe StructDef)
maybeLookupStruct s =
    asks (Map.lookup s . structs)

extendVars :: [(Z.Var, Type)] -> Ti a -> Ti a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $ do
    extendEnv varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Ti Type
lookupVar v =
    lookupEnv varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

askEnvMtvs :: Ti [MetaTv]
askEnvMtvs =
    asks (Set.toList . envMtvs) >>= mapM simplify >>= return . concat
  where
    simplify :: MetaTv -> Ti [MetaTv]
    simplify mtv = do
        maybe_tau <- readTv mtv
        case maybe_tau of
          Just tau  -> (Set.toList . fvs) <$> compress tau
          Nothing   -> return [mtv]

extendTyVars :: [(TyVar, Kind)] -> Ti a -> Ti a
extendTyVars tvks m =
    extendEnv tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Ti Kind
lookupTyVar tv =
    lookupEnv tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: [(IVar, Kind)] -> Ti a -> Ti a
extendIVars ivks m =
    extendEnv iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: IVar -> Ti Kind
lookupIVar iv =
    lookupEnv iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

withExpContext :: Z.Exp -> Ti a -> Ti a
withExpContext e m =
    localExp e $
    withSummaryContext e m

readTv :: MonadRef IORef m => MetaTv -> m (Maybe Type)
readTv (MetaTv _ _ ref) = readRef ref

writeTv :: MonadRef IORef m => MetaTv -> Type -> m ()
writeTv (MetaTv _ _ ref) tau = writeRef ref (Just tau)

newMetaTv :: Kind -> Ti MetaTv
newMetaTv k = do
    u     <- newUnique
    tref  <- newRef Nothing
    return $ MetaTv u k tref

newMetaTvT :: Located a => Kind -> a -> Ti Type
newMetaTvT k x = MetaT <$> newMetaTv k <*> pure (srclocOf x)

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: Ti Doc
relevantBindings =
    fmap (Set.toList . fvs) <$> askCurrentExp >>= go
  where
    go :: Maybe [Z.Var] -> Ti Doc
    go (Just vs@(_:_)) = do
        taus <- mapM lookupVar vs >>= sanitizeTypes
        return $ line <>
            nest 2 (text "Relevant bindings:" </>
                    stack (map pprBinding (vs `zip` taus)))
    go _ =
        return Text.PrettyPrint.Mainland.empty

    pprBinding :: (Z.Var, Type) -> Doc
    pprBinding (v, tau) = nest 2 $ ppr v <+> text ":" <+> ppr tau

sanitizeTypes :: ( Pretty a, Compress a
                 , Located a
                 , Fvs a TyVar
                 , HasVars a MetaTv
                 , Subst Type MetaTv a)
              =>  a
              ->  Ti a
sanitizeTypes x = do
    x'        <- compress x
    mtvs      <- metaTvs x'
    tvs       <- freshVars (length mtvs) ((Set.toList . fvs) x)
    let theta =  Map.fromList (mtvs `zip` map tyVarT tvs)
    return $ subst theta Set.empty x'

{------------------------------------------------------------------------------
 -
 - Meta-variables
 -
 ------------------------------------------------------------------------------}

-- The @metasM@ and @metas@ functions returns a list of all meta variables in
-- /order of occurrence/.

metaTvs :: (Compress a, HasVars a MetaTv) => a -> Ti [MetaTv]
metaTvs x = do
  x' <- compress x
  let mtvs :: OrderedSet MetaTv = allVars x'
  return $ toList mtvs

{------------------------------------------------------------------------------
 -
 - Path compression
 -
 ------------------------------------------------------------------------------}

class Compress a where
    compress :: (Functor m, Applicative m, MonadRef IORef m) => a -> m a

instance (Traversable f, Compress a) => Compress (f a) where
    compress = traverse compress

instance Compress a => Compress (L a) where
    compress (L loc a) =
        L loc <$> compress a

instance Compress Type where
    compress tau@(UnitT {}) =
        pure tau

    compress tau@(BoolT {}) =
        pure tau

    compress tau@(BitT {}) =
        pure tau

    compress tau@(FixT {}) =
        pure tau

    compress tau@(FloatT {}) =
        pure tau

    compress tau@(StringT {}) =
        pure tau

    compress tau@(StructT {}) =
        pure tau

    compress (ArrT tau1 tau2 l) =
        ArrT <$> compress tau1 <*> compress tau2 <*> pure l

    compress (C tau l) =
        C <$> compress tau <*> pure l

    compress tau@(T {}) =
        pure tau

    compress (ST alphas omega tau1 tau2 tau3 l) =
        ST <$> pure alphas <*> compress omega <*> compress tau1 <*>
           compress tau2 <*> compress tau3 <*> pure l

    compress (RefT tau l) =
        RefT <$> compress tau <*> pure l

    compress (FunT iotas taus tau l) =
        FunT <$> pure iotas <*> compress taus <*> compress tau <*> pure l

    compress tau@(ConstI {}) =
        pure tau

    compress tau@(VarI {}) =
        pure tau

    compress tau@(TyVarT {}) =
        pure tau

    compress tau@(MetaT mtv _) = do
        maybe_tau' <- readTv mtv
        case maybe_tau' of
          Nothing    ->  return tau
          Just tau'  ->  do  tau'' <- compress tau'
                             writeTv mtv tau''
                             return tau''
