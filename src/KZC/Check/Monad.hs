{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.Monad
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check.Monad (
    Ti(..),
    runTi,
    liftTi,

    localExp,
    askCurrentExp,

    localValCtxType,
    askValCtxType,
    withValCtx,
    tellValCtx,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,
    tyAppStruct,

    extendVars,
    lookupVar,

    askEnvMtvs,

    extendTyVars,
    lookupTyVar,

    typeSize,

    withExpContext,

    readTv,
    writeTv,
    newMetaTv,
    newMetaTvT,

    readKv,
    writeKv,
    newMetaKv,
    newMetaKvK,

    readRv,
    writeRv,
    newMetaRv,

    relevantBindings,
    sanitizeTypes,

    metaTvs,

    Compress(..)
  ) where

import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State
import Data.Foldable (toList)
import Data.IORef
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.State
import KZC.Check.Types
import KZC.Config
import qualified KZC.Expr.Syntax as E
import KZC.Monad
import KZC.Platform
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

newtype Ti a = Ti { unTi :: ReaderT TiEnv (StateT TiState KZC) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TiEnv,
              MonadState TiState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadPlatform,
              MonadTrace)

runTi :: Ti a -> TiEnv -> TiState -> KZC (a, TiState)
runTi m r = runStateT (runReaderT (unTi m) r)

-- | Run a @Ti@ computation in the @KZC@ monad and update the @Ti@ environment.
liftTi :: forall a . ((a -> Ti a) -> Ti a) -> KZC a
liftTi m = do
    eref   <- asks tienvref
    sref   <- asks tistateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTi (m' eref sref) env state
    return a
  where
    m' :: IORef TiEnv -> IORef TiState -> Ti a
    m' eref sref =
        m $ \x -> do
        ask >>= writeRef eref
        get >>= writeRef sref
        return x

-- | Specify the current expression we are working with.
localExp :: Z.Exp -> Ti a -> Ti a
localExp e = local (\env -> env { curexp = Just e })

-- | Ask the current expression we are working with. We use this to list
-- relevant bindings in error messages.
askCurrentExp :: Ti (Maybe Z.Exp)
askCurrentExp = asks curexp

-- | Specify the type of the computational context in which we need to produce a
-- value.
localValCtxType :: Type -> Ti a -> Ti a
localValCtxType tau = local $ \env -> env { valCtxType = tau }

-- | Ask the type of the computational context in which we need to produce a
-- value.
askValCtxType :: Ti Type
askValCtxType = asks valCtxType

-- | Given a computation that produces a 'E.Exp', return a new computation that
-- produces the same 'E.Exp' modified to incorporate the value context.
withValCtx :: Ti E.Exp -> Ti E.Exp
withValCtx mce = do
    old_valctx <- gets valctx
    modify $ \s -> s { valctx = id }
    ce <- mce
    f  <- gets valctx
    modify $ \s -> s { valctx = old_valctx }
    return $ f ce

-- | Specify a function for adding necessary value context to a 'E.Exp'
-- representing a computation.
tellValCtx :: (E.Exp -> E.Exp) -> Ti ()
tellValCtx f = modify $ \s -> s { valctx = valctx s . f }

extendStructs :: [StructDef] -> Ti a -> Ti a
extendStructs ss =
    extendEnv structs
        (\env x -> env { structs = x }) [(structName s, s) | s <- ss]

lookupStruct :: Z.Struct -> Ti StructDef
lookupStruct s =
    lookupEnv structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: Z.Struct -> Ti (Maybe StructDef)
maybeLookupStruct s =
    asks (Map.lookup s . structs)

-- | Perform type application of a struct to type arguments and return the
-- resulting type and its fields.
tyAppStruct :: StructDef -> [Type] -> Ti (Type, [(Z.Field, Type)])
tyAppStruct sdef taus = go sdef
  where
    theta :: Map TyVar Type
    theta = Map.fromList (map fst tvks `zip` taus)

    tvks :: [Tvk]
    tvks = case sdef of
             StructDef _ tvks _ _ -> tvks
             TypeDef _ tvks _ _   -> tvks

    go (StructDef s _ flds _) =
        return (structT s taus, map fst flds `zip` subst theta mempty (map snd flds))

    go (TypeDef s tvks (SynT _ tau' _) l) =
        go (TypeDef s tvks tau' l)

    go (TypeDef s _ (StructT s' taus' _) _) = do
        sdef'        <- lookupStruct s'
        (tau', flds) <- tyAppStruct sdef' taus'
        return (synT (structT s taus) tau', flds)

    go (TypeDef s _ tau' _) =
        return (synT (structT s taus) tau', [])

extendVars :: [(Z.Var, Type)] -> Ti a -> Ti a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $
      extendEnv varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Ti Type
lookupVar v =
    lookupEnv varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

askEnvMtvs :: Ti [MetaTv]
askEnvMtvs =
    concat <$> (asks (Set.toList . envMtvs) >>= mapM simplify)
  where
    simplify :: MetaTv -> Ti [MetaTv]
    simplify mtv = do
        maybe_tau <- readTv mtv
        case maybe_tau of
          Just tau  -> (Set.toList . fvs) <$> compress tau
          Nothing   -> return [mtv]

extendTyVars :: [Tvk] -> Ti a -> Ti a
extendTyVars = extendEnv tyVars (\env x -> env { tyVars = x })

lookupTyVar :: TyVar -> Ti Kind
lookupTyVar tv =
    lookupEnv tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

-- | Compute the size of a type in bits.
typeSize :: Type -> Ti Int
typeSize = go
  where
    go :: Type -> Ti Int
    go UnitT{}                 = pure 0
    go BoolT{}                 = pure 1
    go (IntT ip _)             = ipBitSize ip
    go (FloatT fp _)           = pure $ fpBitSize fp
    go (ArrT (NatT n _) tau _) = (*) <$> pure n <*> go tau
    go (ST (C tau _) _ _ _ _)  = go tau
    go (RefT tau _)            = go tau

    go (StructT s taus _) = do
        sdef      <- lookupStruct s
        (_, flds) <- tyAppStruct sdef taus
        sum <$> mapM (typeSize . snd) flds

    go (ForallT _ (ST (C tau _) _ _ _ _) _) =
        go tau

    go tau =
        faildoc $ text "Cannot calculate bit width of type" <+> ppr tau

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
    k'    <- case k of
               TauK (R ts) -> do mrv <- newMetaRv ts
                                 return $ TauK (MetaR mrv)
               _           -> return k
    return $ MetaTv u k' tref

newMetaTvT :: Located a => Kind -> a -> Ti Type
newMetaTvT k x = MetaT <$> newMetaTv k <*> pure (srclocOf x)

readKv :: MonadRef IORef m => MetaKv -> m (Maybe Kind)
readKv (MetaKv _ ref) = readRef ref

writeKv :: MonadRef IORef m => MetaKv -> Kind -> m ()
writeKv (MetaKv _ ref) kappa = writeRef ref (Just kappa)

newMetaKv :: Ti MetaKv
newMetaKv = do
    u     <- newUnique
    kref  <- newRef Nothing
    return $ MetaKv u kref

newMetaKvK :: Located a => a -> Ti Kind
newMetaKvK _x = MetaK <$> newMetaKv

readRv :: MonadRef IORef m => MetaRv -> m (Maybe R)
readRv (MetaRv _ _ ref) = readRef ref

writeRv :: MonadRef IORef m => MetaRv -> R -> m ()
writeRv (MetaRv _ _ ref) ts = writeRef ref (Just ts)

newMetaRv :: Traits -> Ti MetaRv
newMetaRv ts = do
    u     <- newUnique
    tref  <- newRef Nothing
    return $ MetaRv u ts tref

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
        return $ nest 2 $
          text "Relevant bindings:" </>
          stack (zipWith pprBinding vs taus)
    go _ =
        return Text.PrettyPrint.Mainland.empty

    pprBinding :: Z.Var -> Type -> Doc
    pprBinding v tau = nest 2 $ ppr v <+> text ":" <+> ppr tau

sanitizeTypes :: ( Compress a
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
    compress :: MonadRef IORef m => a -> m a

instance (Traversable f, Compress a) => Compress (f a) where
    compress = traverse compress

instance Compress a => Compress (L a) where
    compress (L loc a) =
        L loc <$> compress a

instance Compress Type where
    compress tau@UnitT{} =
        pure tau

    compress tau@BoolT{} =
        pure tau

    compress tau@IntT{} =
        pure tau

    compress tau@FixT{} =
        pure tau

    compress tau@FloatT{} =
        pure tau

    compress tau@StringT{} =
        pure tau

    compress (StructT s taus l) =
        StructT s <$> compress taus <*> pure l

    compress (SynT _tau1 tau2 _l) =
        compress tau2

    compress (ArrT tau1 tau2 l) =
        ArrT <$> compress tau1 <*> compress tau2 <*> pure l

    compress (C tau l) =
        C <$> compress tau <*> pure l

    compress tau@T{} =
        pure tau

    compress (ST omega tau1 tau2 tau3 l) =
        ST <$> compress omega <*> compress tau1 <*>
           compress tau2 <*> compress tau3 <*> pure l

    compress (RefT tau l) =
        RefT <$> compress tau <*> pure l

    compress (FunT taus tau l) =
        FunT <$> compress taus <*> compress tau <*> pure l

    compress tau@NatT{} =
        pure tau

    compress (ForallT tvks tau l) =
        ForallT <$> compress tvks <*> compress tau <*> pure l

    compress tau@TyVarT{} =
        pure tau

    compress tau@(MetaT mtv _) = do
        maybe_tau' <- readTv mtv
        case maybe_tau' of
          Nothing    ->  return tau
          Just tau'  ->  do  tau'' <- compress tau'
                             writeTv mtv tau''
                             return tau''

instance Compress Kind where
    compress (TauK r)     = TauK <$> compress r
    compress kappa@OmegaK = return kappa
    compress kappa@MuK    = return kappa
    compress kappa@RhoK   = return kappa
    compress kappa@PhiK   = return kappa
    compress kappa@NatK   = return kappa

    compress kappa@(MetaK mkv) = do
        maybe_kappa' <- readKv mkv
        case maybe_kappa' of
          Nothing     ->  return kappa
          Just kappa' ->  do  kappa'' <- compress kappa'
                              writeKv mkv kappa''
                              return kappa''

instance Compress (Type, Kind) where
    compress (alpha, kappa) = (,) <$> pure alpha <*> compress kappa

instance Compress R where
    compress traits@R{} = pure traits

    compress traits@(MetaR mrv) = do
        maybe_traits' <- readRv mrv
        case maybe_traits' of
          Nothing      -> return traits
          Just traits' -> do  traits'' <- compress traits'
                              writeRv mrv traits''
                              return traits''
