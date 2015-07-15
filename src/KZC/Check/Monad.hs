{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check.Monad (
    Tc(..),
    runTc,
    liftTc,
    withTc,

    localExp,
    askCurrentExp,

    extendVars,
    lookupVar,

    askEnvMtvs,

    extendTyVars,
    lookupTyVar,
    extendTyVarInsts,
    lookupTyVarInst,
    lookupTyVarInsts,

    traceNest,
    traceTc,

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
import Data.IORef
import Data.List (foldl')
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)
import System.IO (hPutStrLn, stderr)
import Text.PrettyPrint.Mainland

import qualified Language.Ziria.Syntax as Z

import KZC.Check.State
import KZC.Check.Types
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

newtype Tc a = Tc { unTc :: ReaderT TcEnv KZC a }
    deriving (Functor, Applicative, MonadIO, MonadReader TcEnv,
              MonadAsyncException,
              MonadRef IORef, MonadAtomicRef IORef)

runTc :: Tc a -> TcEnv -> KZC a
runTc = runReaderT . unTc

-- | Run a @Tc@ computation in the @KZC@ monad and update the @Tc@ environment.
liftTc :: ((a -> Tc (a, TcEnv)) -> Tc (a, TcEnv)) -> KZC a
liftTc m = do
    ref <- asks tcenvref
    env <- readRef ref
    (a, env') <- flip runTc env $ m $ \a -> do
                 env' <- ask
                 return (a, env')
    writeRef ref env'
    return a

-- | Run a @Tc@ computation in the @KZC@ monad without updating the
-- @Tc@ environment.
withTc :: Tc a -> KZC a
withTc m = do
    env <- asks tcenvref >>= readRef
    flip (runReaderT . unTc) env m

instance Monad Tc where
    {-# INLINE (>>=) #-}
    m >>= k = Tc $ ReaderT $ \env -> do
        a <- runTc m env
        runTc (k a) env

    {-# INLINE (>>) #-}
    m1 >> m2 = Tc $ ReaderT $ \env -> do
        _ <- runTc m1 env
        runTc m2 env

    {-# INLINE return #-}
    return a = Tc $ ReaderT $ \_ -> return a

    fail msg = do
        ctx <- take <$> getMaxContext <*> askErrCtx
        liftKZC $ throw (toException (toContextException ctx (FailException (string msg))))

instance MonadUnique Tc where
    newUnique = liftKZC newUnique

instance MonadKZC Tc where
    liftKZC m = Tc $ ReaderT $ \_ -> m

instance MonadException Tc where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Tc $ ReaderT $ \env ->
      runTc m env `catchContextException` \e -> runTc (h e) env

instance MonadErr Tc where
    {-# INLINE askErrCtx #-}
    askErrCtx = asks errctx

    {-# INLINE localErrCtx #-}
    localErrCtx ctx m =
        local (\env -> env { errctx = ctx : errctx env }) m

    {-# INLINE warnIsError #-}
    warnIsError = liftKZC $ asks $ warnErrorF . flags

    warn e = do
        werror <- warnIsError
        if werror
           then err e
           else do  ctx <- take <$> getMaxContext <*> askErrCtx
                    liftIO $ hPutStrLn stderr $ pretty 80 (ppr (toContextException ctx e))

extend :: forall k v a . Ord k
       => (TcEnv -> Map k v)
       -> (TcEnv -> Map k v -> TcEnv)
       -> [(k, v)]
       -> Tc a
       -> Tc a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (TcEnv -> Map k v)
         -> Tc v
         -> k
         -> Tc v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

localExp :: Z.Exp -> Tc a -> Tc a
localExp e = local (\env -> env { curexp = Just e })

askCurrentExp :: Tc (Maybe Z.Exp)
askCurrentExp = asks curexp

extendVars :: [(Z.Var, Type)] -> Tc a -> Tc a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $ do
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Tc Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

askEnvMtvs :: Tc [MetaTv]
askEnvMtvs =
    asks (Set.toList . envMtvs) >>= mapM simplify >>= return . concat
  where
    simplify :: MetaTv -> Tc [MetaTv]
    simplify mtv = do
        maybe_tau <- readTv mtv
        case maybe_tau of
          Just tau  -> (Set.toList . fvs) <$> compress tau
          Nothing   -> return [mtv]

extendTyVars :: [(TyVar, Kind)] -> Tc a -> Tc a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Tc Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendTyVarInsts :: [(TyVar, Type)] -> Tc a -> Tc a
extendTyVarInsts tvks m =
    local (\env -> env { tyVarInsts = foldl' insert (tyVarInsts env) tvks }) m
  where
    insert mp (k, v) = Map.insert k v mp

lookupTyVarInsts :: Tc (Map TyVar Type)
lookupTyVarInsts =
    asks tyVarInsts

lookupTyVarInst :: TyVar -> Tc Type
lookupTyVarInst tv =
    lookupBy tyVarInsts onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

traceNest :: Int -> Tc a -> Tc a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceTc :: Doc -> Tc ()
traceTc doc = do
    doTrace <- liftKZC $ asks $ traceTcF . flags
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDoc stderr $ indent d $ doc <> line

withExpContext :: Z.Exp -> Tc a -> Tc a
withExpContext e m =
    localExp e $
    withSummaryContext e m

readTv :: MonadRef IORef m => MetaTv -> m (Maybe Type)
readTv (MetaTv _ ref) = readRef ref

writeTv :: MonadRef IORef m => MetaTv -> Type -> m ()
writeTv (MetaTv _ ref) tau = writeRef ref (Just tau)

newMetaTv :: Tc MetaTv
newMetaTv = do
    u     <- newUnique
    tref  <- newRef Nothing
    return $ MetaTv u tref

newMetaTvT :: Located a => a -> Tc Type
newMetaTvT x = MetaT <$> newMetaTv <*> pure (srclocOf x)

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: Tc Doc
relevantBindings = do
    maybe_e <- askCurrentExp
    go maybe_e
  where
    go :: Maybe Z.Exp -> Tc Doc
    go Nothing =
        return Text.PrettyPrint.Mainland.empty

    go (Just e) = do
        let vs =  Set.toList $ fvs e
        taus   <- mapM lookupVar vs >>= sanitizeTypes
        return $ line <>
            nest 2 (text "Relevant bindings:" </>
                    stack (map pprBinding (vs `zip` taus)))

    pprBinding :: (Z.Var, Type) -> Doc
    pprBinding (v, tau) = nest 2 $ ppr v <+> text ":" <+> ppr tau

sanitizeTypes :: ( Pretty a, Compress a
                 , Located a
                 , Fvs a TyVar
                 , HasVars a MetaTv
                 , Subst Type MetaTv a)
              =>  a
              ->  Tc a
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

metaTvs :: (Compress a, HasVars a MetaTv) => a -> Tc [MetaTv]
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

    compress tau@(IntT {}) =
        pure tau

    compress tau@(FloatT {}) =
        pure tau

    compress tau@(ComplexT {}) =
        pure tau

    compress tau@(StringT {}) =
        pure tau

    compress (RefT tau l) =
        RefT <$> compress tau <*> pure l

    compress (ArrT tau1 tau2 l) =
        ArrT <$> compress tau1 <*> compress tau2 <*> pure l

    compress tau@(StructT {}) =
        pure tau

    compress (C tau l) =
        C <$> compress tau <*> pure l

    compress tau@(T {}) =
        pure tau

    compress (ST tau1 tau2 tau3 l) =
        ST <$> compress tau1 <*> compress tau2 <*> compress tau3 <*> pure l

    compress (FunT iotas taus tau l) =
        FunT <$> compress iotas <*> compress taus <*> compress tau <*> pure l

    compress tau@(NatI {}) =
        pure tau

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

