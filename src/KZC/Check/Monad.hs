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
    Ti(..),
    runTi,
    liftTi,
    withTi,

    localExp,
    askCurrentExp,

    askValCtxType,
    collectValCtx,
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
import Control.Monad.State
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

import qualified Language.Core.Syntax as C
import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.State
import KZC.Check.Types
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

newtype Ti a = Ti { unTi :: TiEnv -> TiState -> KZC (a, TiState) }

runTi :: Ti a -> TiEnv -> TiState -> KZC (a, TiState)
runTi m r s = unTi m r s

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

instance Functor Ti where
    fmap f x = x >>= return . f

instance Applicative Ti where
    pure  = return
    (<*>) = ap

instance Monad Ti where
    {-# INLINE return #-}
    return a = Ti $ \_ s -> return (a, s)

    {-# INLINE (>>=) #-}
    m >>= f  = Ti $ \r s -> do
               (x, s') <- runTi m r s
               runTi (f x) r s'

    {-# INLINE (>>) #-}
    m1 >> m2 = Ti $ \r s -> do
               (_, s') <- runTi m1 r s
               runTi m2 r s'

    fail msg = throw (FailException (string msg))

instance MonadReader TiEnv Ti where
    ask = Ti $ \r s -> return (r, s)

    local f m = Ti $ \r s -> runTi m (f r) s

instance MonadState TiState Ti where
    get   = Ti $ \_ s -> return (s, s)
    put s = Ti $ \_ _ -> return ((), s)

instance MonadRef IORef Ti where
    newRef x     = liftIO $ newRef x
    readRef r    = liftIO $ readRef r
    writeRef r x = liftIO $ writeRef r x

instance MonadIO Ti where
    liftIO = liftKZC . liftIO

instance MonadUnique Ti where
    newUnique = liftKZC newUnique

instance MonadKZC Ti where
    liftKZC m = Ti $ \_ s -> do
                a <- m
                return (a, s)

instance MonadException Ti where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Ti $ \r s ->
      unTi m r s `catchContextException` \e -> unTi (h e) r s

instance MonadErr Ti where
    {-# INLINE askErrCtx #-}
    askErrCtx = asks errctx

    {-# INLINE localErrCtx #-}
    localErrCtx ctx m =
        local (\env -> env { errctx = ctx : errctx env }) m

    {-# INLINE warnIsError #-}
    warnIsError = liftKZC $ asksFlags (testWarnFlag WarnError)

    warn e = do
        werror <- warnIsError
        if werror
           then err e
           else do ctx <- take <$> getMaxContext <*> askErrCtx
                   liftIO $ hPutStrLn stderr $
                     pretty 80 (text "Warning:" <+> ppr (toContextException ctx e))

extend :: forall k v a . Ord k
       => (TiEnv -> Map k v)
       -> (TiEnv -> Map k v -> TiEnv)
       -> [(k, v)]
       -> Ti a
       -> Ti a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (TiEnv -> Map k v)
         -> Ti v
         -> k
         -> Ti v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

localExp :: Z.Exp -> Ti a -> Ti a
localExp e = local (\env -> env { curexp = Just e })

askCurrentExp :: Ti (Maybe Z.Exp)
askCurrentExp = asks curexp

askValCtxType :: Ti Type
askValCtxType = asks valCtxType

collectValCtx :: Type -> Ti (Ti C.Exp) -> Ti (Ti C.Exp)
collectValCtx tau k = do
    mce <- local (\env -> env { valCtxType = tau }) k
    return $ do old_valctx <- gets valctx
                modify $ \s -> s { valctx = id }
                ce <- mce
                f  <- gets valctx
                modify $ \s -> s { valctx = old_valctx }
                return $ f ce

tellValCtx :: (C.Exp -> C.Exp) -> Ti ()
tellValCtx f = modify $ \s -> s { valctx = valctx s . f }

extendStructs :: [StructDef] -> Ti a -> Ti a
extendStructs ss m =
    extend structs (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: Z.Struct -> Ti StructDef
lookupStruct s =
    lookupBy structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: Z.Struct -> Ti (Maybe StructDef)
maybeLookupStruct s =
    asks (Map.lookup s . structs)

extendVars :: [(Z.Var, Type)] -> Ti a -> Ti a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $ do
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Ti Type
lookupVar v =
    lookupBy varTypes onerr v
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
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Ti Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: [(IVar, Kind)] -> Ti a -> Ti a
extendIVars ivks m =
    extend iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: IVar -> Ti Kind
lookupIVar iv =
    lookupBy iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

traceNest :: Int -> Ti a -> Ti a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceTc :: Doc -> Ti ()
traceTc doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceTc)
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDocLn stderr $ text "traceTc:" <+> indent d (align doc)

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
relevantBindings = do
    maybe_e <- askCurrentExp
    go maybe_e
  where
    go :: Maybe Z.Exp -> Ti Doc
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

    compress tau@(IntT {}) =
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

