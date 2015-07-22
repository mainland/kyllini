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

    shift,
    reset,

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

newtype Tc b a = Tc { unTc :: TcEnv -> TcState -> (a -> TcEnv -> TcState -> KZC (b, TcState)) -> KZC (b, TcState) }

runTc :: Tc a a -> TcEnv -> TcState -> KZC (a, TcState)
runTc m r s = unTc m r s $ \x _ s' -> return (x, s')

-- | Run a @Tc@ computation in the @KZC@ monad and update the @Tc@ environment.
liftTc :: Tc a a -> KZC a
liftTc m = do
    eref  <- asks tcenvref
    sref  <- asks tcstateref
    env   <- readRef eref
    state <- readRef sref
    (a, _) <- unTc m env state $ \a env' state' -> do
              writeRef eref env'
              writeRef sref state'
              return (a, state')
    return a

-- | Run a @Tc@ computation in the @KZC@ monad without updating the
-- @Tc@ environment.
withTc :: Tc a a -> KZC a
withTc m = do
    eref  <- asks tcenvref
    sref  <- asks tcstateref
    env   <- readRef eref
    state <- readRef sref
    (a, _) <- unTc m env state $ \a _ state' -> do
              writeRef sref state'
              return (a, state')
    return a

instance Functor (Tc b) where
    fmap f x = x >>= return . f

instance Applicative (Tc b) where
    pure  = return
    (<*>) = ap

instance Monad (Tc b) where
    {-# INLINE return #-}
    return a = Tc $ \r s k -> k a r s

    {-# INLINE (>>=) #-}
    m >>= f  = Tc $ \r s k -> unTc m  r s $ \x r' s' -> unTc (f x) r' s' $ \y r'' s'' ->
               k y r'' s''

    {-# INLINE (>>) #-}
    m1 >> m2 = Tc $ \r s k -> unTc m1 r s $ \_ r' s' -> unTc m2    r' s' $ \y r'' s'' ->
               k y r'' s''

    fail err = Tc $ \_ _ -> fail err


instance MonadReader TcEnv (Tc b) where
    ask = Tc $ \r s k -> k r r s

    local f m =Tc $ \r s k -> unTc m (f r) s $ \x _ s' -> k x r s'

instance MonadRef IORef (Tc b) where
    newRef x     = liftIO $ newRef x
    readRef r    = liftIO $ readRef r
    writeRef r x = liftIO $ writeRef r x

instance MonadIO (Tc b) where
    liftIO = liftKZC . liftIO

instance MonadUnique (Tc b) where
    newUnique = liftKZC newUnique

instance MonadKZC (Tc b) where
    liftKZC m = Tc $ \r s k -> do
                a <- m
                k a r s

instance MonadException (Tc b) where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Tc $ \r s k ->
      unTc m r s k `catchContextException` \e -> unTc (h e) r s k

instance MonadErr (Tc b) where
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
           else do  ctx <- take <$> getMaxContext <*> askErrCtx
                    liftIO $ hPutStrLn stderr $ pretty 80 (ppr (toContextException ctx e))

reset :: Tc a a -> Tc b a
reset m = Tc $ \r s k -> do (x, s') <- runTc m r s
                            k x r s'

shift :: ((a -> Tc b b) -> Tc b b) -> Tc b a
shift f = Tc $ \r s k ->
    let c = \x -> Tc $ \r' s k' -> do (y, s') <- k x r' s
                                      k' y r' s'
    in
      runTc (f c) r s

extend :: forall k v a b . Ord k
       => (TcEnv -> Map k v)
       -> (TcEnv -> Map k v -> TcEnv)
       -> [(k, v)]
       -> Tc b a
       -> Tc b a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (TcEnv -> Map k v)
         -> Tc b v
         -> k
         -> Tc b v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

localExp :: Z.Exp -> Tc b a -> Tc b a
localExp e = local (\env -> env { curexp = Just e })

askCurrentExp :: Tc b (Maybe Z.Exp)
askCurrentExp = asks curexp

extendVars :: [(Z.Var, Type)] -> Tc b a -> Tc b a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $ do
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Tc b Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

askEnvMtvs :: Tc b [MetaTv]
askEnvMtvs =
    asks (Set.toList . envMtvs) >>= mapM simplify >>= return . concat
  where
    simplify :: MetaTv -> Tc b [MetaTv]
    simplify mtv = do
        maybe_tau <- readTv mtv
        case maybe_tau of
          Just tau  -> (Set.toList . fvs) <$> compress tau
          Nothing   -> return [mtv]

extendTyVars :: [(TyVar, Kind)] -> Tc b a -> Tc b a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Tc b Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendTyVarInsts :: [(TyVar, Type)] -> Tc b a -> Tc b a
extendTyVarInsts tvks m =
    local (\env -> env { tyVarInsts = foldl' insert (tyVarInsts env) tvks }) m
  where
    insert mp (k, v) = Map.insert k v mp

lookupTyVarInsts :: Tc b (Map TyVar Type)
lookupTyVarInsts =
    asks tyVarInsts

lookupTyVarInst :: TyVar -> Tc b Type
lookupTyVarInst tv =
    lookupBy tyVarInsts onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

traceNest :: Int -> Tc b a -> Tc b a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceTc :: Doc -> Tc b ()
traceTc doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceTc)
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDoc stderr $ indent d $ doc <> line

withExpContext :: Z.Exp -> Tc b a -> Tc b a
withExpContext e m =
    localExp e $
    withSummaryContext e m

readTv :: MonadRef IORef m => MetaTv -> m (Maybe Type)
readTv (MetaTv _ ref) = readRef ref

writeTv :: MonadRef IORef m => MetaTv -> Type -> m ()
writeTv (MetaTv _ ref) tau = writeRef ref (Just tau)

newMetaTv :: Tc b MetaTv
newMetaTv = do
    u     <- newUnique
    tref  <- newRef Nothing
    return $ MetaTv u tref

newMetaTvT :: Located a => a -> Tc b Type
newMetaTvT x = MetaT <$> newMetaTv <*> pure (srclocOf x)

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: Tc b Doc
relevantBindings = do
    maybe_e <- askCurrentExp
    go maybe_e
  where
    go :: Maybe Z.Exp -> Tc b Doc
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
              ->  Tc b a
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

metaTvs :: (Compress a, HasVars a MetaTv) => a -> Tc b [MetaTv]
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

