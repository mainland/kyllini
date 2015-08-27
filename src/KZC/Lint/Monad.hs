{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Lint.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Lint.Monad (
    Tc(..),
    runTc,
    liftTc,
    withTc,

    localExp,
    askCurrentExp,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,

    extendVars,
    extendBindVars,
    lookupVar,

    extendTyVars,
    lookupTyVar,

    extendIVars,
    lookupIVar,

    localSTIndTypes,
    askSTIndTypes,
    inSTScope,

    inScopeTyVars,

    traceNest,
    traceLint,

    withExpContext,

    relevantBindings
  ) where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State
import Data.IORef
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO (stderr)
import Text.PrettyPrint.Mainland

import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Lint.State
import KZC.Monad
import KZC.Summary
import KZC.Uniq
import KZC.Vars

newtype Tc r s a = Tc { unTc :: r -> s -> TcEnv -> KZC (a, s) }

runTc :: Tc r s a -> r -> s -> TcEnv -> KZC (a, s)
runTc m r s e = unTc m r s e

-- | Run a @Tc@ computation in the @KZC@ monad and update the @Tc@ environment.
liftTc :: forall r s a . r -> s -> Tc r s a -> KZC a
liftTc r s m = do
    eref   <- asks tcenvref
    env    <- readRef eref
    (a, _) <- runTc (m' eref) r s env
    return a
  where
    m' :: IORef TcEnv -> Tc r s a
    m' eref = do
        x <- m
        askTc >>= writeRef eref
        return x

-- | Run a @Tc@ computation in the @KZC@ monad without updating the
-- @Tc@ environment.
withTc :: forall r s a . r -> s -> Tc r s a -> KZC a
withTc r s m = do
    eref   <- asks tcenvref
    env    <- readRef eref
    (a, _) <- runTc m r s env
    return a

instance Functor (Tc r s) where
    fmap f x = x >>= return . f

instance Applicative (Tc r s) where
    pure  = return
    (<*>) = ap

instance Monad (Tc r s) where
    {-# INLINE return #-}
    return a = Tc $ \_ s _ -> return (a, s)

    {-# INLINE (>>=) #-}
    m >>= f  = Tc $ \r s e -> do
               (x, s') <- runTc m r s e
               runTc (f x) r s' e

    {-# INLINE (>>) #-}
    m1 >> m2 = Tc $ \r s e -> do
               (_, s') <- runTc m1 r s e
               runTc m2 r s' e

    fail msg = throw (FailException (string msg))

instance MonadReader r (Tc r s) where
    ask = Tc $ \r s _ -> return (r, s)

    local f m = Tc $ \r s e -> runTc m (f r) s e

instance MonadState s (Tc r s) where
    get   = Tc $ \_ s _ -> return (s, s)
    put s = Tc $ \_ _ _ -> return ((), s)

instance MonadRef IORef (Tc r s) where
    newRef x     = liftIO $ newRef x
    readRef r    = liftIO $ readRef r
    writeRef r x = liftIO $ writeRef r x

instance MonadIO (Tc r s) where
    liftIO = liftKZC . liftIO

instance MonadUnique (Tc r s) where
    newUnique = liftKZC newUnique

instance MonadKZC (Tc r s) where
    liftKZC m = Tc $ \_ s _ -> do
                a <- m
                return (a, s)

instance MonadException (Tc r s) where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Tc $ \r s env ->
      unTc m r s env `catchContextException` \e -> unTc (h e) r s env

instance MonadErr (Tc r s) where
    {-# INLINE askErrCtx #-}
    askErrCtx = asksTc errctx

    {-# INLINE localErrCtx #-}
    localErrCtx ctx m =
        localTc (\env -> env { errctx = ctx : errctx env }) m

    {-# INLINE warnIsError #-}
    warnIsError = liftKZC $ asksFlags (testWarnFlag WarnError)

askTc :: Tc r s TcEnv
askTc = Tc $ \_ s e -> return (e, s)

asksTc :: (TcEnv -> a) -> Tc r s a
asksTc f = Tc $ \_ s e -> return (f e, s)

localTc :: (TcEnv -> TcEnv) -> Tc r s a -> Tc r s a
localTc f m = Tc $ \r s e -> runTc m r s (f e)

extend :: forall k v r s a . Ord k
       => (TcEnv -> Map k v)
       -> (TcEnv -> Map k v -> TcEnv)
       -> [(k, v)]
       -> Tc r s a
       -> Tc r s a
extend _ _ [] m = m

extend proj upd kvs m = do
    localTc (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (TcEnv -> Map k v)
         -> Tc r s v
         -> k
         -> Tc r s v
lookupBy proj onerr k = do
    maybe_v <- asksTc (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

localExp :: Exp -> Tc r s a -> Tc r s a
localExp e = localTc (\env -> env { curexp = Just e })

askCurrentExp :: Tc r s (Maybe Exp)
askCurrentExp = asksTc curexp

extendStructs :: [StructDef] -> Tc r s a -> Tc r s a
extendStructs ss m =
    extend structs (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: Struct -> Tc r s StructDef
lookupStruct s =
    lookupBy structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: Struct -> Tc r s (Maybe StructDef)
maybeLookupStruct s =
    asksTc (Map.lookup s . structs)

extendVars :: [(Var, Type)] -> Tc r s a -> Tc r s a
extendVars vtaus m =
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

extendBindVars :: [BindVar] -> Tc r s a -> Tc r s a
extendBindVars bvs m =
    extendVars [(v, tau) | BindV v tau <- bvs] m

lookupVar :: Var -> Tc r s Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendTyVars :: [(TyVar, Kind)] -> Tc r s a -> Tc r s a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Tc r s Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: [(IVar, Kind)] -> Tc r s a -> Tc r s a
extendIVars ivks m =
    extend iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: IVar -> Tc r s Kind
lookupIVar iv =
    lookupBy iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

localSTIndTypes :: Maybe (Type, Type, Type) -> Tc r s a -> Tc r s a
localSTIndTypes taus m =
    extendTyVars (alphas `zip` repeat TauK) $
    localTc (\env -> env { stIndTys = taus }) m
  where
    alphas :: [TyVar]
    alphas = case taus of
               Nothing      -> []
               Just (s,a,b) -> [alpha | TyVarT alpha _ <- [s,a,b]]

inSTScope :: Type -> Tc r s a -> Tc r s a
inSTScope tau m =
    scopeOver tau m
  where
    scopeOver :: Type -> Tc r s a -> Tc r s a
    scopeOver (ST _ _ s a b _) m =
        localSTIndTypes (Just (s, a, b)) m

    scopeOver _ m =
        localSTIndTypes Nothing m

askSTIndTypes :: Tc r s (Type, Type, Type)
askSTIndTypes = do
    maybe_taus <- asksTc stIndTys
    case maybe_taus of
      Just taus -> return taus
      Nothing   -> faildoc $ text "Not in scope of an ST computation"

inScopeTyVars :: Tc r s (Set TyVar)
inScopeTyVars = do
    maybe_idxs <- asksTc stIndTys
    case maybe_idxs of
      Nothing         -> return mempty
      Just (s',a',b') -> return $ fvs [s',a',b']

traceNest :: Int -> Tc r s a -> Tc r s a
traceNest d = localTc (\env -> env { nestdepth = nestdepth env + d })

traceLint :: Doc -> Tc r s ()
traceLint doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceLint)
    when doTrace $ do
        d <- asksTc nestdepth
        liftIO $ hPutDocLn stderr $ text "traceLint:" <+> indent d (align doc)

withExpContext :: Exp -> Tc r s a -> Tc r s a
withExpContext e m =
    localExp e $
    withSummaryContext e m

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: Tc r s Doc
relevantBindings = do
    maybe_e <- askCurrentExp
    go maybe_e
  where
    go :: Maybe Exp -> Tc r s Doc
    go Nothing =
        return Text.PrettyPrint.Mainland.empty

    go (Just e) = do
        let vs =  Set.toList $ fvs e
        taus   <- mapM lookupVar vs
        return $ line <>
            nest 2 (text "Relevant bindings:" </>
                    stack (map pprBinding (vs `zip` taus)))

    pprBinding :: (Var, Type) -> Doc
    pprBinding (v, tau) = nest 2 $ ppr v <+> text ":" <+> ppr tau
