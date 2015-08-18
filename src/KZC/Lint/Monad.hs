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
    lookupVar,

    extendTyVars,
    lookupTyVar,

    extendIVars,
    lookupIVar,

    localSTIndTypes,
    askSTIndTypes,

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
import System.IO (hPutStrLn, stderr)
import Text.PrettyPrint.Mainland

import Language.Core.Smart
import Language.Core.Syntax

import KZC.Lint.State
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Uniq
import KZC.Vars

newtype Tc a = Tc { unTc :: TcEnv -> TcState -> KZC (a, TcState) }

runTc :: Tc a -> TcEnv -> TcState -> KZC (a, TcState)
runTc m r s = unTc m r s

-- | Run a @Tc@ computation in the @KZC@ monad and update the @Tc@ environment.
liftTc :: forall a . Tc a -> KZC a
liftTc m = do
    eref   <- asks tcenvref
    sref   <- asks tcstateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTc (m' eref sref) env state
    return a
  where
    m' :: IORef TcEnv -> IORef TcState -> Tc a
    m' eref sref = do
        x <- m
        ask >>= writeRef eref
        get >>= writeRef sref
        return x

-- | Run a @Tc@ computation in the @KZC@ monad without updating the
-- @Tc@ environment.
withTc :: forall a . Tc a -> KZC a
withTc m = do
    eref   <- asks tcenvref
    sref   <- asks tcstateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTc (m' sref) env state
    return a
  where
    m' :: IORef TcState -> Tc a
    m' sref = do
        x <- m
        get >>= writeRef sref
        return x

instance Functor Tc where
    fmap f x = x >>= return . f

instance Applicative Tc where
    pure  = return
    (<*>) = ap

instance Monad Tc where
    {-# INLINE return #-}
    return a = Tc $ \_ s -> return (a, s)

    {-# INLINE (>>=) #-}
    m >>= f  = Tc $ \r s -> do
               (x, s') <- runTc m r s
               runTc (f x) r s'

    {-# INLINE (>>) #-}
    m1 >> m2 = Tc $ \r s -> do
               (_, s') <- runTc m1 r s
               runTc m2 r s'

    fail msg = throw (FailException (string msg))

instance MonadReader TcEnv Tc where
    ask = Tc $ \r s -> return (r, s)

    local f m = Tc $ \r s -> runTc m (f r) s

instance MonadState TcState Tc where
    get   = Tc $ \_ s -> return (s, s)
    put s = Tc $ \_ _ -> return ((), s)

instance MonadRef IORef Tc where
    newRef x     = liftIO $ newRef x
    readRef r    = liftIO $ readRef r
    writeRef r x = liftIO $ writeRef r x

instance MonadIO Tc where
    liftIO = liftKZC . liftIO

instance MonadUnique Tc where
    newUnique = liftKZC newUnique

instance MonadKZC Tc where
    liftKZC m = Tc $ \_ s -> do
                a <- m
                return (a, s)

instance MonadException Tc where
    throw e =
        throwContextException (liftKZC . throw) e

    m `catch` h = Tc $ \r s ->
      unTc m r s `catchContextException` \e -> unTc (h e) r s

instance MonadErr Tc where
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

localExp :: Exp -> Tc a -> Tc a
localExp e = local (\env -> env { curexp = Just e })

askCurrentExp :: Tc (Maybe Exp)
askCurrentExp = asks curexp

extendStructs :: [StructDef] -> Tc a -> Tc a
extendStructs ss m =
    extend structs (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: Struct -> Tc StructDef
lookupStruct s =
    lookupBy structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: Struct -> Tc (Maybe StructDef)
maybeLookupStruct s =
    asks (Map.lookup s . structs)

extendVars :: [(Var, Type)] -> Tc a -> Tc a
extendVars vtaus m =
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Var -> Tc Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendTyVars :: [(TyVar, Kind)] -> Tc a -> Tc a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Tc Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: [(IVar, Kind)] -> Tc a -> Tc a
extendIVars ivks m =
    extend iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: IVar -> Tc Kind
lookupIVar iv =
    lookupBy iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

localSTIndTypes :: Maybe (Type, Type, Type) -> Tc a -> Tc a
localSTIndTypes taus m =
    extendTyVars (alphas `zip` repeat TauK) $
    local (\env -> env { stIndTys = taus }) m
  where
    alphas :: [TyVar]
    alphas = case taus of
               Nothing      -> []
               Just (s,a,b) -> [alpha | TyVarT alpha _ <- [s,a,b]]

askSTIndTypes :: Tc (Type, Type, Type)
askSTIndTypes = do
    maybe_taus <- asks stIndTys
    case maybe_taus of
      Just taus -> return taus
      Nothing   -> faildoc $ text "Not in scope of an ST computation"

inScopeTyVars :: Tc (Set TyVar)
inScopeTyVars = do
    maybe_idxs <- asks stIndTys
    case maybe_idxs of
      Nothing         -> return mempty
      Just (s',a',b') -> return $ fvs [s',a',b']

traceNest :: Int -> Tc a -> Tc a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceLint :: Doc -> Tc ()
traceLint doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceLint)
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDocLn stderr $ text "traceLint:" <+> indent d (align doc)

withExpContext :: Exp -> Tc a -> Tc a
withExpContext e m =
    localExp e $
    withSummaryContext e m

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
    go :: Maybe Exp -> Tc Doc
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
