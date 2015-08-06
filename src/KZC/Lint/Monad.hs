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

    shift,
    reset,

    localExp,
    askCurrentExp,

    extendVars,
    lookupVar,

    extendTyVars,
    lookupTyVar,

    extendIVars,
    lookupIVar,

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
import qualified Data.Set as Set
import System.IO (hPutStrLn, stderr)
import Text.PrettyPrint.Mainland

import Language.Core.Syntax

import KZC.Lint.State
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Uniq
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

    fail msg = throw (FailException (string msg))

instance MonadReader TcEnv (Tc b) where
    ask = Tc $ \r s k -> k r r s

    local f m =Tc $ \r s k -> unTc m (f r) s $ \x _ s' -> k x r s'

instance MonadState TcState (Tc b) where
    get   = Tc $ \r s k -> k s r s
    put s = Tc $ \r _ k -> k () r s

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
           else do ctx <- take <$> getMaxContext <*> askErrCtx
                   liftIO $ hPutStrLn stderr $
                     pretty 80 (text "Warning:" <+> ppr (toContextException ctx e))

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

localExp :: Exp -> Tc b a -> Tc b a
localExp e = local (\env -> env { curexp = Just e })

askCurrentExp :: Tc b (Maybe Exp)
askCurrentExp = asks curexp

extendVars :: [(Var, Type)] -> Tc b a -> Tc b a
extendVars vtaus m =
    extend varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Var -> Tc b Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendTyVars :: [(TyVar, Kind)] -> Tc b a -> Tc b a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: TyVar -> Tc b Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: [(IVar, Kind)] -> Tc b a -> Tc b a
extendIVars ivks m =
    extend iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: IVar -> Tc b Kind
lookupIVar iv =
    lookupBy iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

traceNest :: Int -> Tc b a -> Tc b a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceLint :: Doc -> Tc b ()
traceLint doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceLint)
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDocLn stderr $ text "traceLint:" <+> indent d (align doc)

withExpContext :: Exp -> Tc b a -> Tc b a
withExpContext e m =
    localExp e $
    withSummaryContext e m

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
    go :: Maybe Exp -> Tc b Doc
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
