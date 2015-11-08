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
    MonadTc(..),
    asksTc,

    Tc(..),
    runTc,
    liftTc,
    withTc,

    localFvs,
    askCurrentFvs,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,

    inLocalScope,
    isInTopScope,
    askTopVars,

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

    withFvContext,

    relevantBindings
  ) where

import Control.Applicative
import Control.Monad (liftM)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.State (StateT(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (lift)
import Data.IORef
import Data.List (foldl')
import Data.Loc (Located)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Lint.State
import KZC.Monad
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

newtype Tc a = Tc { unTc :: ReaderT TcEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TcEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runTc :: Tc a -> TcEnv -> KZC a
runTc m r = (runReaderT . unTc) m r

-- | Run a @Tc@ computation in the @KZC@ monad and update the @Tc@ environment.
liftTc :: forall a . Tc a -> KZC a
liftTc m = do
    eref <- asks tcenvref
    env  <- readRef eref
    runTc (m' eref) env
  where
    m' :: IORef TcEnv -> Tc a
    m' eref = do
        x <- m
        askTc >>= writeRef eref
        return x

-- | Run a @Tc@ computation in the @KZC@ monad without updating the
-- @Tc@ environment.
withTc :: Tc a -> KZC a
withTc m = do
    eref <- asks tcenvref
    env  <- readRef eref
    runTc m env

class (Functor m, Applicative m, MonadErr m, MonadFlags m, MonadTrace m, MonadUnique m) => MonadTc m where
    askTc   :: m TcEnv
    localTc :: (TcEnv -> TcEnv) -> m a -> m a

asksTc :: MonadTc m => (TcEnv -> a) -> m a
asksTc f = liftM f askTc

instance MonadTc Tc where
    askTc       = Tc $ ask
    localTc f m = Tc $ local f (unTc m)

instance MonadTc m => MonadTc (ReaderT r m) where
    askTc       = lift askTc
    localTc f m = ReaderT $ \r -> localTc f (runReaderT m r)

instance MonadTc m => MonadTc (StateT r m) where
    askTc       = lift askTc
    localTc f m = StateT $ \s -> localTc f (runStateT m s)

extend :: forall k v a m . (Ord k, MonadTc m)
       => (TcEnv -> Map k v)
       -> (TcEnv -> Map k v -> TcEnv)
       -> [(k, v)]
       -> m a
       -> m a
extend _ _ [] m = m

extend proj upd kvs m = do
    localTc (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: (Ord k, MonadTc m)
         => (TcEnv -> Map k v)
         -> m v
         -> k
         -> m v
lookupBy proj onerr k = do
    maybe_v <- asksTc (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

localFvs :: (Fvs e Var, MonadTc m)
         => e
         -> m a
         -> m a
localFvs e = localTc (\env -> env { curfvs = Just (fvs e) })

askCurrentFvs :: MonadTc m => m (Maybe (Set Var))
askCurrentFvs = asksTc curfvs

extendStructs :: MonadTc m => [StructDef] -> m a -> m a
extendStructs ss m =
    extend structs (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: MonadTc m => Struct -> m StructDef
lookupStruct s =
    lookupBy structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: MonadTc m => Struct -> m (Maybe StructDef)
maybeLookupStruct s =
    asksTc (Map.lookup s . structs)

inLocalScope :: MonadTc m => m a -> m a
inLocalScope k =
    localTc (\env -> env { topScope = False }) k

isInTopScope :: MonadTc m => m Bool
isInTopScope = asksTc topScope

askTopVars :: MonadTc m => m (Set Var)
askTopVars = asksTc topVars

extendVars :: forall m a . MonadTc m => [(Var, Type)] -> m a -> m a
extendVars vtaus m = do
    topScope <- isInTopScope
    extendTopVars topScope (map fst vtaus) $ do
    extend varTypes (\env x -> env { varTypes = x }) vtaus m
  where
    extendTopVars :: Bool -> [Var] -> m a -> m a
    extendTopVars True vs k =
        localTc (\env -> env { topVars = topVars env `Set.union` Set.fromList vs }) k

    extendTopVars False _ k =
        k

extendBindVars :: MonadTc m => [BindVar] -> m a -> m a
extendBindVars bvs m =
    extendVars [(v, tau) | BindV v tau <- bvs] m

lookupVar :: MonadTc m => Var -> m Type
lookupVar v =
    lookupBy varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendTyVars :: MonadTc m => [(TyVar, Kind)] -> m a -> m a
extendTyVars tvks m =
    extend tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: MonadTc m => TyVar -> m Kind
lookupTyVar tv =
    lookupBy tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: MonadTc m => [(IVar, Kind)] -> m a -> m a
extendIVars ivks m =
    extend iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: MonadTc m => IVar -> m Kind
lookupIVar iv =
    lookupBy iVars onerr iv
  where
    onerr = faildoc $ text "Index variable" <+> ppr iv <+> text "not in scope"

localSTIndTypes :: MonadTc m => Maybe (Type, Type, Type) -> m a -> m a
localSTIndTypes taus m =
    extendTyVars (alphas `zip` repeat TauK) $
    localTc (\env -> env { stIndTys = taus }) m
  where
    alphas :: [TyVar]
    alphas = case taus of
               Nothing      -> []
               Just (s,a,b) -> [alpha | TyVarT alpha _ <- [s,a,b]]

inSTScope :: forall m a . MonadTc m => Type -> m a -> m a
inSTScope tau m =
    scopeOver tau m
  where
    scopeOver :: Type -> m a -> m a
    scopeOver (ST _ _ s a b _) m =
        localSTIndTypes (Just (s, a, b)) m

    scopeOver _ m =
        localSTIndTypes Nothing m

askSTIndTypes :: MonadTc m => m (Type, Type, Type)
askSTIndTypes = do
    maybe_taus <- asksTc stIndTys
    case maybe_taus of
      Just taus -> return taus
      Nothing   -> faildoc $ text "Not in scope of an ST computation"

inScopeTyVars :: MonadTc m => m (Set TyVar)
inScopeTyVars = do
    maybe_idxs <- asksTc stIndTys
    case maybe_idxs of
      Nothing         -> return mempty
      Just (s',a',b') -> return $ fvs [s',a',b']

withFvContext :: (Summary e, Located e, Fvs e Var, MonadTc m)
              => e
              -> m a
              -> m a
withFvContext e m =
    localFvs e $
    withSummaryContext e m

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: forall m . MonadTc m => m Doc
relevantBindings = do
    maybe_fvs <- fmap Set.toList <$> askCurrentFvs
    go maybe_fvs
  where
    go :: Maybe [Var] -> m Doc
    go Nothing =
        return Text.PrettyPrint.Mainland.empty

    go (Just vs) = do
        taus <- mapM lookupVar vs
        return $ line <>
            nest 2 (text "Relevant bindings:" </>
                    stack (map pprBinding (vs `zip` taus)))

    pprBinding :: (Var, Type) -> Doc
    pprBinding (v, tau) = nest 2 $ ppr v <+> text ":" <+> ppr tau
