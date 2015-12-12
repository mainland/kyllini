{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Lint.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Core.Lint.Monad (
    TcEnv(..),
    defaultTcEnv,

    MonadTc(..),
    asksTc,

    defaultValueC,

    localFvs,
    askCurrentFvs,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,

    inLocalScope,
    isInTopScope,
    askTopVars,

    extendVars,
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

import Control.Applicative (Applicative, (<$>))
import Control.Monad (liftM)
import Control.Monad.Error (Error, ErrorT(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import Data.List (foldl')
import Data.Loc (Located, noLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (Monoid, mempty)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

data TcEnv = TcEnv
    { curfvs     :: !(Maybe (Set Var))
    , structs    :: !(Map Struct StructDef)
    , topScope   :: !Bool
    , topVars    :: !(Set Var)
    , varTypes   :: !(Map Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , iVars      :: !(Map IVar Kind)
    , stIndTys   :: !(Maybe (Type, Type, Type))
    }
  deriving (Eq, Ord, Show)

defaultTcEnv :: TcEnv
defaultTcEnv = TcEnv
    { curfvs     = Nothing
    , structs    = Map.fromList [(structName s, s) | s <- builtinStructs]
    , topScope   = True
    , topVars    = mempty
    , varTypes   = mempty
    , tyVars     = mempty
    , iVars      = mempty
    , stIndTys   = Nothing
    }
  where
    builtinStructs :: [StructDef]
    builtinStructs =
        [ complexStruct "complex"   intT
        , complexStruct "complex8"  int8T
        , complexStruct "complex16" int16T
        , complexStruct "complex32" int32T
        , complexStruct "complex64" int64T ]

    complexStruct :: Struct -> Type -> StructDef
    complexStruct s tau =
        StructDef s [("re", tau), ("im", tau)] noLoc

class (Functor m, Applicative m, MonadErr m, MonadFlags m, MonadTrace m, MonadUnique m) => MonadTc m where
    askTc   :: m TcEnv
    localTc :: (TcEnv -> TcEnv) -> m a -> m a

asksTc :: MonadTc m => (TcEnv -> a) -> m a
asksTc f = liftM f askTc

instance MonadTc m => MonadTc (MaybeT m) where
    askTc       = lift askTc
    localTc f m = MaybeT $ localTc f (runMaybeT m)

instance (Error e, MonadTc m) => MonadTc (ErrorT e m) where
    askTc       = lift askTc
    localTc f m = ErrorT $ localTc f (runErrorT m)

instance MonadTc m => MonadTc (ReaderT r m) where
    askTc       = lift askTc
    localTc f m = ReaderT $ \r -> localTc f (runReaderT m r)

instance MonadTc m => MonadTc (StateT r m) where
    askTc       = lift askTc
    localTc f m = StateT $ \s -> localTc f (runStateT m s)

instance (Monoid w, MonadTc m) => MonadTc (WriterT w m) where
    askTc       = lift askTc
    localTc f m = WriterT $ localTc f (runWriterT m)

extendTcEnv :: forall k v a m . (Ord k, MonadTc m)
            => (TcEnv -> Map k v)
            -> (TcEnv -> Map k v -> TcEnv)
            -> [(k, v)]
            -> m a
            -> m a
extendTcEnv _ _ [] m = m

extendTcEnv proj upd kvs m = do
    localTc (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupTcEnv :: (Ord k, MonadTc m)
            => (TcEnv -> Map k v)
            -> m v
            -> k
            -> m v
lookupTcEnv proj onerr k = do
    maybe_v <- asksTc (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

-- | Given a type, produce a default (constant) value of that type
defaultValueC :: MonadTc m => Type -> m Const
defaultValueC (UnitT {})         = return UnitC
defaultValueC (BoolT {})         = return $ BoolC False
defaultValueC (BitT {})          = return $ BitC False
defaultValueC (FixT sc s w bp _) = return $ FixC sc s w bp 0
defaultValueC (FloatT fp _)      = return $ FloatC fp 0
defaultValueC (StringT {})       = return $ StringC ""

defaultValueC (StructT s _) = do
    StructDef s flds _ <- lookupStruct s
    let (fs, taus)     =  unzip flds
    cs                 <- mapM defaultValueC taus
    return $ StructC s (fs `zip` cs)

defaultValueC (ArrT (ConstI n _) tau _) = do
    c <- defaultValueC tau
    return $ ArrayC (replicate n c)

defaultValueC tau@(ArrT {}) =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@(ST {}) =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@(RefT {}) =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@(FunT {}) =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@(TyVarT {}) =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

localFvs :: (Fvs e Var, MonadTc m)
         => e
         -> m a
         -> m a
localFvs e = localTc (\env -> env { curfvs = Just (fvs e) })

askCurrentFvs :: MonadTc m => m (Maybe (Set Var))
askCurrentFvs = asksTc curfvs

extendStructs :: MonadTc m => [StructDef] -> m a -> m a
extendStructs ss m =
    extendTcEnv structs
        (\env x -> env { structs = x }) [(structName s, s) | s <- ss] m

lookupStruct :: MonadTc m => Struct -> m StructDef
lookupStruct s =
    lookupTcEnv structs onerr s
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
    extendTcEnv varTypes (\env x -> env { varTypes = x }) vtaus m
  where
    extendTopVars :: Bool -> [Var] -> m a -> m a
    extendTopVars True vs k =
        localTc (\env -> env { topVars = topVars env `Set.union` Set.fromList vs }) k

    extendTopVars False _ k =
        k

lookupVar :: MonadTc m => Var -> m Type
lookupVar v =
    lookupTcEnv varTypes onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendTyVars :: MonadTc m => [(TyVar, Kind)] -> m a -> m a
extendTyVars tvks m =
    extendTcEnv tyVars (\env x -> env { tyVars = x }) tvks m

lookupTyVar :: MonadTc m => TyVar -> m Kind
lookupTyVar tv =
    lookupTcEnv tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: MonadTc m => [(IVar, Kind)] -> m a -> m a
extendIVars ivks m =
    extendTcEnv iVars (\env x -> env { iVars = x }) ivks m

lookupIVar :: MonadTc m => IVar -> m Kind
lookupIVar iv =
    lookupTcEnv iVars onerr iv
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
