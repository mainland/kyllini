{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Expr.Lint.Monad
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Expr.Lint.Monad (
    TcEnv(..),
    defaultTcEnv,
    complexStructDef,

    MonadTc(..),
    MonadTcRef,
    asksTc,

    defaultValueC,

    localFvs,
    askCurrentFvs,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,
    lookupStructFields,
    tyAppStruct,

    inLocalScope,
    isInTopScope,
    askTopVars,
    isTopVar,
    withTopVars,

    extendExtFuns,
    isExtFun,

    extendVars,
    lookupVar,

    extendTyVars,
    lookupTyVar,
    inScopeTyVars,

    extendTyVarTypes,
    maybeLookupTyVarType,
    lookupTyVarType,
    askTyVarTypeSubst,

    localSTTyVars,
    askSTTyVars,

    localSTIndices,
    askSTIndices,
    inSTScope,

    extendLet,
    extendLetFun,

    typeSize,
    typeSizeInBytes,

    withFvContext,

    relevantBindings,

    castStruct
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Primitive (PrimMonad(..),
                                RealWorld)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Ref (MonadRef(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))
import Data.IORef (IORef)
import Data.List (foldl')
import Data.Loc (Located, noLoc)
import Data.Map (Map)
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid, mempty)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Expr.Smart
import KZC.Expr.Syntax
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

data TcEnv = TcEnv
    { curfvs     :: !(Maybe (Set Var))
    , structs    :: !(Map Struct StructDef)
    , topScope   :: !Bool
    , topVars    :: !(Set Var)
    , extFuns    :: !(Set Var)
    , varTypes   :: !(Map Var Type)
    , tyVars     :: !(Map TyVar Kind)
    , tyVarTypes :: !(Map TyVar Type)
    , stTyVars   :: !(Set TyVar)
    , stIndices  :: !(Maybe (Type, Type, Type))
    }
  deriving (Eq, Ord, Show)

defaultTcEnv :: TcEnv
defaultTcEnv = TcEnv
    { curfvs     = Nothing
    , structs    = Map.fromList [(structName s, s) | s <- builtinStructs]
    , topScope   = True
    , topVars    = mempty
    , extFuns    = mempty
    , varTypes   = mempty
    , tyVars     = mempty
    , tyVarTypes = mempty
    , stTyVars   = mempty
    , stIndices  = Nothing
    }
  where
    builtinStructs :: [StructDef]
    builtinStructs = [complexStructDef]

complexStructDef :: StructDef
complexStructDef = StructDef "Complex" [(a, num)] [("re", tyVarT a), ("im", tyVarT a)] noLoc
  where
    a :: TyVar
    a = "a"

    num :: Kind
    num = TauK (traits [NumR])

class (Functor m, Applicative m, MonadErr m, MonadConfig m, MonadPlatform m, MonadTrace m, MonadUnique m) => MonadTc m where
    askTc   :: m TcEnv
    localTc :: (TcEnv -> TcEnv) -> m a -> m a

-- | A 'MonadTc' with support for IO references.
class (MonadTc m, MonadIO m, MonadRef IORef m,
       PrimMonad m, PrimState m ~ RealWorld)
    => MonadTcRef m

asksTc :: MonadTc m => (TcEnv -> a) -> m a
asksTc f = fmap f askTc

instance MonadTc m => MonadTc (MaybeT m) where
    askTc       = lift askTc
    localTc f m = MaybeT $ localTc f (runMaybeT m)

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadTc m) => MonadTc (ErrorT e m) where
    askTc       = lift askTc
    localTc f m = ErrorT $ localTc f (runErrorT m)
#endif /* !MIN_VERSION_base(4,8,0) */

instance MonadTc m => MonadTc (ExceptT e m) where
    askTc       = lift askTc
    localTc f m = ExceptT $ localTc f (runExceptT m)

instance MonadTc m => MonadTc (ReaderT r m) where
    askTc       = lift askTc
    localTc f m = ReaderT $ \r -> localTc f (runReaderT m r)

instance MonadTc m => MonadTc (StateT r m) where
    askTc       = lift askTc
    localTc f m = StateT $ \s -> localTc f (runStateT m s)

instance MonadTc m => MonadTc (S.StateT r m) where
    askTc       = lift askTc
    localTc f m = S.StateT $ \s -> localTc f (S.runStateT m s)

instance (Monoid w, MonadTc m) => MonadTc (WriterT w m) where
    askTc       = lift askTc
    localTc f m = WriterT $ localTc f (runWriterT m)

instance (Monoid w, MonadTc m) => MonadTc (S.WriterT w m) where
    askTc       = lift askTc
    localTc f m = S.WriterT $ localTc f (S.runWriterT m)

instance MonadTcRef m => MonadTcRef (MaybeT m) where

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadTcRef m) => MonadTcRef (ErrorT e m) where
#endif /* !MIN_VERSION_base(4,8,0) */

instance MonadTcRef m => MonadTcRef (ExceptT e m) where

instance MonadTcRef m => MonadTcRef (ReaderT r m) where

instance MonadTcRef m => MonadTcRef (StateT r m) where

instance MonadTcRef m => MonadTcRef (S.StateT r m) where

instance (Monoid w, MonadTcRef m) => MonadTcRef (WriterT w m) where

instance (Monoid w, MonadTcRef m) => MonadTcRef (S.WriterT w m) where

extendTcEnv :: forall k v a m . (Ord k, MonadTc m)
            => (TcEnv -> Map k v)
            -> (TcEnv -> Map k v -> TcEnv)
            -> [(k, v)]
            -> m a
            -> m a
extendTcEnv _ _ [] m = m

extendTcEnv proj upd kvs m =
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
defaultValueC UnitT{}       = return UnitC
defaultValueC BoolT{}       = return $ BoolC False
defaultValueC (FixT ip _)   = return $ FixC ip 0
defaultValueC (FloatT fp _) = return $ FloatC fp 0
defaultValueC StringT{}     = return $ StringC ""

defaultValueC (StructT s taus _) = do
    sdef        <- lookupStruct s
    (fs, ftaus) <- unzip <$> tyAppStruct sdef taus
    cs          <- mapM defaultValueC ftaus
    return $ StructC s taus (fs `zip` cs)

defaultValueC (ArrT (NatT n _) tau _) = do
    c <- defaultValueC tau
    return $ ReplicateC n c

defaultValueC tau =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

localFvs :: (Fvs e Var, MonadTc m)
         => e
         -> m a
         -> m a
localFvs e = localTc (\env -> env { curfvs = Just (fvs e) })

askCurrentFvs :: MonadTc m => m (Maybe (Set Var))
askCurrentFvs = asksTc curfvs

extendStructs :: MonadTc m => [StructDef] -> m a -> m a
extendStructs ss =
    extendTcEnv structs
        (\env x -> env { structs = x }) [(structName s, s) | s <- ss]

lookupStruct :: MonadTc m => Struct -> m StructDef
lookupStruct s =
    lookupTcEnv structs onerr s
  where
    onerr = faildoc $ text "Struct" <+> ppr s <+> text "not in scope"

maybeLookupStruct :: MonadTc m => Struct -> m (Maybe StructDef)
maybeLookupStruct s =
    asksTc (Map.lookup s . structs)

lookupStructFields :: MonadTc m => Struct -> [Type] -> m [(Field, Type)]
lookupStructFields struct taus = do
    sdef <- lookupStruct struct
    tyAppStruct sdef taus

-- | Perform type application of a struct to type arguments and return the
-- resulting fields and their types.
tyAppStruct :: forall m . MonadTc m => StructDef -> [Type] -> m [(Field, Type)]
tyAppStruct (StructDef _ tvks flds _) taus =
    return (map fst flds `zip` subst theta mempty (map snd flds))
  where
    theta :: Map TyVar Type
    theta = Map.fromList (map fst tvks `zip` taus)

inLocalScope :: MonadTc m => m a -> m a
inLocalScope = localTc $ \env -> env { topScope = False }

isInTopScope :: MonadTc m => m Bool
isInTopScope = asksTc topScope

askTopVars :: MonadTc m => m (Set Var)
askTopVars = asksTc topVars

isTopVar :: MonadTc m => Var -> m Bool
isTopVar v = asksTc (Set.member v . topVars)

withTopVars :: MonadTc m => m a -> m a
withTopVars =
    localTc $ \env ->
      env { varTypes = Map.filterWithKey (\v _ -> Set.member v (topVars env))
                                         (varTypes env) }

extendExtFuns :: MonadTc m => [(Var, Type)] -> m a -> m a
extendExtFuns vtaus k =
    localTc (\env -> env { extFuns = fs <> extFuns env }) $
    extendVars vtaus k
  where
    fs :: Set Var
    fs = Set.fromList $ map fst vtaus

isExtFun :: MonadTc m => Var -> m Bool
isExtFun f = asksTc (Set.member f . extFuns)

extendVars :: forall m a . MonadTc m => [(Var, Type)] -> m a -> m a
extendVars vtaus m = do
    topScope <- isInTopScope
    extendTopVars topScope (map fst vtaus) $
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

extendTyVars :: MonadTc m => [Tvk] -> m a -> m a
extendTyVars tvks =
    localTc $ \env -> env
      { tyVars     = foldl' insert (tyVars env) tvks
      , tyVarTypes = foldl' delete (tyVarTypes env) (map fst tvks)
      }
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert m (k, v) = Map.insert k v m

    delete :: Ord k => Map k v -> k -> Map k v
    delete m k = Map.delete k m

lookupTyVar :: MonadTc m => TyVar -> m Kind
lookupTyVar tv =
    lookupTcEnv tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

-- | Return currently in scope type variables.
inScopeTyVars :: MonadTc m => m (Set TyVar)
inScopeTyVars = asksTc (Map.keysSet . tyVars)

extendTyVarTypes :: MonadTc m => [(TyVar, Type)] -> m a -> m a
extendTyVarTypes = extendTcEnv tyVarTypes (\env x -> env { tyVarTypes = x })

maybeLookupTyVarType :: MonadTc m => TyVar -> m (Maybe Type)
maybeLookupTyVarType alpha = asksTc (Map.lookup alpha . tyVarTypes)

lookupTyVarType :: MonadTc m => TyVar -> m Type
lookupTyVarType alpha =
    lookupTcEnv tyVarTypes onerr alpha
  where
    onerr = faildoc $
            text "Instantiated type variable" <+> ppr alpha <+>
            text "not in scope"

-- | Return the current substitution from type variables to types.
askTyVarTypeSubst :: MonadTc m => m (Map TyVar Type)
askTyVarTypeSubst = asksTc tyVarTypes

-- | Record the set of type variables quantified over an ST type inside the term
-- of that type. For example, inside a term of type @forall a b . ST (C c) a a
-- b@, we mark @a@ and @b@ as locally quantified.
localSTTyVars :: MonadTc m => [Tvk] -> m a -> m a
localSTTyVars tvks =
    localTc (\env -> env { stTyVars = Set.fromList (map fst tvks) })

askSTTyVars :: MonadTc m => m (Set TyVar)
askSTTyVars = asksTc stTyVars

-- | Specify the current three ST type indices.
localSTIndices :: MonadTc m => Maybe (Type, Type, Type) -> m a -> m a
localSTIndices taus = localTc (\env -> env { stIndices = taus })

-- | Return the current three ST type indices.
askSTIndices :: MonadTc m => m (Type, Type, Type)
askSTIndices = do
    maybe_taus <- asksTc stIndices
    case maybe_taus of
      Just taus -> return taus
      Nothing   -> faildoc $ text "Not in scope of an ST computation"

-- | Execute a continuation in the scope of an ST type.
inSTScope :: forall m a . MonadTc m => Type -> m a -> m a
inSTScope = scopeOver
  where
    scopeOver :: Type -> m a -> m a
    scopeOver (ForallT tvks (ST _ s a b _) _) k =
        extendTyVars tvks $
        localSTTyVars tvks $
        localSTIndices (Just (s, a, b)) k

    scopeOver (ST _ s a b _) k =
        localSTIndices (Just (s, a, b)) k

    scopeOver _ k =
        localSTIndices Nothing k

extendLet :: MonadTc m
          => v
          -> Type
          -> m a
          -> m a
extendLet _v tau k =
    inSTScope tau $
    inLocalScope k

extendLetFun :: MonadTc m
             => v
             -> [Tvk]
             -> [(Var, Type)]
             -> Type
             -> m a
             -> m a
extendLetFun _f tvks vbs tau_ret k =
    extendTyVars tvks $
    extendVars vbs $
    inSTScope tau_ret $
    inLocalScope k

-- | Compute the size of a type in bits.
typeSize :: forall m . MonadTc m => Type -> m Int
typeSize = go
  where
    go :: Type -> m Int
    go UnitT{}                 = pure 0
    go BoolT{}                 = pure 1
    go (FixT IDefault _)       = asksPlatform platformIntWidth
    go (FixT (I w) _)          = pure w
    go (FixT UDefault _)       = asksPlatform platformIntWidth
    go (FixT (U w) _)          = pure w
    go (FloatT fp _)           = pure $ fpWidth fp
    go (ArrT (NatT n _) tau _) = (*) <$> pure n <*> go tau
    go (ST (C tau) _ _ _ _)    = go tau
    go (RefT tau _)            = go tau

    go (StructT s taus _) = do
        sdef <- lookupStruct s
        flds <- tyAppStruct sdef taus
        sum <$> mapM (typeSize . snd) flds

    go (ForallT _ (ST (C tau) _ _ _ _) _) =
        go tau

    go tau =
        faildoc $ text "Cannot calculate bit width of type" <+> ppr tau

-- | Compute the size of a type in bytes.
typeSizeInBytes :: forall m . MonadTc m => Type -> m Int
typeSizeInBytes tau = quot <$> typeSize tau <*> pure 8

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
relevantBindings =
    fmap Set.toList <$> askCurrentFvs >>= go
  where
    go :: Maybe [Var] -> m Doc
    go (Just vs@(_:_)) = do
        taus <- mapM lookupVar vs
        return $ nest 2 $
          text "Relevant bindings:" </>
          stack (zipWith pprBinding vs taus)

    go _ =
        return Text.PrettyPrint.Mainland.empty

    pprBinding :: Var -> Type -> Doc
    pprBinding v tau = nest 2 $ ppr v <+> text ":" <+> ppr tau

{------------------------------------------------------------------------------
 -
 - Struct Casting
 -
 ------------------------------------------------------------------------------}

castStruct :: forall a m . MonadTc m
           => (Type -> a -> m a)
           -> Struct
           -> [(Field, a)]
           -> m [(Field, a)]
castStruct cast sn flds = do
    StructDef _ _ fldtaus _ <- lookupStruct sn
    mapM (castField fldtaus) flds
  where
    castField :: [(Field, Type)] -> (Field, a) -> m (Field, a)
    castField fldtaus (f, val) = do
        tau <- case lookup f fldtaus of
                 Nothing  -> faildoc $ text "Unknown struct field" <+> ppr f
                 Just tau -> return tau
        (,) <$> pure f <*> cast tau val
