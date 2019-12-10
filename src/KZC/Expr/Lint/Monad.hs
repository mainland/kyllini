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

    MonadTc(..),
    MonadTcRef,
    asksTc,

    defaultValueC,

    localFvs,
    askCurrentFvs,

    extendStructs,
    lookupStruct,
    maybeLookupStruct,
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

    simplType,

    evalNat,

    hasZeroTypeSize,
    typeSize,
    typeSizeInBytes,

    withFvContext,

    relevantBindings,

    castStruct
  ) where

import Control.Monad.Except (ExceptT(..), runExceptT)
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
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
import Data.Loc (Located)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid ((<>))
#endif /* !MIN_VERSION_base(4,11,0) */
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Config
import KZC.Expr.Syntax
import KZC.Fuel
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Pretty
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
    , structs    = mempty
    , topScope   = True
    , topVars    = mempty
    , extFuns    = mempty
    , varTypes   = mempty
    , tyVars     = mempty
    , tyVarTypes = mempty
    , stTyVars   = mempty
    , stIndices  = Nothing
    }

class (Functor m, Applicative m, MonadFail m, MonadErr m, MonadConfig m, MonadFuel m, MonadPlatform m, MonadTrace m, MonadUnique m) => MonadTc m where
    askTc   :: m TcEnv
    localTc :: (TcEnv -> TcEnv) -> m a -> m a

-- | A 'MonadTc' with support for IO references.
class ( MonadTc m
      , MonadIO m
      , MonadRef IORef m
      , PrimMonad m
      , PrimState m ~ RealWorld)
    => MonadTcRef m

asksTc :: MonadTc m => (TcEnv -> a) -> m a
asksTc f = fmap f askTc

instance MonadTc m => MonadTc (MaybeT m) where
    askTc       = lift askTc
    localTc f m = MaybeT $ localTc f (runMaybeT m)

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
defaultValueC (IntT ip _)   = return $ IntC ip 0
defaultValueC (FixT qp _)   = return $ FixC qp 0
defaultValueC (FloatT fp _) = return $ FloatC fp 0
defaultValueC StringT{}     = return $ StringC ""

defaultValueC (StructT struct taus _) = do
    (fs, ftaus) <- unzip <$> tyAppStruct struct taus
    cs          <- mapM defaultValueC ftaus
    return $ StructC struct taus (fs `zip` cs)

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
    onerr = notInScope (text "Struct") s

maybeLookupStruct :: MonadTc m => Struct -> m (Maybe StructDef)
maybeLookupStruct s =
    asksTc (Map.lookup s . structs)

-- | Perform type application of a struct to type arguments and return the
-- resulting fields and their types.
tyAppStruct :: Monad m => StructDef -> [Type] -> m [(Field, Type)]
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
    onerr = notInScope (text "Variable") v

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
    onerr = notInScope (text "Type variable") tv

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
    onerr = notInScope (text "Instantiated type variable") alpha

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

-- | Simplify a type
simplType :: MonadTc m => Type -> m Type
simplType tau@UnitT{}   = pure tau
simplType tau@BoolT{}   = pure tau
simplType tau@IntT{}    = pure tau
simplType tau@FixT{}    = pure tau
simplType tau@FloatT{}  = pure tau
simplType tau@StringT{} = pure tau

simplType (StructT struct taus l) =
    StructT struct <$> mapM simplType taus <*> pure l

simplType (ArrT tau1 tau2 l) =
    ArrT <$> simplType tau1 <*> simplType tau2 <*> pure l

simplType (ST omega tau1 tau2 tau3 l) =
    ST omega <$> simplType tau1 <*> simplType tau2 <*> simplType tau3 <*> pure l

simplType (RefT tau l) =
    RefT <$> simplType tau <*> pure l

simplType (FunT taus tau l) =
    FunT <$> mapM simplType taus <*> simplType tau <*> pure l

simplType tau@NatT{} =
    pure tau

simplType (UnopT op tau0 l) =
    unop op <$> simplType tau0
  where
    unop :: Unop -> Type -> Type
    unop Neg tau = negate tau
    unop op  tau = UnopT op tau l

simplType (BinopT op tau1_0 tau2_0 l) =
    binop op <$> simplType tau1_0 <*> simplType tau2_0
  where
    binop :: Binop -> Type -> Type -> Type
    binop Add tau1 tau2 = tau1 + tau2
    binop Sub tau1 tau2 = tau1 - tau2
    binop Mul tau1 tau2 = tau1 * tau2
    binop Div tau1 tau2 = tau1 `quot` tau2
    binop op  tau1 tau2 = BinopT op tau1 tau2 l

simplType (ForallT tvks tau l) =
    ForallT tvks <$> simplType tau <*> pure l

simplType tau@(TyVarT alpha _) =
    fromMaybe tau <$> maybeLookupTyVarType alpha

-- | Evaluate a type of kind nat.
evalNat :: forall m . MonadTc m => Type -> m Int
evalNat (NatT n _) =
    return n

evalNat (UnopT op tau1 _) = do
    x <- evalNat tau1
    unop op x
  where
    unop :: Unop -> Int -> m Int
    unop Neg x = return $ -x
    unop op  _ = faildoc $ text "Illegal operation on nat:" <+> ppr op

evalNat (BinopT op tau1 tau2 _) = do
    x <- evalNat tau1
    y <- evalNat tau2
    binop op x y
  where
    binop :: Binop -> Int -> Int -> m Int
    binop Add x y = return $ x + y
    binop Sub x y = return $ x - y
    binop Mul x y = return $ x * y
    binop Div x y = return $ x `div` y
    binop op  _ _ = faildoc $ text "Illegal operation on nats:" <+> ppr op

evalNat (TyVarT alpha _) =
    lookupTyVarType alpha >>= evalNat

evalNat tau =
    faildoc $ text "Expected a type of kind nat, but got" <+> enquote (ppr tau)

-- | Return 'True' if type has a zero-size representation, 'False' otherwise. We
-- need this in addition to 'typeSize' because 'typeSize' requires that type
-- variables of kind nat are all defined to handle the case of arrays, and when
-- compiling size-polymorphic functions, we may not have this information.
hasZeroTypeSize :: forall m . MonadTc m => Type -> m Bool
hasZeroTypeSize = go
  where
    go :: Type -> m Bool
    go UnitT{}              = pure True
    go BoolT{}              = pure False
    go IntT{}               = pure False
    go FixT {}              = pure False
    go FloatT{}             = pure False
    go StringT{}            = pure False
    go (ArrT _ tau _)       = hasZeroTypeSize tau
    go (ST (C tau) _ _ _ _) = hasZeroTypeSize tau
    go (RefT tau _)         = hasZeroTypeSize tau

    go (StructT struct taus _) = do
        flds <- tyAppStruct struct taus
        and <$> mapM (hasZeroTypeSize . snd) flds

    go (ForallT _ (ST (C tau) _ _ _ _) _) =
        hasZeroTypeSize tau

    go tau@(TyVarT alpha _) = do
        maybe_tau <- maybeLookupTyVarType alpha
        case maybe_tau of
          Nothing   -> err tau
          Just tau' -> go tau'

    go tau =
        err tau

    err tau =
        faildoc $ text "Cannot determine whether type" <+> ppr tau <+> text "has zero size"

-- | Compute the size of a type in bits.
typeSize :: forall m . MonadTc m => Type -> m Int
typeSize = go
  where
    go :: Type -> m Int
    go UnitT{}              = pure 0
    go BoolT{}              = pure 1
    go (IntT ip _)          = ipBitSize ip
    go (FixT qp _)          = pure $ qpBitSize qp
    go (FloatT fp _)        = pure $ fpBitSize fp
    go (ArrT n tau _)       = (*) <$> evalNat n <*> go tau
    go (ST (C tau) _ _ _ _) = go tau
    go (RefT tau _)         = go tau

    go (StructT struct taus _) = do
        flds <- tyAppStruct struct taus
        sum <$> mapM (typeSize . snd) flds

    go (ForallT _ (ST (C tau) _ _ _ _) _) =
        go tau

    go tau@(TyVarT alpha _) = do
        maybe_tau <- maybeLookupTyVarType alpha
        case maybe_tau of
          Nothing   -> err tau
          Just tau' -> go tau'

    go tau =
        err tau

    err tau =
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
           -> StructDef
           -> [(Field, a)]
           -> m [(Field, a)]
castStruct cast (StructDef _ _ fldtaus _) flds =
    mapM (castField fldtaus) flds
  where
    castField :: [(Field, Type)] -> (Field, a) -> m (Field, a)
    castField fldtaus (f, val) = do
        tau <- case lookup f fldtaus of
                 Nothing  -> faildoc $ text "Unknown struct field" <+> ppr f
                 Just tau -> return tau
        (,) <$> pure f <*> cast tau val
