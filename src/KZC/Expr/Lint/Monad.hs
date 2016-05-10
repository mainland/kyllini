{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Expr.Lint.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

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

    inLocalScope,
    isInTopScope,
    askTopVars,
    isTopVar,

    extendExtFuns,
    isExtFun,

    extendVars,
    lookupVar,

    extendTyVars,
    lookupTyVar,

    extendIVars,
    lookupIVar,

    localSTIndTypes,
    askSTIndTypes,
    inSTScope,

    extendLet,
    extendLetFun,

    inScopeTyVars,

    typeSize,

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
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import Data.IORef (IORef)
import Data.List (foldl')
import Data.Loc (Located, noLoc, srclocOf)
import Data.Map (Map)
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid, mempty)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Error
import KZC.Expr.Smart
import KZC.Expr.Syntax
import KZC.Flags
import KZC.Platform
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

data TcEnv = TcEnv
    { curfvs     :: !(Maybe (Set Var))
    , structs    :: !(Map Struct StructDef)
    , topScope   :: !Bool
    , topVars    :: !(Set Var)
    , extFuns    :: !(Set Var)
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
    , extFuns    = mempty
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
defaultValueC UnitT{}            = return UnitC
defaultValueC BoolT{}            = return $ BoolC False
defaultValueC (FixT sc s w bp _) = return $ FixC sc s w bp 0
defaultValueC (FloatT fp _)      = return $ FloatC fp 0
defaultValueC StringT{}          = return $ StringC ""

defaultValueC (StructT s _) = do
    StructDef s flds _ <- lookupStruct s
    let (fs, taus)     =  unzip flds
    cs                 <- mapM defaultValueC taus
    return $ StructC s (fs `zip` cs)

defaultValueC (ArrT (ConstI n _) tau _) = do
    c <- defaultValueC tau
    return $ ArrayC (replicate n c)

defaultValueC tau@ArrT{} =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@ST{} =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@RefT{} =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@FunT{} =
    faildoc $ text "Cannot generate default value for type" <+> ppr tau

defaultValueC tau@TyVarT{} =
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

inLocalScope :: MonadTc m => m a -> m a
inLocalScope = localTc $ \env -> env { topScope = False }

isInTopScope :: MonadTc m => m Bool
isInTopScope = asksTc topScope

askTopVars :: MonadTc m => m (Set Var)
askTopVars = asksTc topVars

isTopVar :: MonadTc m => Var -> m Bool
isTopVar v = asksTc (Set.member v . topVars)

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

extendTyVars :: MonadTc m => [(TyVar, Kind)] -> m a -> m a
extendTyVars = extendTcEnv tyVars (\env x -> env { tyVars = x })

lookupTyVar :: MonadTc m => TyVar -> m Kind
lookupTyVar tv =
    lookupTcEnv tyVars onerr tv
  where
    onerr = faildoc $ text "Type variable" <+> ppr tv <+> text "not in scope"

extendIVars :: MonadTc m => [(IVar, Kind)] -> m a -> m a
extendIVars = extendTcEnv iVars (\env x -> env { iVars = x })

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
inSTScope = scopeOver
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
             -> [IVar]
             -> [(Var, Type)]
             -> Type
             -> m a
             -> m a
extendLetFun _f ivs vbs tau_ret k =
    extendIVars (ivs `zip` repeat IotaK) $
    extendVars vbs $
    inSTScope tau_ret $
    inLocalScope k
  where
    _tau :: Type
    _tau = FunT ivs (map snd vbs) tau_ret (srclocOf tau_ret)

-- | Compute the size of a type in bits.
typeSize :: forall m . MonadTc m => Type -> m Int
typeSize = go
  where
    go :: Type -> m Int
    go UnitT{}                   = pure 0
    go BoolT{}                   = pure 1
    go (FixT _ _ w _ _)          = pure $ width w
    go (FloatT fp _)             = pure $ fpWidth fp
    go (StructT "complex" _)     = pure $ 2 * width dEFAULT_INT_WIDTH
    go (StructT "complex8" _)    = pure 16
    go (StructT "complex16" _)   = pure 32
    go (StructT "complex32" _)   = pure 64
    go (StructT "complex64" _)   = pure 128
    go (ArrT (ConstI n _) tau _) = (*) <$> pure n <*> go tau
    go (ST _ (C tau) _ _ _ _)    = go tau
    go (RefT tau _)              = go tau

    go (StructT s _) = do
        StructDef _ flds _ <- lookupStruct s
        sum <$> mapM (typeSize . snd) flds

    go tau =
        faildoc $ text "Cannot calculate bit width of type" <+> ppr tau

    width :: W -> Int
    width (W n) = n

    fpWidth :: FP -> Int
    fpWidth FP16 = 16
    fpWidth FP32 = 32
    fpWidth FP64 = 64

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
        return $ line <>
            nest 2 (text "Relevant bindings:" </>
                    stack (zipWith pprBinding vs taus))

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
    StructDef _ fldtaus _ <- lookupStruct sn
    mapM (castField fldtaus) flds
  where
    castField :: [(Field, Type)] -> (Field, a) -> m (Field, a)
    castField fldtaus (f, val) = do
        tau <- case lookup f fldtaus of
                 Nothing  -> faildoc $ text "Unknown struct field" <+> ppr f
                 Just tau -> return tau
        (,) <$> pure f <*> cast tau val
