{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check.Monad
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check.Monad (
    Ti(..),
    runTi,
    liftTi,
    liftTi',

    localExp,
    askCurrentExp,

    localValCtxType,
    askValCtxType,
    withValCtx,
    tellValCtx,

    extendStructs,
    lookupStruct,
    askStructIds,
    maybeLookupStruct,
    tyAppStruct,

    extendCoreStructs,
    lookupCoreStruct,

    extendVars,
    lookupVar,

    askEnvMtvs,

    extendTyVars,
    lookupTyVar,

    extendTyVarTypes,
    maybeLookupTyVarType,
    lookupTyVarType,

    simplNat,

    typeSize,

    withExpContext,

    readTv,
    writeTv,
    newMetaTv,
    newMetaTvT,

    readKv,
    writeKv,
    newMetaKv,
    newMetaKvK,

    readRv,
    writeRv,
    newMetaRv,

    relevantBindings,
    sanitizeTypes,

    metaTvs,

    Compress(..)
  ) where

import Control.Monad.Exception
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State
import Data.Foldable (toList)
import Data.IORef
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Smart
import KZC.Check.State
import KZC.Check.Types
import KZC.Config
import qualified KZC.Expr.Syntax as E
import KZC.Monad
import KZC.Platform
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

newtype Ti a = Ti { unTi :: ReaderT TiEnv (StateT TiState KZC) a }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadFail
             , MonadIO
             , MonadRef IORef
             , MonadAtomicRef IORef
             , MonadReader TiEnv
             , MonadState TiState
             , MonadException
             , MonadUnique
             , MonadErr
             , MonadConfig
             , MonadPlatform
             , MonadTrace)

runTi :: Ti a -> TiEnv -> TiState -> KZC (a, TiState)
runTi m r = runStateT (runReaderT (unTi m) r)

-- | Run a @Ti@ computation in the @KZC@ monad and update the @Ti@ environment.
liftTi :: forall a . ((a -> Ti a) -> Ti a) -> KZC a
liftTi m = do
    eref   <- asks tienvref
    sref   <- asks tistateref
    env    <- readRef eref
    state  <- readRef sref
    (a, _) <- runTi (m' eref sref) env state
    return a
  where
    m' :: IORef TiEnv -> IORef TiState -> Ti a
    m' eref sref =
        m $ \x -> do
        ask >>= writeRef eref
        get >>= writeRef sref
        return x

-- | Run a @Ti@ computation in the @KZC@ monad without updating the @Ti@
-- environment.
liftTi' :: Ti a -> KZC a
liftTi' m = do
    env    <- asks tienvref >>= readRef
    state  <- asks tistateref >>= readRef
    (a, _) <- runTi m env state
    return a

-- | Specify the current expression we are working with.
localExp :: Z.Exp -> Ti a -> Ti a
localExp e = local (\env -> env { curexp = Just e })

-- | Ask the current expression we are working with. We use this to list
-- relevant bindings in error messages.
askCurrentExp :: Ti (Maybe Z.Exp)
askCurrentExp = asks curexp

-- | Specify the type of the computational context in which we need to produce a
-- value.
localValCtxType :: Type -> Ti a -> Ti a
localValCtxType tau = local $ \env -> env { valCtxType = tau }

-- | Ask the type of the computational context in which we need to produce a
-- value.
askValCtxType :: Ti Type
askValCtxType = asks valCtxType

-- | Given a computation that produces a 'E.Exp', return a new computation that
-- produces the same 'E.Exp' modified to incorporate the value context.
withValCtx :: Ti E.Exp -> Ti E.Exp
withValCtx mce = do
    old_valctx <- gets valctx
    modify $ \s -> s { valctx = id }
    ce <- mce
    f  <- gets valctx
    modify $ \s -> s { valctx = old_valctx }
    return $ f ce

-- | Specify a function for adding necessary value context to a 'E.Exp'
-- representing a computation.
tellValCtx :: (E.Exp -> E.Exp) -> Ti ()
tellValCtx f = modify $ \s -> s { valctx = valctx s . f }

extendStructs :: [StructDef] -> Ti a -> Ti a
extendStructs ss =
    extendEnv structs
        (\env x -> env { structs = x }) [(structName s, s) | s <- ss]

lookupStruct :: Z.Struct -> Ti StructDef
lookupStruct s =
    lookupEnv structs onerr s
  where
    onerr = notInScope (text "Struct") s

-- | Return the set of all declared struct identifiers.
askStructIds :: Ti (Set Z.Struct)
askStructIds =
    Map.keysSet <$> asks structs

maybeLookupStruct :: Z.Struct -> Ti (Maybe StructDef)
maybeLookupStruct s =
    asks (Map.lookup s . structs)

-- | Perform type application of a struct to type arguments and return the
-- resulting type and its fields.
tyAppStruct :: StructDef -> [Type] -> Ti (Type, [(Z.Field, Type)])
tyAppStruct struct taus = go struct
  where
    theta :: Map TyVar Type
    theta = Map.fromList (map fst tvks `zip` taus)

    tvks :: [Tvk]
    tvks = case struct of
             StructDef _ tvks _ _ -> tvks
             TypeDef _ tvks _ _   -> tvks

    go (StructDef s _ flds _) =
        return (structT s taus, map fst flds `zip` subst theta mempty (map snd flds))

    go (TypeDef s tvks (SynT _ tau' _) l) =
        go (TypeDef s tvks tau' l)

    go (TypeDef s _ (StructT s' taus' _) _) = do
        struct'      <- lookupStruct s'
        (tau', flds) <- tyAppStruct struct' taus'
        return (synT (structT s taus) tau', flds)

    go (TypeDef s _ tau' _) =
        return (synT (structT s taus) tau', [])

extendCoreStructs :: [E.StructDef] -> Ti a -> Ti a
extendCoreStructs ss =
    extendEnv cstructs
        (\env x -> env { cstructs = x }) [(E.structName s, s) | s <- ss]

lookupCoreStruct :: E.Struct -> Ti E.StructDef
lookupCoreStruct s =
    lookupEnv cstructs onerr s
  where
    onerr = notInScope (text "Struct") s

extendVars :: [(Z.Var, Type)] -> Ti a -> Ti a
extendVars vtaus m = do
    mtvs <- fvs <$> compress (map snd vtaus)
    local (\env -> env { envMtvs = mtvs `Set.union` envMtvs env }) $
      extendEnv varTypes (\env x -> env { varTypes = x }) vtaus m

lookupVar :: Z.Var -> Ti Type
lookupVar v =
    lookupEnv varTypes onerr v
  where
    onerr = notInScope (text "Variable") v

askEnvMtvs :: Ti [MetaTv]
askEnvMtvs =
    concat <$> (asks (Set.toList . envMtvs) >>= mapM simplify)
  where
    simplify :: MetaTv -> Ti [MetaTv]
    simplify mtv = do
        maybe_tau <- readTv mtv
        case maybe_tau of
          Just tau  -> (Set.toList . fvs) <$> compress tau
          Nothing   -> return [mtv]

extendTyVars :: [Tvk] -> Ti a -> Ti a
extendTyVars = extendEnv tyVars (\env x -> env { tyVars = x })

lookupTyVar :: TyVar -> Ti Kind
lookupTyVar tv =
    lookupEnv tyVars onerr tv
  where
    onerr = notInScope (text "Type variable") tv

extendTyVarTypes :: [(TyVar, Type)] -> Ti a -> Ti a
extendTyVarTypes = extendEnv tyVarTypes (\env x -> env { tyVarTypes = x })

maybeLookupTyVarType :: TyVar -> Ti (Maybe Type)
maybeLookupTyVarType alpha = asks (Map.lookup alpha . tyVarTypes)

lookupTyVarType :: TyVar -> Ti Type
lookupTyVarType alpha =
    lookupEnv tyVarTypes onerr alpha
  where
    onerr = notInScope (text "Instantiated type variable") alpha

-- | Simplify a type of kind nat.
simplNat :: Type -> Ti Type
simplNat (UnopT op tau0 l) =
    unop op <$> simplNat tau0
  where
    unop :: Unop -> Type -> Type
    unop Neg tau = negate tau
    unop op  tau = UnopT op tau l

simplNat (BinopT op tau1_0 tau2_0 l) =
    binop op <$> simplNat tau1_0 <*> simplNat tau2_0
  where
    binop :: Binop -> Type -> Type -> Type
    binop Add tau1 tau2 = tau1 + tau2
    binop Sub tau1 tau2 = tau1 - tau2
    binop Mul tau1 tau2 = tau1 * tau2
    binop Div tau1 tau2 = tau1 `quot` tau2
    binop op  tau1 tau2 = BinopT op tau1 tau2 l

simplNat tau@(TyVarT alpha _) = do
    maybe_tau' <- maybeLookupTyVarType alpha
    case maybe_tau' of
      Nothing   -> return tau
      Just tau' -> simplNat tau'

simplNat tau =
    pure tau

-- | Compute the size of a type in bits.
typeSize :: Type -> Ti Int
typeSize = simplNat >=> go
  where
    go :: Type -> Ti Int
    go UnitT{}                 = pure 0
    go BoolT{}                 = pure 1
    go (IntT ip _)             = ipBitSize ip
    go (FloatT fp _)           = pure $ fpBitSize fp
    go (ArrT (NatT n _) tau _) = (*) <$> pure n <*> go tau
    go (ST (C tau _) _ _ _ _)  = go tau
    go (RefT tau _)            = go tau

    go (StructT s taus _) = do
        struct    <- lookupStruct s
        (_, flds) <- tyAppStruct struct taus
        sum <$> mapM (typeSize . snd) flds

    go (ForallT _ (ST (C tau _) _ _ _ _) _) =
        go tau

    go tau =
        faildoc $ text "Cannot calculate bit width of type" <+> ppr tau

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
    k'    <- case k of
               TauK (R ts) -> do mrv <- newMetaRv ts
                                 return $ TauK (MetaR mrv)
               _           -> return k
    return $ MetaTv u k' tref

newMetaTvT :: Located a => Kind -> a -> Ti Type
newMetaTvT k x = MetaT <$> newMetaTv k <*> pure (srclocOf x)

readKv :: MonadRef IORef m => MetaKv -> m (Maybe Kind)
readKv (MetaKv _ ref) = readRef ref

writeKv :: MonadRef IORef m => MetaKv -> Kind -> m ()
writeKv (MetaKv _ ref) kappa = writeRef ref (Just kappa)

newMetaKv :: Ti MetaKv
newMetaKv = do
    u     <- newUnique
    kref  <- newRef Nothing
    return $ MetaKv u kref

newMetaKvK :: Located a => a -> Ti Kind
newMetaKvK _x = MetaK <$> newMetaKv

readRv :: MonadRef IORef m => MetaRv -> m (Maybe R)
readRv (MetaRv _ _ ref) = readRef ref

writeRv :: MonadRef IORef m => MetaRv -> R -> m ()
writeRv (MetaRv _ _ ref) ts = writeRef ref (Just ts)

newMetaRv :: Traits -> Ti MetaRv
newMetaRv ts = do
    u     <- newUnique
    tref  <- newRef Nothing
    return $ MetaRv u ts tref

{------------------------------------------------------------------------------
 -
 - Error handling
 -
 ------------------------------------------------------------------------------}

relevantBindings :: Ti Doc
relevantBindings =
    fmap (Set.toList . fvs) <$> askCurrentExp >>= go
  where
    go :: Maybe [Z.Var] -> Ti Doc
    go (Just vs@(_:_)) = do
        taus <- mapM lookupVar vs >>= sanitizeTypes
        return $ nest 2 $
          text "Relevant bindings:" </>
          stack (zipWith pprBinding vs taus)
    go _ =
        return Text.PrettyPrint.Mainland.empty

    pprBinding :: Z.Var -> Type -> Doc
    pprBinding v tau = nest 2 $ ppr v <+> text ":" <+> ppr tau

sanitizeTypes :: ( Compress a
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
    compress :: MonadRef IORef m => a -> m a

instance (Traversable f, Compress a) => Compress (f a) where
    compress = traverse compress

instance Compress a => Compress (L a) where
    compress (L loc a) =
        L loc <$> compress a

instance Compress Type where
    compress tau@UnitT{} =
        pure tau

    compress tau@BoolT{} =
        pure tau

    compress tau@IntT{} =
        pure tau

    compress tau@FixT{} =
        pure tau

    compress tau@FloatT{} =
        pure tau

    compress tau@StringT{} =
        pure tau

    compress (StructT s taus l) =
        StructT s <$> compress taus <*> pure l

    compress (SynT _tau1 tau2 _l) =
        compress tau2

    compress (ArrT tau1 tau2 l) =
        ArrT <$> compress tau1 <*> compress tau2 <*> pure l

    compress (C tau l) =
        C <$> compress tau <*> pure l

    compress tau@T{} =
        pure tau

    compress (ST omega tau1 tau2 tau3 l) =
        ST <$> compress omega <*> compress tau1 <*>
           compress tau2 <*> compress tau3 <*> pure l

    compress (RefT tau l) =
        RefT <$> compress tau <*> pure l

    compress (FunT taus tau l) =
        FunT <$> compress taus <*> compress tau <*> pure l

    compress tau@NatT{} =
        pure tau

    compress (UnopT op tau l) =
        UnopT op <$> compress tau <*> pure l

    compress (BinopT op tau1 tau2 l) =
        BinopT op <$> compress tau1 <*> compress tau2 <*> pure l

    compress (ForallT tvks tau l) =
        ForallT <$> compress tvks <*> compress tau <*> pure l

    compress tau@TyVarT{} =
        pure tau

    compress tau@(MetaT mtv _) = do
        maybe_tau' <- readTv mtv
        case maybe_tau' of
          Nothing    ->  return tau
          Just tau'  ->  do  tau'' <- compress tau'
                             writeTv mtv tau''
                             return tau''

instance Compress Kind where
    compress (TauK r)     = TauK <$> compress r
    compress kappa@OmegaK = return kappa
    compress kappa@MuK    = return kappa
    compress kappa@RhoK   = return kappa
    compress kappa@PhiK   = return kappa
    compress kappa@NatK   = return kappa

    compress kappa@(MetaK mkv) = do
        maybe_kappa' <- readKv mkv
        case maybe_kappa' of
          Nothing     ->  return kappa
          Just kappa' ->  do  kappa'' <- compress kappa'
                              writeKv mkv kappa''
                              return kappa''

instance Compress (Type, Kind) where
    compress (alpha, kappa) = (,) <$> pure alpha <*> compress kappa

instance Compress R where
    compress traits@R{} = pure traits

    compress traits@(MetaR mrv) = do
        maybe_traits' <- readRv mrv
        case maybe_traits' of
          Nothing      -> return traits
          Just traits' -> do  traits'' <- compress traits'
                              writeRv mrv traits''
                              return traits''
