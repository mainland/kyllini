{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Simplify
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Simplify (
    SimplStats(..),
    SimplM,
    runSimplM,

    simplProgram
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            modify)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

type InVar    = Var
type InExp    = Exp
type InComp l = Comp l

type OutVar    = Var
type OutExp    = Exp
type OutComp l = Comp l

type Theta l = Map InVar (SubstRng l)

data SubstRng l = SuspExp     (Theta l) InExp
                | SuspFun     (Theta l) [IVar] [(Var, Type)] Type InExp
                | SuspComp    (Theta l) (InComp l)
                | SuspFunComp (Theta l) [IVar] [(Var, Type)] Type (InComp l)
                | DoneExp     OutExp
                | DoneFun     [IVar] [(Var, Type)] Type OutExp
                | DoneComp    (OutComp l)
                | DoneFunComp [IVar] [(Var, Type)] Type (OutComp l)
  deriving (Eq, Ord, Read, Show)

type VarDefs l = Map OutVar (Definition l)

data Definition l = Unknown
                  | BoundToExp     (Maybe OccInfo) Level OutExp
                  | BoundToFun     (Maybe OccInfo) [IVar] [(Var, Type)] Type OutExp
                  | BoundToComp    (Maybe OccInfo) (OutComp l)
                  | BoundToFunComp (Maybe OccInfo) [IVar] [(Var, Type)] Type (OutComp l)
  deriving (Eq, Ord, Read, Show)

data Level = Top | Nested
  deriving (Eq, Ord, Read, Show)

type Phi = Map IVar Iota

type Psi = Map TyVar Type

data SimplStats = SimplStats
    { simplDrop     :: Int
    , simplInline   :: Int
    , simplRewrites :: Int
    }
  deriving (Eq, Ord, Show)

instance Monoid SimplStats where
    mempty =
        SimplStats { simplDrop     = 0
                   , simplInline   = 0
                   , simplRewrites = 0
                   }

    s1 `mappend` s2 =
        SimplStats { simplDrop     = simplDrop s1 + simplDrop s2
                   , simplInline   = simplInline s1 + simplInline s2
                   , simplRewrites = simplRewrites s1 + simplRewrites s2
                   }

data SimplEnv l = SimplEnv
    { simplTheta   :: !(Theta l)
    , simplVarDefs :: !(VarDefs l)
    , simplPhi     :: !Phi
    , simplPsi     :: !Psi
    }

defaultSimplEnv :: SimplEnv l
defaultSimplEnv = SimplEnv mempty mempty mempty mempty

data SimplState = SimplState
    { simplStats :: SimplStats }

defaultSimplState :: SimplState
defaultSimplState = SimplState
    { simplStats = mempty }

newtype SimplM l m a = SimplM { unSimplM :: StateT SimplState (ReaderT (SimplEnv l) m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadReader (SimplEnv l),
              MonadState SimplState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans (SimplM l) where
    lift m = SimplM $ lift $ lift m

runSimplM :: MonadTc m => SimplM l m a -> m (a, SimplStats)
runSimplM m = do
    (x, st) <- runReaderT (runStateT (unSimplM m) defaultSimplState) defaultSimplEnv
    return (x, simplStats st)

mappendStats :: MonadTc m => SimplStats -> SimplM l m ()
mappendStats stats =
    modify $ \s -> s { simplStats = simplStats s <> stats }

dropBinding :: MonadTc m => BoundVar -> SimplM l m ()
dropBinding _ =
    mappendStats mempty { simplDrop = 1 }

inlineBinding :: MonadTc m => Var -> SimplM l m ()
inlineBinding _v =
    mappendStats mempty { simplInline = 1 }

rewrite :: MonadTc m => SimplM l m ()
rewrite =
    mappendStats mempty { simplRewrites = 1 }

askSubst :: MonadTc m => SimplM l m (Theta l)
askSubst = asks simplTheta

lookupSubst :: MonadTc m => InVar -> SimplM l m (Maybe (SubstRng l))
lookupSubst v = asks (Map.lookup v . simplTheta)

killVars :: MonadTc m
         => [InVar]
         -> SimplM l m a
         -> SimplM l m a
killVars vs k =
    local
    (\env -> env { simplTheta = foldl' (flip Map.delete) (simplTheta env) vs }) k

extendSubst :: MonadTc m
            => InVar
            -> SubstRng l
            -> SimplM l m a
            -> SimplM l m a
extendSubst v rng k =
    local (\env -> env { simplTheta = Map.insert v rng (simplTheta env) }) k

withSubst :: MonadTc m
          => Theta l
          -> SimplM l m a
          -> SimplM l m a
withSubst theta k =
    local (\env -> env { simplTheta = theta }) k

isInScope :: MonadTc m
          => InVar
          -> SimplM l m Bool
isInScope v = asks (Map.member v . simplVarDefs)

lookupDefinition :: MonadTc m
                 => InVar
                 -> SimplM l m (Maybe (Definition l))
lookupDefinition v = asks (Map.lookup v . simplVarDefs)

extendDefinitions :: MonadTc m
                  => [(OutVar, Definition l)]
                  -> SimplM l m a
                  -> SimplM l m a
extendDefinitions defs k =
    local (\env -> env { simplVarDefs = foldl' insert (simplVarDefs env) defs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

withUniqVar :: MonadTc m
            => Var
            -> (Var -> SimplM l m a)
            -> SimplM l m a
withUniqVar v k = do
    inscope <- isInScope v
    if inscope
      then do v' <- uniquify v
              extendSubst v ((DoneExp . varE) v') $ k v'
      else killVars [v] $ k v

withUniqVars :: MonadTc m
             => [Var]
             -> ([Var] -> SimplM l m a)
             -> SimplM l m a
withUniqVars [] k =
    k []

withUniqVars (v:vs) k =
    withUniqVar  v  $ \v'  ->
    withUniqVars vs $ \vs' ->
    k (v':vs')

withUniqBoundVar :: MonadTc m
                 => BoundVar
                 -> (BoundVar -> SimplM l m a)
                 -> SimplM l m a
withUniqBoundVar v k = do
    inscope <- isInScope (bVar v)
    if inscope
      then do v' <- uniquify v
              extendSubst (bVar v) ((DoneExp . varE . bVar) v') $ k v'
      else killVars [bVar v] $ k v

askIVarSubst :: MonadTc m => SimplM l m Phi
askIVarSubst = asks simplPhi

extendIVarSubst :: MonadTc m => [(IVar, Iota)] -> SimplM l m a -> SimplM l m a
extendIVarSubst ivs k =
    local (\env -> env { simplPhi = foldl' insert (simplPhi env) ivs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

askTyVarSubst :: MonadTc m => SimplM l m Psi
askTyVarSubst = asks simplPsi

extendTyVarSubst :: MonadTc m
                 => [(TyVar, Type)]
                 -> SimplM l m a
                 -> SimplM l m a
extendTyVarSubst tvs k =
    local (\env -> env { simplPsi = foldl' insert (simplPsi env) tvs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context.
withInstantiatedTyVars :: MonadTc m
                       => Type
                       -> SimplM l m a
                       -> SimplM l m a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarSubst [(alpha, tau) | (TyVarT alpha _, tau) <-
                                       [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

simplProgram :: (IsLabel l, MonadTc m)
             => Program l
             -> SimplM l m (Program l)
simplProgram (Program decls comp tau) = do
  (decls', comp') <-
      simplDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      simplComp comp
  return $ Program decls' comp' tau

simplType :: MonadTc m => Type -> SimplM l m Type
simplType tau = do
    phi <- askTyVarSubst
    psi <- askIVarSubst
    return $ subst psi mempty (subst phi mempty tau)

simplIota :: MonadTc m => Iota -> SimplM l m Iota
simplIota iota = do
    psi <- askIVarSubst
    return $ subst psi mempty iota

simplDecls :: (IsLabel l, MonadTc m)
           => [Decl l]
           -> SimplM l m a
           -> SimplM l m ([Decl l], a)
simplDecls [] m = do
    x <- m
    return ([], x)

simplDecls (d:ds) m = do
    (maybe_d', (ds', x)) <- simplDecl d $ simplDecls ds $ m
    return (maybe ds' (:ds') maybe_d', x)

simplDecl :: forall l m a . (IsLabel l, MonadTc m)
          => Decl l
          -> SimplM l m a
          -> SimplM l m (Maybe (Decl l), a)
simplDecl (LetD decl s) m = do
    (maybe_decl', x) <- simplLocalDecl decl m
    case maybe_decl' of
      Nothing    -> return (Nothing, x)
      Just decl' -> return (Just (LetD decl' s), x)

simplDecl decl m = do
    flags <- askFlags
    preInlineUnconditionally flags decl
  where
    -- | Drop a dead binding and unconditionally inline a binding that occurs only
    -- once.
    preInlineUnconditionally :: Flags -> Decl l -> SimplM l m (Maybe (Decl l), a)
    preInlineUnconditionally _flags (LetD {}) =
        faildoc $ text "preInlineUnconditionally: can't happen"

    preInlineUnconditionally flags decl@(LetFunD f ivs vbs tau_ret e _)
        | isDead = dropBinding f >> withoutBinding m
        | isOnce && testDynFlag MayInlineFun flags = do
              theta <- askSubst
              extendSubst (bVar f) (SuspFun theta ivs vbs tau_ret e) $ do
              dropBinding f
              withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    preInlineUnconditionally flags decl@(LetExtFunD f _ _ _ _)
        | isDead    = dropBinding f >> withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead :: Bool
        isDead = bOccInfo f == Just Dead

    preInlineUnconditionally flags decl@(LetStructD {}) =
        postInlineUnconditionally flags decl

    preInlineUnconditionally flags decl@(LetCompD v _ comp _)
        | isDead = dropBinding v >> withoutBinding m
        | isOnce && testDynFlag MayInlineComp flags = do
              theta <- askSubst
              extendSubst (bVar v) (SuspComp theta comp) $ do
              dropBinding v
              withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo v == Just Dead
        isOnce = bOccInfo v == Just Once

    preInlineUnconditionally flags (LetFunCompD f ivs vbs tau_ret comp _)
        | isDead = dropBinding f >> withoutBinding m
        | isOnce && testDynFlag MayInlineComp flags = do
              theta <- askSubst
              extendSubst (bVar f)
                          (SuspFunComp theta ivs vbs tau_ret comp) $ do
              dropBinding f
              withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    -- | Simplify the right-hand-side of a binding and then see if we want to
    -- inline it unconditionally. If so, add it to the current
    -- substitution. Otherwise, rename it if needed and add it to the current
    -- set of in scope bindings.
    postInlineUnconditionally :: Flags -> Decl l -> SimplM l m (Maybe (Decl l), a)
    postInlineUnconditionally _flags (LetD {}) =
        faildoc $ text "postInlineUnconditionally: can't happen"

    postInlineUnconditionally _flags (LetFunD f ivs vbs tau_ret e l) = do
        (ivs', vbs', tau_ret', e') <-
            extendLetFun f ivs vbs tau_ret $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $ do
            tau_ret' <- simplType tau_ret
            e'       <- simplExp e
            return (ivs, (vs' `zip` taus), tau_ret', e')
        inlineIt <- shouldInlineFunUnconditionally ivs' vbs' tau_ret' e'
        if inlineIt
          then extendSubst (bVar f) (DoneFun ivs' vbs' tau_ret' e') $ do
               dropBinding f
               withoutBinding m
          else withUniqBoundVar f $ \f' ->
               extendVars [(bVar f', tau)] $
               extendDefinitions
                   [(bVar f', BoundToFun (bOccInfo f') ivs' vbs' tau_ret' e')] $
               withBinding (LetFunD f' ivs' vbs' tau_ret' e' l) $
               m
      where
        vs :: [Var]
        taus :: [Type]
        (vs, taus) = unzip vbs

        tau :: Type
        tau = FunT ivs (map snd vbs) tau_ret l

    postInlineUnconditionally _flags (LetExtFunD f iotas vbs tau_ret l) =
        extendExtFuns [(bVar f, tau)] $
        withBinding (LetExtFunD f iotas vbs tau_ret l) $
        m
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    postInlineUnconditionally _flags decl@(LetStructD s flds l) =
        extendStructs [StructDef s flds l] $
        withBinding decl $
        m

    postInlineUnconditionally _flags (LetCompD v tau comp l) = do
        comp' <- extendLet v tau $
                 simplComp comp
        inlineIt <- shouldInlineCompUnconditionally comp'
        if inlineIt
          then extendSubst (bVar v) (DoneComp comp') $ do
               dropBinding v
               withoutBinding m
          else withUniqBoundVar v $ \v' ->
               extendVars [(bVar v', tau)] $
               extendDefinitions [(bVar v', BoundToComp (bOccInfo v') comp')] $
               withBinding (LetCompD v' tau comp' l) $
               m

    postInlineUnconditionally _flags (LetFunCompD f ivs vbs tau_ret comp l) = do
        (ivs', vbs', tau_ret', comp') <-
            extendLetFun f ivs vbs tau_ret $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $ do
            tau_ret' <- simplType tau_ret
            comp'    <- simplComp comp
            return (ivs, (vs' `zip` taus), tau_ret', comp')
        inlineIt <- shouldInlineCompFunUnconditionally ivs' vbs' tau_ret' comp'
        if inlineIt
          then extendSubst (bVar f) (DoneFunComp ivs' vbs' tau_ret' comp') $ do
               dropBinding f
               withoutBinding m
          else withUniqBoundVar f $ \f' ->
               extendVars [(bVar f', tau)] $
               extendDefinitions
                   [(bVar f',
                     BoundToFunComp (bOccInfo f') ivs' vbs' tau_ret' comp')] $
               withBinding (LetFunCompD f' ivs' vbs' tau_ret' comp' l) $
               m
      where
        vs :: [Var]
        taus :: [Type]
        (vs, taus) = unzip vbs

        tau :: Type
        tau = FunT ivs (map snd vbs) tau_ret l

    withoutBinding :: SimplM l m a -> SimplM l m (Maybe (Decl l), a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: Decl l -> SimplM l m a -> SimplM l m (Maybe (Decl l), a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

simplLocalDecl :: forall a l m . (IsLabel l, MonadTc m)
               => LocalDecl
               -> SimplM l m a
               -> SimplM l m (Maybe LocalDecl, a)
simplLocalDecl decl m = do
    flags <- askFlags
    preInlineUnconditionally flags decl
  where
    preInlineUnconditionally :: Flags -> LocalDecl -> SimplM l m (Maybe LocalDecl, a)
    preInlineUnconditionally flags decl@(LetLD v _ e _)
        | isDead = dropBinding v >> withoutBinding m
        | isOnce && not (isArrE e) && testDynFlag MayInlineVal flags = do
              theta <- askSubst
              extendSubst (bVar v) (SuspExp theta e) $ do
              dropBinding v
              withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo v == Just Dead
        isOnce = bOccInfo v == Just Once

    preInlineUnconditionally flags decl@(LetRefLD v _ _ _)
        | isDead    = dropBinding v >> withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead :: Bool
        isDead = bOccInfo v == Just Dead

    postInlineUnconditionally :: Flags -> LocalDecl -> SimplM l m (Maybe LocalDecl, a)
    postInlineUnconditionally _flags (LetLD v tau e s) = do
        e'       <- simplExp e
        tau'     <- simplType tau
        inlineIt <- shouldInlineExpUnconditionally e'
        if inlineIt
          then extendSubst (bVar v) (DoneExp e') $ do
               dropBinding v
               withoutBinding m
          else withUniqBoundVar v $ \v' ->
               extendVars [(bVar v', tau)] $
               extendDefinitions [(bVar v', BoundToExp (bOccInfo v') Top e')] $
               withBinding (LetLD v' tau' e' s) m

    postInlineUnconditionally _flags (LetRefLD v tau e s) = do
        e'   <- traverse simplExp e
        tau' <- simplType tau
        withUniqBoundVar v $ \v' ->
            extendVars [(bVar v', refT tau)] $
            extendDefinitions [(bVar v', Unknown)] $
            withBinding (LetRefLD v' tau' e' s) m

    withoutBinding :: SimplM l m a -> SimplM l m (Maybe LocalDecl, a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: LocalDecl -> SimplM l m a -> SimplM l m (Maybe LocalDecl, a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

simplComp :: (IsLabel l, MonadTc m) => Comp l -> SimplM l m (Comp l)
simplComp (Comp steps) = Comp <$> simplSteps steps

simplSteps :: forall l m . (IsLabel l, MonadTc m)
           => [Step l]
           -> SimplM l m [Step l]
simplSteps [] =
    return []

simplSteps (LetC l decl s : steps) = do
    (maybe_decl', steps') <- withSummaryContext steps $
                             simplLocalDecl decl $
                             simplSteps steps
    case maybe_decl' of
      Nothing    -> return steps'
      Just decl' -> return $ LetC l decl' s : steps'

simplSteps (BindC {} : _) =
    panicdoc $ text "simplSteps: leading BindC"

simplSteps (step : BindC l wv tau s : steps) = do
    step' <- simplStep step
    tau'  <- simplType tau
    go step' tau' wv
  where
    go :: [Step l] -> Type -> WildVar -> SimplM l m [Step l]
    go [step'] tau' (TameV v) | bOccInfo v == Just Dead = do
        dropBinding v
        go [step'] tau' WildV

    go [ReturnC {}] _tau' WildV =
        simplSteps steps

    go [ReturnC l e s] tau' (TameV v) =
        withUniqBoundVar v $ \v' ->
        extendVars [(bVar v', tau)] $
        extendDefinitions [(bVar v', BoundToExp Nothing Nested e)] $ do
        steps' <- simplSteps steps
        return $ LetC l (LetLD v' tau' e s) s : steps'

    go [step'] tau' WildV = do
        steps' <- simplSteps steps
        return $ step' : BindC l WildV tau' s : steps'

    go [step'] tau' (TameV v) =
        withUniqBoundVar v $ \v' ->
        extendVars [(bVar v', tau)] $
        extendDefinitions [(bVar v', Unknown)] $ do
        steps' <- simplSteps steps
        return $ step' : BindC l (TameV v') tau' s : steps'

    go [] _tau' _wv =
        faildoc $ text "simplSteps: can't happen"

    go step' tau' wv = do
        (++) <$> pure hd <*> go [tl] tau' wv
      where
        hd :: [Step l]
        tl :: Step l
        hd = init step'
        tl = last step'

simplSteps (step : steps) = do
    step' <- simplStep step
    (omega, _, _, _) <- inferComp (Comp step') >>= checkST
    case (omega, steps) of
      (C (UnitT {}), [ReturnC _ (ConstE UnitC _) _]) -> rewrite >> return step'
      _ -> (++) <$> pure step' <*> simplSteps steps

{- Note [Inlining Computations]

When we might inline a computation more than once, we must rewrite its labels so
that we don't end up with duplicate labels. We can tell if a computation is only
inlined once, because in that case it will show up in the substitution as a
Susp* form. If that happens, we /do not/ rewrite its labels. For the case where
a computation may be inlined more than once, we use the function
'uniquifyCompLabels' to ensure that all labels in the computation are unique

The extra complication is that there may be references to the label of the
computation, which is either a 'VarC' or a 'CallC', that is subject to
inlining. Therefore, we need to make sure that the inlined computation has the
same initial label as the computation it is replacing. We must then /also/
rewrite the inlined computation so that all references to /its/ initial label
are fixed up. The function 'rewriteStepsLabel' handles replacing the label of
the first step in a computation and rewriting all references to the old
label. Note that we must always perform this operation, even for a computation
that is inlined only once.
-}

simplStep :: forall l m . (IsLabel l, MonadTc m)
          => Step l
          -> SimplM l m [Step l]
simplStep step@(VarC l v _) =
    lookupSubst v >>= go
  where
    go :: Maybe (SubstRng l) -> SimplM l m [Step l]
    go Nothing =
        lookupDefinition v >>= callSiteInline

    go (Just (SuspComp theta comp)) =
        withSubst theta $ do
        inlineBinding v
        unComp <$> simplComp comp >>= rewriteStepsLabel l

    go (Just (DoneComp comp)) =
        inlineCompRhs comp

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "substituted with non-computation."

    callSiteInline :: Maybe (Definition l) -> SimplM l m [Step l]
    callSiteInline maybe_def = do
        flags <- askFlags
        go flags maybe_def
      where
        go :: Flags -> Maybe (Definition l) -> SimplM l m [Step l]
        go flags (Just (BoundToComp occ rhs)) | testDynFlag MayInlineComp flags && inline occ rhs =
            inlineCompRhs rhs

        go _ _ =
            return [step]

    inline :: Maybe OccInfo -> OutComp l -> Bool
    inline _occ _rhs = True

    inlineCompRhs :: Comp l -> SimplM l m [Step l]
    inlineCompRhs comp =
        withSubst mempty $ do
        inlineBinding v
        unComp <$> (simplComp comp >>= uniquifyCompLabels) >>= rewriteStepsLabel l

simplStep (CallC l f0 iotas0 args0 s) = do
    iotas <- mapM simplIota iotas0
    args  <- mapM simplArg args0
    lookupSubst f0 >>= go f0 iotas args
  where
    go :: Var -> [Iota] -> [Arg l] -> Maybe (SubstRng l) -> SimplM l m [Step l]
    go f iotas args Nothing =
        lookupDefinition f >>= callSiteInline f iotas args

    -- This can occur when f was in scope, so it was renamed to f'. We need to
    -- recurse because we may still want to inline the call to f', nee f.
    go _ iotas args (Just (DoneExp (VarE f' _))) =
       lookupSubst f' >>= go f' iotas args

    go _ iotas args (Just (SuspFunComp theta ivs vbs tau_ret comp)) =
        withSubst theta $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $
        withInstantiatedTyVars tau_ret $ do
        inlineBinding f0
        unComp <$> simplComp comp >>= rewriteStepsLabel l

    go _ iotas args (Just (DoneFunComp ivs vbs tau_ret comp)) =
        inlineFunCompRhs iotas args ivs vbs tau_ret comp

    go f _ _ _ =
        faildoc $
        text "Computation function" <+> ppr f <+>
        text "substituted with non-computation function."

    callSiteInline :: Var
                   -> [Iota]
                   -> [Arg l]
                   -> Maybe (Definition l)
                   -> SimplM l m [Step l]
    callSiteInline f iotas args maybe_def = do
        flags <- askFlags
        go flags maybe_def
      where
        go :: Flags -> Maybe (Definition l) -> SimplM l m [Step l]
        go flags (Just (BoundToFunComp _occ ivs vbs tau_ret rhs))
            | testDynFlag MayInlineComp flags =
          inlineFunCompRhs iotas args ivs vbs tau_ret rhs

        go _ _ =
            return1 $ CallC l f iotas args s

    inlineFunCompRhs :: [Iota]
                     -> [Arg l]
                     -> [IVar]
                     -> [(Var, Type)]
                     -> Type
                     -> Comp l
                     -> SimplM l m [Step l]
    inlineFunCompRhs iotas args ivs vbs tau_ret comp =
        withSubst mempty $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $
        withInstantiatedTyVars tau_ret $ do
        inlineBinding f0
        unComp <$> (simplComp comp >>= uniquifyCompLabels) >>= rewriteStepsLabel l

    simplArg :: Arg l -> SimplM l m (Arg l)
    simplArg (ExpA e)  = ExpA  <$> simplExp e
    simplArg (CompA c) = CompA <$> simplComp c

    extendArgs :: [(Var, Arg l)] -> SimplM l m a -> SimplM l m a
    extendArgs []                   k = k
    extendArgs ((v, ExpA e):vargs)  k = extendSubst v (DoneExp e)  $
                                        extendArgs vargs k
    extendArgs ((v, CompA c):vargs) k = extendSubst v (DoneComp c) $
                                        extendArgs vargs k

simplStep (IfC l e1 c2 c3 s) = do
    e1' <- simplExp e1
    c2' <- simplComp c2
    c3' <- simplComp c3
    simplIf e1' c2' c3'
  where
    simplIf :: Exp -> Comp l -> Comp l -> SimplM l m [Step l]
    simplIf e1' c2' c3'
        | isTrue e1'  = return $ unComp c2'
        | isFalse e1' = return $ unComp c3'
        | otherwise   = return1 $ IfC l e1' c2' c3' s

simplStep (LetC {}) =
    faildoc $ text "Cannot occ let step."

simplStep (WhileC l e c s) = do
    WhileC l <$> simplExp e <*> simplComp c <*> pure s >>= return1

simplStep (ForC l ann v tau e1 e2 c s) = do
    e1' <- simplExp e1
    e2' <- simplExp e2
    extendVars [(v, tau)] $
        withUniqVar v $ \v' ->
        extendVars [(v', tau)] $
        extendDefinitions [(v', Unknown)] $ do
        c' <- simplComp c
        return1 $ ForC l ann v' tau e1' e2' c' s

simplStep (LiftC l e s) =
    LiftC l <$> simplExp e <*> pure s >>= return1

simplStep (ReturnC l e s) =
    ReturnC l <$> simplExp e <*> pure s >>= return1

simplStep (BindC {}) =
    faildoc $ text "Cannot occ bind step."

simplStep (TakeC l tau s) = do
    tau' <- simplType tau
    return1 $ TakeC l tau' s

simplStep (TakesC l n tau s) = do
    tau' <- simplType tau
    return1 $ TakesC l n tau' s

simplStep (EmitC l e s) =
    EmitC l <$> simplExp e <*> pure s >>= return1

simplStep (EmitsC l e s) =
    EmitsC l <$> simplExp e <*> pure s >>= return1

simplStep (RepeatC l ann c s) =
    RepeatC l ann <$> simplComp c <*> pure s >>= return1

simplStep (ParC ann b c1 c2 sloc) = do
    (s, a, c) <- askSTIndTypes
    c1'       <- withFvContext c1 $
                 localSTIndTypes (Just (s, a, b)) $
                 simplComp c1
    c2'       <- withFvContext c2 $
                 localSTIndTypes (Just (b, b, c)) $
                 simplComp c2
    return1 $ ParC ann b c1' c2' sloc

simplStep (LoopC {}) =
    faildoc $ text "simplStep: saw LoopC"

simplExp :: forall l m . (IsLabel l, MonadTc m)
         => Exp
         -> SimplM l m Exp
simplExp e@(ConstE {}) =
    return e

simplExp e0@(VarE v _) =
    lookupSubst v >>= go
  where
    go :: Maybe (SubstRng l) -> SimplM l m Exp
    go Nothing =
        lookupDefinition v >>= callSiteInline

    go (Just (SuspExp theta e)) =
        withSubst theta $ do
        inlineBinding v
        simplExp e

    go (Just (DoneExp e)) =
        inlineRhs e

    -- The variable may be bound to a pureish computation, in which case we need
    -- to convert it back to an expression...ugh. See #13.
    go (Just (SuspComp theta c)) = do
        e <- compToExp c
        go (Just (SuspExp theta e))

    go (Just (DoneComp c)) = do
        e <- compToExp c
        go (Just (DoneExp e))

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "substituted with non-expression."

    callSiteInline :: Maybe (Definition l) -> SimplM l m Exp
    callSiteInline maybe_def = do
        flags <- askFlags
        go flags maybe_def
      where
        go :: Flags -> Maybe (Definition l) -> SimplM l m Exp
        go flags (Just (BoundToExp occ lvl rhs)) | testDynFlag MayInlineVal flags && inline rhs occ lvl =
            inlineRhs rhs

        go _ _ =
            return e0

    inline :: OutExp -> Maybe OccInfo -> Level -> Bool
    inline _rhs Nothing            _lvl = False
    inline _rhs (Just Dead)        _lvl = error "inline: saw Dead binding"
    inline rhs (Just Once)         _lvl
        | isArrE rhs                    = False
        | otherwise                     = error "inline: saw Once binding"
    inline _rhs (Just OnceInFun)   _lvl = False
    inline _rhs (Just ManyBranch)  _lvl = False
    inline _rhs (Just Many)        _lvl = False

    inlineRhs :: Exp -> SimplM l m Exp
    inlineRhs rhs =
        withSubst mempty $ do
        inlineBinding v
        simplExp rhs

simplExp (UnopE op e s) = do
    e' <- simplExp e
    simplUnop op e'
  where
    simplUnop :: Unop -> Exp -> SimplM l m Exp
    simplUnop Neg e' = return $ negate e'
    simplUnop op  e' = return $ UnopE op e' s

simplExp (BinopE op e1 e2 s) = do
    e1' <- simplExp e1
    e2' <- simplExp e2
    simplBinop op e1' e2'
  where
    simplBinop :: Binop -> Exp -> Exp -> SimplM l m Exp
    simplBinop Add e1' e2' = return $ e1' + e2'
    simplBinop Sub e1' e2' = return $ e1' - e2'
    simplBinop Mul e1' e2' = return $ e1' * e2'
    simplBinop op  e1' e2' = return $ BinopE op e1' e2' s

simplExp (IfE e1 e2 e3 s) = do
    e1' <- simplExp e1
    e2' <- simplExp e2
    e3' <- simplExp e3
    simplIf e1' e2' e3'
  where
    simplIf :: Exp -> Exp -> Exp -> SimplM l m Exp
    simplIf e1' e2' e3'
        | isTrue e1'  = return e2'
        | isFalse e1' = return e3'
        | otherwise   = return $ IfE e1' e2' e3' s

simplExp (LetE decl e s) = do
    (maybe_decl', e') <- simplLocalDecl decl $ simplExp e
    case maybe_decl' of
      Nothing    -> return e'
      Just decl' -> return $ LetE decl' e' s

simplExp (CallE f0 iotas0 es0 s) = do
    iotas <- mapM simplIota iotas0
    es    <- mapM simplExp es0
    lookupSubst f0 >>= go f0 iotas es
  where
    go :: Var -> [Iota] -> [Exp] -> Maybe (SubstRng l) -> SimplM l m Exp
    go f iotas args Nothing =
        lookupDefinition f >>= callSiteInline f iotas args

    -- This can occur when f was in scope, so it was renamed to f'. We need to
    -- recurse because we may still want to inline the call to f', nee f.
    go _ iotas args (Just (DoneExp (VarE f' _))) =
       lookupSubst f' >>= go f' iotas args

    go _ iotas args (Just (SuspFun theta ivs vbs _tau_ret e)) =
        withSubst theta $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $ do
        inlineBinding f0
        simplExp e

    go _ iotas args (Just (DoneFun ivs vbs tau_ret rhs)) =
        inlineFunRhs iotas args ivs vbs tau_ret rhs

    go f _ _ _ =
        faildoc $
        text "Function" <+> ppr f <+>
        text "substituted with non-function."

    callSiteInline :: Var
                   -> [Iota]
                   -> [Exp]
                   -> Maybe (Definition l)
                   -> SimplM l m Exp
    callSiteInline f iotas args maybe_def = do
        flags <- askFlags
        go flags maybe_def
      where
        go :: Flags -> Maybe (Definition l) -> SimplM l m Exp
        go flags (Just (BoundToFun _occ ivs vbs tau_ret rhs))
            | testDynFlag MayInlineFun flags =
          inlineFunRhs iotas args ivs vbs tau_ret rhs

        go _ _ =
            return $ CallE f iotas args s

    inlineFunRhs :: [Iota]
                 -> [Exp]
                 -> [IVar]
                 -> [(Var, Type)]
                 -> Type
                 -> Exp
                 -> SimplM l m Exp
    inlineFunRhs iotas args ivs vbs _tau_ret e =
        withSubst mempty $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $ do
        inlineBinding f0
        simplExp e

    extendArgs :: [(Var, Exp)] -> SimplM l m a -> SimplM l m a
    extendArgs []             k = k
    extendArgs ((v, e):vargs) k = extendSubst v (DoneExp e) $
                                  extendArgs vargs k

simplExp (DerefE e s) =
    DerefE <$> simplExp e <*> pure s

simplExp (AssignE e1 e2 s) =
    AssignE <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (WhileE e1 e2 s) =
    WhileE <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (ForE ann v tau e1 e2 e3 s) = do
    e1' <- simplExp e1
    e2' <- simplExp e2
    extendVars [(v, tau)] $
        withUniqVar v $ \v' ->
        extendVars [(v', tau)] $
        extendDefinitions [(v', Unknown)] $ do
        e3' <- simplExp e3
        return $ ForE ann v' tau e1' e2' e3' s

simplExp (ArrayE es s) =
    ArrayE <$> mapM simplExp es <*> pure s

simplExp (IdxE e1 e2 len s) =
    IdxE <$> simplExp e1 <*> simplExp e2 <*> pure len <*> pure s

simplExp (StructE struct flds s) =
    StructE struct <$> (zip (map fst flds) <$> mapM (simplExp . snd) flds)
                   <*> pure s

simplExp (ProjE e f s) =
    ProjE <$> simplExp e <*> pure f <*> pure s

simplExp (PrintE nl es s) =
    PrintE nl <$> mapM simplExp es <*> pure s

simplExp e@(ErrorE {}) =
    return e

simplExp (ReturnE ann e s) =
    ReturnE ann <$> simplExp e <*> pure s

simplExp (BindE wv tau e1 e2 s) = do
    e1'  <- simplExp e1
    tau' <- simplType tau
    go e1' tau' wv
  where
    go :: Exp -> Type -> WildVar -> SimplM l m Exp
    go e tau' (TameV v) | bOccInfo v == Just Dead = do
        dropBinding v
        go e tau' WildV

    go (ReturnE {}) _tau' WildV =
        simplExp e2

    go (ReturnE _ e1' _) tau' (TameV v) = do
        decl <- withUniqBoundVar v $ \v' ->
                extendVars [(bVar v', tau)] $
                extendDefinitions [(bVar v', BoundToExp Nothing Nested e1')] $
                return $ LetLD v' tau' e1' s
        e2'  <- simplExp e2
        return $ LetE decl e2' s

    go e1' tau' WildV = do
        e2' <- simplExp e2
        return $ BindE WildV tau' e1' e2' s

    go e1' tau' (TameV v) =
       withUniqBoundVar v $ \v' ->
       extendVars [(bVar v', tau)] $
       extendDefinitions [(bVar v', Unknown)] $ do
       e2' <- simplExp e2
       return $ BindE wv tau' e1' e2' s

simplExp (LutE e) =
    LutE <$> simplExp e

isTrue :: Exp -> Bool
isTrue (ConstE (BoolC True) _) = True
isTrue _                       = False

isFalse :: Exp -> Bool
isFalse (ConstE (BoolC False) _) = True
isFalse _                        = False

return1 :: Monad m => a -> m [a]
return1 x = return [x]

isSimple :: Exp -> Bool
isSimple (ConstE {}) = True
isSimple (VarE {})   = True
isSimple _           = False

shouldInlineExpUnconditionally :: MonadTc m
                               => InExp -> SimplM l m Bool
shouldInlineExpUnconditionally e | isSimple e =
    asksFlags (testDynFlag MayInlineVal)

shouldInlineExpUnconditionally _ =
    return False

shouldInlineFunUnconditionally :: MonadTc m
                               => [IVar]
                               -> [(Var, Type)]
                               -> Type
                               -> OutExp
                               -> SimplM l m Bool
shouldInlineFunUnconditionally _ _ _ e | isSimple e =
    asksFlags (testDynFlag MayInlineFun)

shouldInlineFunUnconditionally _ _ _ _ =
    return False

shouldInlineCompUnconditionally :: MonadTc m
                                => InComp l -> SimplM l m Bool
shouldInlineCompUnconditionally _ =
    asksFlags (testDynFlag AlwaysInlineComp)

shouldInlineCompFunUnconditionally :: MonadTc m
                                   => [IVar]
                                   -> [(Var, Type)]
                                   -> Type
                                   -> OutComp l
                                   -> SimplM l m Bool
shouldInlineCompFunUnconditionally _ _ _ _ =
    asksFlags (testDynFlag AlwaysInlineComp)
