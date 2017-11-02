{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Simplify
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Simplify (
    SimplStats(..),

    simplProgram,
    simplComp
  ) where

import Prelude hiding ((<=))
import qualified Prelude

import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State.Strict (MonadState(..),
                                   StateT(..),
                                   modify)
import Data.Bits
import Data.List (foldl')
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Occ
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Label
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

type InVar    = Var
type InExp    = Exp
type InComp l = Comp l

type OutVar    = Var
type OutExp    = Exp
type OutComp l = Comp l

type Theta l = Map InVar (SubstRng l)

data SubstRng l = SuspExp     (Theta l) InExp
                | SuspFun     (Theta l) [Tvk] [(Var, Type)] Type InExp
                | SuspComp    (Theta l) (InComp l)
                | SuspFunComp (Theta l) [Tvk] [(Var, Type)] Type (InComp l)
                | DoneExp     OutExp
                | DoneFun     [Tvk] [(Var, Type)] Type OutExp
                | DoneComp    (OutComp l)
                | DoneFunComp [Tvk] [(Var, Type)] Type (OutComp l)
  deriving (Eq, Ord, Read, Show)

type VarDefs l = Map OutVar (Definition l)

data Definition l = Unknown
                  | BoundToExp     (Maybe OccInfo) Level OutExp
                  | BoundToFun     (Maybe OccInfo) [Tvk] [(Var, Type)] Type OutExp
                  | BoundToComp    (Maybe OccInfo) (OutComp l)
                  | BoundToFunComp (Maybe OccInfo) [Tvk] [(Var, Type)] Type (OutComp l)
  deriving (Eq, Ord, Read, Show)

data Level = Top | Nested
  deriving (Eq, Ord, Read, Show)

data SimplStats = SimplStats
    { simplDrop     :: {-# UNPACK #-} !Int
    , simplInline   :: {-# UNPACK #-} !Int
    , simplRewrites :: {-# UNPACK #-} !Int
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
    { simplOccInfo :: !(Map Var OccInfo)
    , simplTheta   :: !(Theta l)
    , simplVarDefs :: !(VarDefs l)
    , simplRefDrop :: !(Set Var)
    }

defaultSimplEnv :: SimplEnv l
defaultSimplEnv = SimplEnv
    { simplOccInfo = mempty
    , simplTheta   = mempty
    , simplVarDefs = mempty
    , simplRefDrop = mempty
    }

data SimplState = SimplState
    { simplStats :: {-# UNPACK #-} !SimplStats }

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
              MonadConfig,
              MonadPlatform,
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

extendOccInfo :: MonadTc m => BoundVar -> SimplM l m a -> SimplM l m a
extendOccInfo BoundV{bVar=v, bOccInfo=Just occ} =
    local $ \env -> env { simplOccInfo = Map.insert v occ (simplOccInfo env) }

extendOccInfo _ = id

lookupOccInfo :: MonadTc m => Var -> SimplM l m (Maybe OccInfo)
lookupOccInfo v = asks (Map.lookup v . simplOccInfo)

askSubst :: MonadTc m => SimplM l m (Theta l)
askSubst = asks simplTheta

lookupSubst :: MonadTc m => InVar -> SimplM l m (Maybe (SubstRng l))
lookupSubst v = asks (Map.lookup v . simplTheta)

killVars :: MonadTc m
         => [InVar]
         -> SimplM l m a
         -> SimplM l m a
killVars vs =
    local $ \env ->
      env { simplTheta = foldl' (flip Map.delete) (simplTheta env) vs }

extendSubst :: MonadTc m
            => InVar
            -> SubstRng l
            -> SimplM l m a
            -> SimplM l m a
extendSubst v rng =
    local $ \env -> env { simplTheta = Map.insert v rng (simplTheta env) }

extendSubsts :: MonadTc m
             => [(InVar, SubstRng l)]
             -> SimplM l m a
             -> SimplM l m a
extendSubsts vrngs =
    local $ \env ->
      env { simplTheta = Map.fromList vrngs `Map.union` simplTheta env }

withSubst :: MonadTc m
          => Theta l
          -> SimplM l m a
          -> SimplM l m a
withSubst theta =
    local $ \env -> env { simplTheta = theta }

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
extendDefinitions defs =
    local $ \env ->
      env { simplVarDefs = foldl' insert (simplVarDefs env) defs }
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

dropRef :: MonadTc m => Var -> SimplM l m a -> SimplM l m a
dropRef v =
    local $ \env -> env { simplRefDrop = Set.insert v (simplRefDrop env) }

keepRef :: MonadTc m => Var -> SimplM l m a -> SimplM l m a
keepRef v =
    local $ \env -> env { simplRefDrop = Set.delete v (simplRefDrop env) }

isDroppedRef :: MonadTc m => Var -> SimplM l m Bool
isDroppedRef v = asks (Set.member v . simplRefDrop)

simplProgram :: (IsLabel l, MonadTc m)
             => Program l
             -> m (Program l, SimplStats)
simplProgram (Program imports decls main) = runSimplM $ do
    (decls', main') <- simplDecls decls $
                       traverse simplMain main
    return $ Program imports decls' main'

simplMain :: (IsLabel l, MonadTc m)
          => Main l
          -> SimplM l m (Main l)
simplMain (Main comp tau) = do
    comp' <- inSTScope tau $
             inLocalScope $
             withLocContext comp (text "In definition of main") $
             simplC comp
    return $ Main comp' tau

simplComp :: forall l m . (IsLabel l, MonadTc m)
          => Comp l
          -> m (Comp l)
simplComp c = do
    n <- asksConfig maxSimpl
    go 0 n c
  where
    go :: Int -> Int -> Comp l -> m (Comp l)
    go i n c | i >= n =
        return c

    go i n c = do
        (c', stats) <- occComp c >>= runSimplM . simplC
        if stats /= mempty
          then go (i+1) n c'
          else return c

simplDecls :: (IsLabel l, MonadTc m)
           => [Decl l]
           -> SimplM l m a
           -> SimplM l m ([Decl l], a)
simplDecls [] m = do
    x <- m
    return ([], x)

simplDecls (d:ds) m = do
    (maybe_d', (ds', x)) <- simplDecl d $ simplDecls ds m
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
    flags <- askConfig
    preInlineUnconditionally flags decl
  where
    -- | Drop a dead binding and unconditionally inline a binding that occurs only
    -- once.
    preInlineUnconditionally :: Config -> Decl l -> SimplM l m (Maybe (Decl l), a)
    preInlineUnconditionally flags decl@StructD{} =
        postInlineUnconditionally flags decl

    preInlineUnconditionally _flags LetD{} =
        faildoc $ text "preInlineUnconditionally: can't happen"

    preInlineUnconditionally flags decl@(LetFunD f tvks vbs tau_ret e _)
        | isDead = dropBinding f >> withoutBinding m
        | isOnce && testDynFlag MayInlineFun flags = do
              theta <- askSubst
              extendSubst (bVar f) (SuspFun theta tvks vbs tau_ret e) $ do
                dropBinding f
                withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    preInlineUnconditionally flags decl@(LetExtFunD f _ _ _ _)
        | isDead    = dropBinding f >> withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead = bOccInfo f == Just Dead

    preInlineUnconditionally flags decl@(LetCompD v _ comp _)
        | isDead = dropBinding v >> withoutBinding m
        | isOnce && testDynFlag MayInlineComp flags = do
              theta <- askSubst
              extendSubst (bVar v) (SuspComp theta comp) $ do
                dropBinding v
                withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead = bOccInfo v == Just Dead
        isOnce = bOccInfo v == Just Once

    preInlineUnconditionally flags (LetFunCompD f tvks vbs tau_ret comp _)
        | isDead = dropBinding f >> withoutBinding m
        | isOnce && testDynFlag MayInlineComp flags = do
              theta <- askSubst
              extendSubst (bVar f)
                          (SuspFunComp theta tvks vbs tau_ret comp) $ do
                dropBinding f
                withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    -- | Simplify the right-hand-side of a binding and then see if we want to
    -- inline it unconditionally. If so, add it to the current
    -- substitution. Otherwise, rename it if needed and add it to the current
    -- set of in scope bindings.
    postInlineUnconditionally :: Config -> Decl l -> SimplM l m (Maybe (Decl l), a)
    postInlineUnconditionally _flags decl@(StructD s taus flds l) =
        extendStructs [StructDef s taus flds l] $
        withBinding decl m

    postInlineUnconditionally _flags LetD{} =
        faildoc $ text "postInlineUnconditionally: can't happen"

    postInlineUnconditionally _flags (LetFunD f tvks vbs tau_ret e l) = do
        (tvks', vbs', tau_ret', e') <-
            extendLetFun f tvks vbs tau_ret $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $ do
            tau_ret' <- simplType tau_ret
            e'       <- simplE e
            return (tvks, vs' `zip` taus, tau_ret', e')
        inlineIt <- shouldInlineFunUnconditionally tvks' vbs' tau_ret' e'
        if inlineIt
          then extendSubst (bVar f) (DoneFun tvks' vbs' tau_ret' e') $ do
               dropBinding f
               withoutBinding m
          else withUniqBoundVar f $ \f' ->
               extendVars [(bVar f', tau)] $
               extendDefinitions
                   [(bVar f', BoundToFun (bOccInfo f') tvks' vbs' tau_ret' e')] $
               withBinding (LetFunD f' tvks' vbs' tau_ret' e' l) m
      where
        (vs, taus) = unzip vbs
        tau        = funT tvks (map snd vbs) tau_ret l

    postInlineUnconditionally _flags (LetExtFunD f tvks vbs tau_ret l) =
        extendExtFuns [(bVar f, tau)] $
        withBinding (LetExtFunD f tvks vbs tau_ret l) m
      where
        tau = funT tvks (map snd vbs) tau_ret l

    postInlineUnconditionally _flags (LetCompD v tau comp l) = do
        comp' <- extendLet v tau $
                 simplC comp
        inlineIt <- shouldInlineCompUnconditionally comp'
        if inlineIt
          then extendSubst (bVar v) (DoneComp comp') $ do
               dropBinding v
               withoutBinding m
          else withUniqBoundVar v $ \v' ->
               extendVars [(bVar v', tau)] $
               extendDefinitions [(bVar v', BoundToComp (bOccInfo v') comp')] $
               withBinding (LetCompD v' tau comp' l) m

    postInlineUnconditionally _flags (LetFunCompD f tvks vbs tau_ret comp l) = do
        (tvks', vbs', tau_ret', comp') <-
            extendLetFun f tvks vbs tau_ret $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $ do
            tau_ret' <- simplType tau_ret
            comp'    <- simplC comp
            return (tvks, vs' `zip` taus, tau_ret', comp')
        inlineIt <- shouldInlineCompFunUnconditionally tvks' vbs' tau_ret' comp'
        if inlineIt
          then extendSubst (bVar f) (DoneFunComp tvks' vbs' tau_ret' comp') $ do
               dropBinding f
               withoutBinding m
          else withUniqBoundVar f $ \f' ->
               extendVars [(bVar f', tau)] $
               extendDefinitions
                   [(bVar f',
                     BoundToFunComp (bOccInfo f') tvks' vbs' tau_ret' comp')] $
               withBinding (LetFunCompD f' tvks' vbs' tau_ret' comp' l) m
      where
        vs :: [Var]
        taus :: [Type]
        (vs, taus) = unzip vbs

        tau :: Type
        tau = funT tvks (map snd vbs) tau_ret l

    withoutBinding :: SimplM l m a -> SimplM l m (Maybe (Decl l), a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: Decl l -> SimplM l m a -> SimplM l m (Maybe (Decl l), a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

simplLocalDecl :: forall a l m . (IsLabel l, MonadTc m)
               => LocalDecl
               -> SimplM l m a
               -> SimplM l m (Maybe LocalDecl, a)
simplLocalDecl decl m = do
    flags <- askConfig
    preInlineUnconditionally flags decl
  where
    preInlineUnconditionally :: Config -> LocalDecl -> SimplM l m (Maybe LocalDecl, a)
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
        | isDead    = do dropBinding v
                         dropRef (bVar v) $ withoutBinding m
        | otherwise = postInlineUnconditionally flags decl
      where
        isDead :: Bool
        isDead = bOccInfo v == Just Dead

    preInlineUnconditionally flags decl@LetTypeLD{} =
        postInlineUnconditionally flags decl

    preInlineUnconditionally _flags LetViewLD{} =
        faildoc $ text "Views not supported"

    postInlineUnconditionally :: Config -> LocalDecl -> SimplM l m (Maybe LocalDecl, a)
    postInlineUnconditionally _flags (LetLD v tau e s) = do
        e'       <- simplE e
        tau'     <- simplType tau
        inlineIt <- shouldInlineExpUnconditionally e'
        if inlineIt
          then extendSubst (bVar v) (DoneExp e') $ do
               dropBinding v
               withoutBinding m
          else withUniqBoundVar v $ \v' ->
               extendVars [(bVar v', tau)] $
               extendOccInfo v' $
               extendDefinitions [(bVar v', BoundToExp (bOccInfo v') Top e')] $
               withBinding (LetLD v' tau' e' s) m

    postInlineUnconditionally _flags (LetRefLD v tau e s) = do
        e'   <- traverse simplE e
        tau' <- simplType tau
        withUniqBoundVar v $ \v' ->
            extendDefinitions [(bVar v', Unknown)] $
            keepRef (bVar v) $
            withRefBinding v' tau' e' s m

    postInlineUnconditionally _flags (LetTypeLD alpha kappa tau s) = do
        tau' <- simplType tau
        extendTyVars [(alpha, kappa)] $
          extendTyVarTypes [(alpha, tau')] $
          withBinding (LetTypeLD alpha kappa tau' s) m

    postInlineUnconditionally _flags LetViewLD{} =
        faildoc $ text "Views not supported"

    withoutBinding :: SimplM l m a -> SimplM l m (Maybe LocalDecl, a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: LocalDecl -> SimplM l m a -> SimplM l m (Maybe LocalDecl, a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

    withRefBinding :: BoundVar
                   -> Type
                   -> Maybe Exp
                   -> SrcLoc
                   -> SimplM l m a
                   -> SimplM l m (Maybe LocalDecl, a)
    withRefBinding v tau maybe_e s m | Just True <- bStaticRef v = do
        rewrite
        e <- maybe (constE <$> defaultValueC tau) return maybe_e
        extendVars [(bVar v, tau)] $
          extendOccInfo v $
          (,) <$> pure (Just (LetLD v tau e s)) <*> m

    withRefBinding v tau e s m =
        extendVars [(bVar v, refT tau)] $
        extendOccInfo v $
        (,) <$> pure (Just (LetRefLD v tau e s)) <*> m

simplC :: (IsLabel l, MonadTc m) => Comp l -> SimplM l m (Comp l)
simplC comp = do
    steps' <- simplSteps (unComp comp)
    return comp{ unComp = steps' }

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
      Just decl' -> simplLift $ LetC l decl' s : steps'

simplSteps (BindC {} : _) =
    panicdoc $ text "simplSteps: leading BindC"

--
-- Move lift past take(s)
--
-- { lift e; x <- take; ... } -> { x <- take; lift e; ... }
--
simplSteps (s1@LiftC{} : s2 : s3@BindC{} : steps) | isTake s2 =
    simplSteps (s2:s3:s1:steps)
  where
    isTake :: Step l -> Bool
    isTake TakeC{}  = True
    isTake TakesC{} = True
    isTake _        = False

--
-- Coalesce multiples sequential TakesC
--
-- { xs <- takes n; ys <- takes m; ... } ->
-- { zs <- takes (n+m); ... [xs -> zs[0:n]; ys -> zs[n:m]] }
--
simplSteps steps@(TakesC l1 _ tau s1 : BindC l2 TameV{} _ s2 :
                  TakesC{}           : BindC _  TameV{} _ _  :
                  _) = do
    zs <- gensym "zs"
    extendVars [(zs, arrT total tau)] $
      extendSubsts [(v, DoneExp e) | (v, i, n) <- zip3 vs offs lens,
                                     let e = IdxE (varE zs) (intE i) (Just n) (srclocOf n)] $ do
      steps' <- simplSteps rest
      simplSteps $ TakesC l1 total tau s1 :
                   BindC l2 (TameV (mkBoundVar zs)) (arrT total tau) s2 :
                   steps'
  where
    vs :: [Var]
    lens :: [Nat]
    offs :: [Nat]
    total :: Nat
    (vs, lens) = unzip takes
    offs = scanl (+) 0 lens
    total = last offs

    takes :: [(Var, Nat)]
    rest :: [Step l]
    (takes, rest) = go [] steps

    go :: [(Var, Nat)] -> [Step l] -> ([(Var, Nat)], [Step l])
    go takes (TakesC _ n _ _ : BindC _ (TameV xs) _ _ : steps) =
      go ((bVar xs, n) : takes) steps

    go takes steps =
      (reverse takes, steps)

--
-- Coalesce multiple sequential EmitsC
--
-- { emits x[i,n]; emits x[i+n,m]; ... } ->
-- { emits x[i,n+m]] }
--
simplSteps (EmitsC l1 (IdxE (VarE v  _) ei len1 s1) s2 :
            EmitsC _  (IdxE (VarE v' _) ej len2 _)   _ :
            steps)
  | v' == v,
    Just i <- fromIntE ei,
    Just j <- fromIntE ej,
    j == i + sliceLen len1 = do
      rewrite
      simplSteps $ EmitsC l1 (IdxE (varE v) ei (fmap fromIntegral len') s1) s2 : steps
  where
    len' :: Maybe Int
    len' = Just $ sliceLen len1 + sliceLen len2

--
-- Convert assignment followed by dereference and emit(s) to an emit(s)
--
--   { x <- lift { y := e; !y }; emit(s) x; ... }
--   ->
--   { x <- lift { y := e; !y }; emit(s) e; ... }
--
--
simplSteps (LiftC l1 e1 s1 : BindC l2 (TameV v) tau s2 : EmitsC l3 e2 s3 : steps)
  | Just (_, rhs)  <- unAssignBangE e1
  , VarE v' _ <- e2
  , v' == bVar v = do
    rewrite
    simplSteps (LiftC l1 e1 s1 : BindC l2 (TameV v) tau s2 : EmitsC l3 rhs s3 : steps)

simplSteps (LiftC l1 e1 s1 : BindC l2 (TameV v) tau s2 : EmitC l3 e2 s3 : steps)
  | Just (_, rhs)  <- unAssignBangE e1
  , VarE v' _ <- e2
  , v' == bVar v = do
    rewrite
    simplSteps (LiftC l1 e1 s1 : BindC l2 (TameV v) tau s2 : EmitC l3 rhs s3 : steps)

--
-- Drop dead dereferences
--
--   { lift { y := e; !y }; ... }
--   ->
--   { lift { y := e }; ... }
--
--
simplSteps (LiftC l1 e1 s1 : BindC l2 WildV _tau s2 : steps)
  | Just (x, rhs) <- unAssignBangE e1 = do
    rewrite
    simplSteps (LiftC l1 (assignE (varE x) rhs) s1 : BindC l2 WildV unitT s2 : steps)

simplSteps (step : BindC l wv tau s : steps) = do
    step' <- simplStep step
    tau'  <- simplType tau
    go step' tau' wv
  where
    go :: [Step l] -> Type -> WildVar -> SimplM l m [Step l]
    --
    -- Drop an unbound return, e.g.,
    --
    --   { return e1; ... } -> { ... }
    --
    go [ReturnC {}] _tau' WildV = do
        rewrite
        simplSteps steps

    --
    -- Default computation sequencing
    --
    go [step'] tau' WildV = do
        steps' <- simplSteps steps
        simplLift $ step' : BindC l WildV tau' s : steps'

    --
    -- Drop unused bindings. The step whose result is bound might have an
    -- effect, so we can't just throw it away.
    --
    go [step'] tau' (TameV v) | bOccInfo v == Just Dead = do
        dropBinding v
        go [step'] tau' WildV

    --
    -- Convert a bind-return into a let, e.g.,
    --
    --   { x <- return e1; ... } -> { let x = e1; ... }
    --
    go [ReturnC l e s] tau' (TameV v) =
        withUniqBoundVar v $ \v' ->
        extendVars [(bVar v', tau)] $
        extendDefinitions [(bVar v', BoundToExp Nothing Nested e)] $ do
        steps' <- simplSteps steps
        rewrite
        simplLift $ LetC l (LetLD v' tau' e s) s : steps'

    --
    -- Default computation bind
    --
    go [step'] tau' (TameV v) =
        withUniqBoundVar v $ \v' ->
        extendVars [(bVar v', tau)] $
        extendDefinitions [(bVar v', Unknown)] $ do
        steps' <- simplSteps steps
        simplLift $ step' : BindC l (TameV v') tau' s : steps'

    --
    -- Can't happen---simplifying a step has to yield one or more steps
    --
    go [] _tau' _wv =
        faildoc $ text "simplSteps: can't happen"

    --
    -- When simplifying a steps yields more than one step, simplify the
    -- resulting sequence. A single step can simplify to many steps if we inline
    -- a computation.
    --
    go step' tau' wv =
        (++) <$> pure hd <*> go [tl] tau' wv >>= simplLift
      where
        hd :: [Step l]
        tl :: Step l
        hd = init step'
        tl = last step'

--
-- Drop an unbound return; we know the return isn't bound becasue it isn't the
-- final step and we didn't match the bind case just above.
simplSteps (ReturnC{} : steps@(_:_)) = do
    rewrite
    simplSteps steps

simplSteps [step1, step2@(ReturnC _ (ConstE UnitC _) _)] = do
    step1' <- simplStep step1
    (omega, _, _, _) <- inferComp (mkComp step1') >>= checkST
    case omega of
      C UnitT{} -> do rewrite
                      simplLift step1'
      _         -> simplLift $ step1' ++ [step2]

simplSteps (step : steps) =
    (++) <$> simplStep step <*> simplSteps steps >>= simplLift

-- Pull apart expressions of the form
--
--    { x := e; !x }
--
unAssignBangE :: Exp -> Maybe (Var, Exp)
unAssignBangE (BindE _ _ (AssignE (VarE v _) e _) (DerefE (VarE v' _) _) _) | v' == v =
    Just (v, e)

unAssignBangE _ =
    Nothing

-- | Return 'True' if the binders of @x@ are used in @y@, 'False' otherwise.
notUsedIn :: (Binders a Var, Fvs b Var) => a -> b -> Bool
notUsedIn x y = Set.null (vs1 `Set.intersection` vs2)
  where
    vs1 :: Set Var
    vs1 = binders x

    vs2 :: Set Var
    vs2 = fvs y

-- | Coalesce lifted expressions whenever possible. This is critical for the
-- auto-LUTter. The argument to 'simplLift' should already have been simplified;
-- we assume that the tail of the argument has already been through 'simplLift',
-- which is the case as it is currently used in 'simplSteps'
simplLift :: forall l m . (IsLabel l, MonadTc m)
          => [Step l]
          -> SimplM l m [Step l]
simplLift (IfC l e1 Comp{unComp=[LiftC _ e2 _]} Comp{unComp=[LiftC _ e3 _]} s : steps) = do
    rewrite
    simplLift $ LiftC l (IfE e1 e2 e3 s) s : steps

simplLift (LetC _ decl _ : LiftC l2 e _ : steps) | decl `notUsedIn` steps = do
    rewrite
    return $ LiftC l2 (LetE decl e s) s : steps
  where
    s :: SrcLoc
    s = decl `srcspan` e

simplLift (WhileC l e1 Comp{unComp=[LiftC _ e2 _]} s : steps) = do
    rewrite
    simplLift $ LiftC l (WhileE e1 e2 s) s : steps

simplLift (ForC l ann v tau gint Comp{unComp=[LiftC _ e _]} s : steps) = do
    rewrite
    simplLift $ LiftC l (ForE ann v tau gint e s) s : steps

simplLift (LiftC l e1 _ : LiftC _ e2 _ : steps) = do
    rewrite
    simplLift $ LiftC l (seqE e1 e2) s : steps
  where
    s :: SrcLoc
    s = e1 `srcspan` e2

simplLift (LiftC l e1 _ : BindC _ wv tau _ : LiftC _ e2 _ : steps) | wv `notUsedIn` steps = do
    rewrite
    simplLift $ LiftC l (BindE wv tau e1 e2 s) s : steps
  where
    s :: SrcLoc
    s = e1 `srcspan` e2

simplLift steps =
    return steps

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
        unComp <$> simplC comp >>= rewriteStepsLabel l

    go (Just (DoneComp comp)) =
        inlineCompRhs comp

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "substituted with non-computation."

    callSiteInline :: Maybe (Definition l) -> SimplM l m [Step l]
    callSiteInline maybe_def = do
        flags <- askConfig
        go flags maybe_def
      where
        go :: Config -> Maybe (Definition l) -> SimplM l m [Step l]
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
        unComp <$> (simplC comp >>= traverse uniquify) >>=
                   rewriteStepsLabel l

simplStep (CallC l f0 taus0 args0 s) = do
    taus <- mapM simplType taus0
    args <- mapM simplArg args0
    lookupSubst f0 >>= go f0 taus args
  where
    go :: Var -> [Type] -> [Arg l] -> Maybe (SubstRng l) -> SimplM l m [Step l]
    go f taus args Nothing =
        lookupDefinition f >>= callSiteInline f taus args

    -- This can occur when f was in scope, so it was renamed to f'. We need to
    -- recurse because we may still want to inline the call to f', nee f.
    go _ taus args (Just (DoneExp (VarE f' _))) =
       lookupSubst f' >>= go f' taus args

    go _ taus args (Just (SuspFunComp theta tvks vbs tau_ret comp)) =
        withSubst theta $
        extendTyVarTypes (map fst tvks `zip` taus) $
        extendArgs (map fst vbs `zip` args) $
        withInstantiatedTyVars tau_ret $ do
        inlineBinding f0
        unComp <$> simplC comp >>= rewriteStepsLabel l

    go _ taus args (Just (DoneFunComp tvks vbs tau_ret comp)) =
        inlineFunCompRhs taus args tvks vbs tau_ret comp

    go f _ _ _ =
        faildoc $
        text "Computation function" <+> ppr f <+>
        text "substituted with non-computation function."

    callSiteInline :: Var
                   -> [Type]
                   -> [Arg l]
                   -> Maybe (Definition l)
                   -> SimplM l m [Step l]
    callSiteInline f taus args maybe_def = do
        flags <- askConfig
        go flags maybe_def
      where
        go :: Config -> Maybe (Definition l) -> SimplM l m [Step l]
        go flags (Just (BoundToFunComp _occ tvks vbs tau_ret rhs))
            | testDynFlag MayInlineComp flags =
          inlineFunCompRhs taus args tvks vbs tau_ret rhs

        go _ _ =
            return1 $ CallC l f taus args s

    inlineFunCompRhs :: [Type]
                     -> [Arg l]
                     -> [Tvk]
                     -> [(Var, Type)]
                     -> Type
                     -> Comp l
                     -> SimplM l m [Step l]
    inlineFunCompRhs taus args tvks vbs tau_ret comp =
        withSubst mempty $
        extendTyVarTypes (map fst tvks `zip` taus) $
        extendArgs (map fst vbs `zip` args) $
        withInstantiatedTyVars tau_ret $ do
        inlineBinding f0
        unComp <$> (simplC comp >>= traverse uniquify) >>=
                   rewriteStepsLabel l

    simplArg :: Arg l -> SimplM l m (Arg l)
    simplArg (ExpA e)  = ExpA  <$> simplE e
    simplArg (CompA c) = CompA <$> simplC c

    extendArgs :: [(Var, Arg l)] -> SimplM l m a -> SimplM l m a
    extendArgs []                   k = k
    extendArgs ((v, ExpA e):vargs)  k = extendSubst v (DoneExp e)  $
                                        extendArgs vargs k
    extendArgs ((v, CompA c):vargs) k = extendSubst v (DoneComp c) $
                                        extendArgs vargs k

simplStep (IfC l e1 c2 c3 s) = do
    e1' <- simplE e1
    c2' <- simplC c2
    c3' <- simplC c3
    simplIf e1' c2' c3'
  where
    simplIf :: Exp -> Comp l -> Comp l -> SimplM l m [Step l]
    simplIf e1' c2' c3'
        | isTrue e1'  = return $ unComp c2'
        | isFalse e1' = return $ unComp c3'
        | otherwise   = return1 $ IfC l e1' c2' c3' s

simplStep LetC{} =
    faildoc $ text "Cannot occ let step."

simplStep (WhileC l e c s) =
    WhileC l <$> simplE e <*> simplC c <*> pure s >>= return1

simplStep (ForC l ann v tau gint c s) = do
    ei'   <- simplE ei
    elen' <- simplE elen
    unroll ann ei' elen'
  where
    ei, elen :: Exp
    (ei, elen) = toStartLenGenInt gint

    unroll :: UnrollAnn
           -> Exp
           -> Exp
           -> SimplM l m [Step l]
    unroll _ _ elen' | Just 0 <- fromIntE elen' = do
        rewrite
        return1 $ ReturnC l unitE s

    unroll _ ei' elen' | Just 1 <- fromIntE elen' = do
        rewrite
        extendSubst v (DoneExp ei') $
          unComp <$> simplC c

    unroll Unroll (ConstE (IntC ip i) _) elen' | Just len <- fromIntE elen' = do
        rewrite
        unComp . mconcat <$> mapM body [i..i+len-1]
      where
        -- We must ensure that each unrolling has a unique set of labels
        body :: Int -> SimplM l m (Comp l)
        body i =
            extendSubst v (DoneExp (idx i)) $
            simplC c >>= traverse uniquify
          where
            idx :: Int -> Exp
            idx i = constE $ IntC ip i

    unroll _ ei' elen' =
        withUniqVar v $ \v' ->
        extendVars [(v', tau)] $
        extendDefinitions [(v', Unknown)] $ do
        c' <- simplC c
        return1 $ ForC l ann v' tau (startLenGenInt ei' elen') c' s

simplStep (LiftC l e s) =
    simplE e >>= go
  where
    go :: Exp -> SimplM l m [Step l]
    --
    -- Collapse lifted return
    --
    -- { _ <- lift (return e); ... } ->  { _ <- return e; ... }
    --
    go (ReturnE _ann e' s') = do
        rewrite
        return [ReturnC l e' s']

    go e' =
        return [LiftC l e' s]

simplStep (ReturnC l e s) =
    ReturnC l <$> simplE e <*> pure s >>= return1

simplStep BindC{} =
    faildoc $ text "Cannot occ bind step."

simplStep (TakeC l tau s) = do
    tau' <- simplType tau
    return1 $ TakeC l tau' s

simplStep (TakesC l n tau s) = do
    n'   <- simplType n
    tau' <- simplType tau
    return1 $ TakesC l n' tau' s

simplStep (EmitC l e s) =
    EmitC l <$> simplE e <*> pure s >>= return1

simplStep (EmitsC l e s) =
    EmitsC l <$> simplE e <*> pure s >>= return1

simplStep (RepeatC l ann c s) =
    RepeatC l ann <$> simplC c <*> pure s >>= return1

simplStep (ParC ann b c1 c2 sloc) = do
    (s, a, c) <- askSTIndices
    c1'       <- withFvContext c1 $
                 localSTIndices (Just (s, a, b)) $
                 simplC c1
    c2'       <- withFvContext c2 $
                 localSTIndices (Just (b, b, c)) $
                 simplC c2
    return1 $ ParC ann b c1' c2' sloc

simplConst :: forall l m . (IsLabel l, MonadTc m)
           => Const
           -> SimplM l m Const
simplConst c@UnitC{}        = return c
simplConst c@BoolC{}        = return c
simplConst c@IntC{}         = return c
simplConst c@FixC{}         = return c
simplConst c@FloatC{}       = return c
simplConst c@StringC{}      = return c
simplConst (ArrayC v)       = ArrayC <$> V.mapM simplConst v
simplConst (ReplicateC n c) = ReplicateC n <$> simplConst c
simplConst (EnumC tau)      = EnumC <$> simplType tau

simplConst (StructC struct taus flds) =
    StructC struct <$> mapM simplType taus <*> mapM simplField flds
  where
    simplField :: (Field, Const) -> SimplM l m (Field, Const)
    simplField (f, c) = (,) <$> pure f <*> simplConst c

simplE :: forall l m . (IsLabel l, MonadTc m)
       => Exp
       -> SimplM l m Exp
simplE (ConstE c s)=
    ConstE <$> simplConst c <*> pure s

simplE e0@(VarE v _) =
    lookupSubst v >>= go
  where
    go :: Maybe (SubstRng l) -> SimplM l m Exp
    go Nothing =
        lookupDefinition v >>= callSiteInline

    go (Just (SuspExp theta e)) =
        withSubst theta $ do
        inlineBinding v
        simplE e

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
        flags <- askConfig
        go flags maybe_def
      where
        go :: Config -> Maybe (Definition l) -> SimplM l m Exp
        go flags (Just (BoundToExp occ lvl rhs)) | testDynFlag MayInlineVal flags && inline rhs occ lvl =
            inlineRhs rhs

        go _ _ =
            return e0

    inline :: OutExp -> Maybe OccInfo -> Level -> Bool
    inline _rhs Nothing            _lvl = False
    inline _rhs (Just Dead)        _lvl = error "inline: saw Dead binding"
    -- We may choose not to inline a Once binding if, e.g., it is an array expression
    inline _rhs (Just Once)        _lvl = False
    inline _rhs (Just OnceInFun)   _lvl = False
    inline _rhs (Just ManyBranch)  _lvl = False
    inline _rhs (Just Many)        _lvl = False

    inlineRhs :: Exp -> SimplM l m Exp
    inlineRhs rhs =
        withSubst mempty $ do
        inlineBinding v
        simplE rhs

simplE (UnopE op e s) = do
    e' <- simplE e
    unop op e'
  where
    unop :: Unop -> Exp -> SimplM l m Exp
    unop Lnot (ConstE c _) | Just c' <- liftBool op not c = do
        rewrite
        return $ ConstE c' s

    unop Bnot (ConstE c _) | Just c' <- liftBits op complement c = do
        rewrite
        return $ ConstE c' s

    unop Neg (ConstE c _) | Just c' <- liftNum op negate c = do
        rewrite
        return $ ConstE c' s

    unop Len e' = do
        (tau, _) <- inferExp e' >>= checkArrOrRefArrT
        tau'     <- simplType tau
        case tau' of
          NatT n _ -> do rewrite
                         return $ ConstE (idxC n) s
          _        -> return $ UnopE op e' s

    unop op e' =
        return $ UnopE op e' s

simplE (BinopE op e1 e2 s) = do
    e1' <- simplE e1
    e2' <- simplE e2
    binop op e1' e2'
  where
    binop :: Binop -> Exp -> Exp -> SimplM l m Exp
    binop Lt (ConstE x _) (ConstE y _) =
        return $ ConstE (liftOrd op (<) x y) s

    binop Le (ConstE x _) (ConstE y _) =
        return $ ConstE (liftOrd op (Prelude.<=) x y) s

    binop Eq (ConstE x _) (ConstE y _) =
        return $ ConstE (liftEq op (==) x y) s

    binop Ge (ConstE x _) (ConstE y _) =
        return $ ConstE (liftOrd op (>=) x y) s

    binop Gt (ConstE x _) (ConstE y _) =
        return $ ConstE (liftOrd op (>) x y) s

    binop Ne (ConstE x _) (ConstE y _) =
        return $ ConstE (liftEq op (/=) x y) s

    binop Land e1@(ConstE x _) e2@(ConstE y _)
        | isTrue e1                        = return e2
        | isFalse e1                       = return e1
        | Just c' <- liftBool2 op (&&) x y = return $ ConstE c' s

    binop Lor e1@(ConstE x _) e2@(ConstE y _)
        | isTrue e1                        = return e1
        | isFalse e2                       = return e2
        | Just c' <- liftBool2 op (&&) x y = return $ ConstE c' s

    binop Add (ConstE x _) (ConstE y _) | Just c' <- liftNum2 op (+) x y =
        return $ ConstE c' s

    binop Sub (ConstE x _) (ConstE y _) | Just c' <- liftNum2 op (-) x y =
        return $ ConstE c' s

    binop Mul (ConstE x _) (ConstE y _) | Just c' <- liftNum2 op (*) x y =
        return $ ConstE c' s

    binop Div (ConstE x _) (ConstE y _) | Just c' <- liftIntegral2 op quot x y =
        return $ ConstE c' s

    binop Rem (ConstE x _) (ConstE y _) | Just c' <- liftIntegral2 op rem x y =
        return $ ConstE c' s

    binop op e1' e2' =
        return $ BinopE op e1' e2' s

simplE (IfE e1 e2 e3 s) = do
    e1' <- simplE e1
    e2' <- simplE e2
    e3' <- simplE e3
    simplIf e1' e2' e3'
  where
    simplIf :: Exp -> Exp -> Exp -> SimplM l m Exp
    simplIf e1' e2' e3'
        | isTrue e1'  = return e2'
        | isFalse e1' = return e3'
        | otherwise   = return $ IfE e1' e2' e3' s

simplE (LetE decl e s) = do
    (maybe_decl', e') <- simplLocalDecl decl $ simplE e
    go maybe_decl' e'
  where
    go :: Maybe LocalDecl -> Exp -> SimplM l m Exp
    go Nothing e' =
        return e'

    -- XXX This is a hack to transform an expression of the form
    --
    --     letref (v : tau) = ... in { v := e1; e2 }
    --
    -- into an expression of the forman expression of the form
    --
    --     letref (v : tau) = e1 in e2
    --
    -- It is a not a very general transformation, but we see this pattern over
    -- and over again as a result of the interleaver. We want to perform this
    -- transformation because it may yield a letref that is never actually
    -- modified, meaning we can convert it into a let, meaning we can avoid a
    -- memory copy. And we like to avoid memory copies...
    --
    go (Just (LetRefLD bv tau _ s)) (BindE WildV _ (AssignE (VarE v _) e1 _) e2 _)
      | v == bVar bv = do rewrite
                          return $ LetE (LetRefLD bv tau (Just e1) s) e2 s

    go (Just decl') e' =
        return $ LetE decl' e' s

simplE (CallE f0 taus0 es0 s) = do
    taus <- mapM simplType taus0
    es   <- mapM simplE es0
    lookupSubst f0 >>= go f0 taus es
  where
    go :: Var -> [Type] -> [Exp] -> Maybe (SubstRng l) -> SimplM l m Exp
    go f taus args Nothing =
        lookupDefinition f >>= callSiteInline f taus args

    -- This can occur when f was in scope, so it was renamed to f'. We need to
    -- recurse because we may still want to inline the call to f', nee f.
    go _ taus args (Just (DoneExp (VarE f' _))) =
       lookupSubst f' >>= go f' taus args

    go _ taus args (Just (SuspFun theta tvks vbs _tau_ret e)) =
        withSubst theta $
        extendTyVarTypes (map fst tvks `zip` taus) $
        extendArgs (map fst vbs `zip` args) $ do
        inlineBinding f0
        simplE e

    go _ taus args (Just (DoneFun tvks vbs tau_ret rhs)) =
        inlineFunRhs taus args tvks vbs tau_ret rhs

    go f _ _ _ =
        faildoc $
        text "Function" <+> ppr f <+>
        text "substituted with non-function."

    callSiteInline :: Var
                   -> [Type]
                   -> [Exp]
                   -> Maybe (Definition l)
                   -> SimplM l m Exp
    callSiteInline f taus args maybe_def = do
        flags <- askConfig
        go flags maybe_def
      where
        go :: Config -> Maybe (Definition l) -> SimplM l m Exp
        go flags (Just (BoundToFun _occ tvks vbs tau_ret rhs))
            | testDynFlag MayInlineFun flags =
          inlineFunRhs taus args tvks vbs tau_ret rhs

        go _ _ =
            return $ CallE f taus args s

    inlineFunRhs :: [Type]
                 -> [Exp]
                 -> [Tvk]
                 -> [(Var, Type)]
                 -> Type
                 -> Exp
                 -> SimplM l m Exp
    inlineFunRhs taus args tvks vbs _tau_ret e =
        withSubst mempty $
        extendTyVarTypes (map fst tvks `zip` taus) $
        extendArgs (map fst vbs `zip` args) $ do
        inlineBinding f0
        simplE e

    extendArgs :: [(Var, Exp)] -> SimplM l m a -> SimplM l m a
    extendArgs []             k = k
    extendArgs ((v, e):vargs) k = extendSubst v (DoneExp e) $
                                  extendArgs vargs k

simplE (DerefE e s) = do
    e'  <- simplE e
    tau <- inferExp e'
    return $ if isRefT tau
             then DerefE e' s
             else ReturnE AutoInline e' s

simplE (AssignE e1 e2 s) = do
    drop <- refPathRoot e1 >>= isDroppedRef
    if drop
      then do rewrite
              return $ returnE unitE
      else AssignE <$> simplE e1 <*> simplE e2 <*> pure s

simplE (LowerE tau _) = do
    tau' <- simplType tau
    n    <- evalNat tau'
    return $ intE n

simplE (WhileE e1 e2 s) =
    WhileE <$> simplE e1 <*> simplE e2 <*> pure s

--
-- Simplify empty for loop
--
--   for i in ...
--     return ()
-- ->
--   return ()

simplE (ForE _ann _v _tau _gint e@(ReturnE _ (ConstE UnitC{} _) _) _) = do
    rewrite
    return e

--
-- Simplify assignment loops.
--
--   for i in [0,len]
--     xs[i] := e_yx[i + k]
-- ->
--   xs[0,len] := e_yx[k,len]
--
-- This loop form shows up regularly in fused code.
--
simplE (ForE _ann v _tau gint
             (AssignE (IdxE (VarE xs _) eidx  Nothing _) e_rhs _)
             s)
  | Just len            <- fromIntE elen
  , Just v'             <- fromIdxVarE eidx
  , Just (e_ys, v'', f) <- unIdx e_rhs
  , v' == v, v'' == v
  = do rewrite
       -- The recursive call to 'simplE' is important! We need to be sure to
       -- recursively call simplE here in case @xs@ has been substituted away.
       simplE $ AssignE (IdxE (VarE xs s) ei (Just (fromIntegral len)) s)
                        (IdxE e_ys (f ei) (Just (fromIntegral len)) s)
                        s
  where
    ei, elen :: Exp
    (ei, elen) = toStartLenGenInt gint

    unIdx :: Exp -> Maybe (Exp, Var, Exp -> Exp)
    unIdx (IdxE e1 e2 Nothing _) | Just v <- fromIdxVarE e2 =
        return (e1, v, id)

    unIdx (IdxE e1 (BinopE Add e2 e3 s) Nothing _) | Just v <- fromIdxVarE e2 =
        return (e1, v, \e -> BinopE Add e e3 s)

    unIdx (IdxE e1 (BinopE Add e2 e3 s) Nothing _) | Just v <- fromIdxVarE e3 =
        return (e1, v, \e -> BinopE Add e e2 s)

    unIdx _ =
        fail "Not an index expression"

simplE (ForE ann v tau gint e3 s) = do
    ei'   <- simplE ei
    elen' <- simplE elen
    unroll ann ei' elen'
  where
    ei, elen :: Exp
    (ei, elen) = toStartLenGenInt gint

    unroll :: UnrollAnn
           -> Exp
           -> Exp
           -> SimplM l m Exp
    unroll _ _ elen' | Just 0 <- fromIntE elen' = do
        rewrite
        return $ ReturnE AutoInline unitE s

    unroll _ ei' elen' | Just 1 <- fromIntE elen' = do
        rewrite
        extendSubst v (DoneExp ei') $
          simplE e3

    unroll Unroll (ConstE (IntC ip i) _) elen' | Just len <- fromIntE elen' = do
        rewrite
        es <- mapM body [i..i+len-1]
        return $ foldr seqE (returnE unitE) es
      where
        body :: Int -> SimplM l m Exp
        body i =
            extendSubst v (DoneExp (idx i)) $
            simplE e3
          where
            idx :: Int -> Exp
            idx i = constE $ IntC ip i

    unroll _ ei' elen' =
        withUniqVar v $ \v' ->
        extendVars [(v', tau)] $
        extendDefinitions [(v', Unknown)] $ do
        e3' <- simplE e3
        return $ ForE ann v' tau (startLenGenInt ei' elen') e3' s

simplE (ArrayE es s) =
    mapM simplE es >>= go
  where
    go :: [Exp] -> SimplM l m Exp
    --
    -- Convert a non-constant array expression into a constant array expression
    -- if we can.
    --
    go es' | all isConstE es' = do
        rewrite
        cs <- V.mapM unConstE (V.fromList es)
        return $ ConstE (ArrayC cs) s

    --
    -- Convert an "exploded" array expression into a slice
    --
    -- arr { x[0], x[1], x[2] } -> x[0,3]
    --
    go (IdxE (VarE xs _) ei Nothing _ : es') | Just i  <- fromIntE ei
                                             , Just e' <- coalesce xs i 1 es' = do
        rewrite
        return e'
      where
        coalesce :: Var -> Int -> Int -> [Exp] -> Maybe Exp
        coalesce xs i len [] =
            return $ sliceE (varE xs) (intE i) (fromIntegral len)

        coalesce xs i len (IdxE (VarE xs' _) ej Nothing _ : es'')
          | Just j <- fromIntE ej, j == i + len, xs' == xs =
            coalesce xs i (len+1) es''

        coalesce _ _ _ _ =
            fail "Cannot coalesce"

    go es' =
        return $ ArrayE es' s

simplE (IdxE e1 e2 len0 s) = do
    e1' <- simplE e1
    e2' <- simplE e2
    go e1' e2' len0
  where
    go :: Exp -> Exp -> Maybe Type -> SimplM l m Exp
    --
    -- Replace a slice of a slice with a single slice.
    --
    --  x[i, n][j, m] -> x[i+j, m]
    --
    go (IdxE e1' ei Just{} _) e2' len = do
        rewrite
        go e1' (ei + e2') len

    --
    -- Replace a whole-array slice with the array itself.
    --
    --   x[0, n] -> n        when x is an array of size n
    --
    go e1' e2' (Just len) | Just 0 <- fromIntE e2' = do
        (nat, _) <- inferExp e1' >>= checkArrOrRefArrT
        if nat == len
          then do rewrite
                  return e1'
          else return $ IdxE e1' e2' (Just len) s

    go e1' e2' len =
        return $ IdxE e1' e2' len s

simplE (StructE struct taus flds s) = do
    es'   <- mapM simplE es
    taus' <- mapM simplType taus
    if all isConstE es'
      then do cs <- mapM unConstE es'
              return $ ConstE (StructC struct taus' (fs `zip` cs)) s
      else return $ StructE struct taus' (fs `zip` es') s
  where
    fs :: [Field]
    es :: [Exp]
    (fs, es) = unzip flds

simplE (ProjE e f s) =
    simplE e >>= go
  where
    go :: Exp -> SimplM l m Exp
    go (StructE _ _ flds _) =
        case lookup f flds of
          Nothing -> faildoc $ text "Unknown struct field" <+> ppr f
          Just e' -> return e'

    go (ConstE (StructC _ _ flds) _) =
        case lookup f flds of
          Nothing -> faildoc $ text "Unknown struct field" <+> ppr f
          Just c  -> return $ ConstE c s

    go e' =
        return $ ProjE e' f s

simplE (CastE tau e s) = do
    tau' <- simplType tau
    e'   <- simplE e
    cast tau' e'
  where
    cast :: Type -> Exp -> SimplM l m Exp
    cast (StructT sn' taus' _) (ConstE (StructC sn _taus flds) s) | isComplexStruct sn && isComplexStruct sn' = do
        rewrite
        flds' <- castStruct cast' sn' flds
        return $ ConstE (StructC sn' taus' flds') s
      where
        cast' :: Type -> Const -> SimplM l m Const
        cast' tau c = do
            ConstE c' _ <- cast tau (ConstE c s)
            return c'

    cast (StructT sn' taus' _) (StructE sn _taus flds s) | isComplexStruct sn && isComplexStruct sn' = do
        rewrite
        flds' <- castStruct cast sn' flds
        return $ StructE sn' taus' flds' s

    -- Eliminate casts of constants
    cast tau (ConstE c _) | Just c' <- liftCast tau c = do
        rewrite
        return $ ConstE c' s

    -- Avoid double cast
    cast tau e = do
        tau' <- inferExp e
        if tau' == tau
          then do rewrite
                  return e
          else return $ CastE tau e s

simplE (BitcastE tau e s) = do
    tau' <- simplType tau
    e'   <- simplE e
    bitcast tau' e'
  where
    bitcast :: Type -> Exp -> SimplM l m Exp
    -- Remove duplicate bitcast operations.
    bitcast tau (BitcastE _ e s) = do
        rewrite
        return $ BitcastE tau e s

    bitcast tau e =
        return $ BitcastE tau e s

simplE (PrintE nl es s) =
    PrintE nl <$> mapM simplE es <*> pure s

simplE e@ErrorE{} =
    return e

simplE (ReturnE ann e s) =
    ReturnE ann <$> simplE e <*> pure s

simplE (BindE wv tau e1 e2 s) = do
    tau' <- simplType tau
    simplBind wv tau' e1 e2 s
  where
    simplBind :: WildVar
              -> Type
              -> Exp
              -> Exp
              -> SrcLoc
              -> SimplM l m Exp
    -- Reassociate bind
    simplBind wv tau (BindE wv' tau' e1a e1b s') e2 s = do
        rewrite
        simplBind wv' tau' e1a (BindE wv tau e1b e2 s') s

    --
    -- Drop unnecessary final return (), e.g.,
    --
    --   { ... ; x := 1; return (); } -> { ... ; x := 1; }
    --
    simplBind WildV UnitT{} e1 (ReturnE _ann (ConstE UnitC _) _) _s = do
        rewrite
        simplE e1

    --
    -- Drop an unbound return, e.g.,
    --
    --   { return e1; ... } -> { ... }
    --
    simplBind WildV _tau ReturnE{} e2 _s = do
        rewrite
        simplE e2

    --
    -- Combine sequential array assignments.
    --
    --  { x[e1] := y[e2]; x[e1+1] := y[e2+1]; ... } -> { x[e1:1] := y[e2:1]; ... }
    --
    -- We see this after coalescing/fusion
    --
    simplBind WildV _ e1 e_rest _
      | let (e2, mkBind) = unBind e_rest
      , AssignE (IdxE xs e_i len1 s1) (IdxE ys e_k len1' s2) s3 <- e1
      , len1' == len1
      , AssignE (IdxE xs' e_j len2 _)  (IdxE ys' e_l len2' _)  _ <- e2
      , len2' == len2
      , xs' == xs
      , ys' == ys
      , e_i + sliceLen len1 == e_j
      , e_k + sliceLen len1 == e_l
      = do
        rewrite
        let len = plusl len1 len2
        simplE $ mkBind $ AssignE (IdxE xs e_i len s1) (IdxE ys e_k len s2) s3
      where
        plusl :: Maybe Type -> Maybe Type -> Maybe Type
        plusl len1 len2 = Just $ sliceLen len1 + sliceLen len2

    --
    -- Combine sequential assignment and dereference.
    --
    --  { x := e; !x; ... } -> { x := e; return e; ... }
    --
    -- We see this after coalescing/fusion. We must be careful not to duplicate
    -- work! To avoid work duplication, we onlt inline e_rhs when it is simple
    -- or when x is used only once, i.e., only here!
    --
    simplBind WildV tau e1 e_rest s
      | let (e2, mkBind) = unBind e_rest
      , AssignE (VarE v  _) e_rhs _ <- e1
      , DerefE  (VarE v' _)       _ <- e2
      , v' == v
      = do
        theta  <- lookupSubst v
        let v' =  case theta of
                    Just (DoneExp (VarE v' _)) -> v'
                    _ -> v
        occ    <- lookupOccInfo v'
        if isSimple e_rhs || occ == Just Once
          then do rewrite
                  simplBind WildV tau e1 (mkBind (returnE e_rhs)) s
          else simplWildBind tau e1 e_rest s

    --
    -- Default command sequencing
    --
    simplBind WildV tau e1 e2 s =
        simplWildBind tau e1 e2 s

    --
    -- Drop unused bindings. The expression whose result is bound might have an
    -- effect, so we can't just throw it away.
    --
    simplBind (TameV v) tau e1 e2 s | bOccInfo v == Just Dead = do
        dropBinding v
        simplBind WildV tau e1 e2 s

    --
    -- Convert a bind-return into a let, e.g.,
    --
    --   { x <- return e1; ... } -> { let x = e1; ... }
    --
    simplBind (TameV v) tau (ReturnE _ e1 _) e2 s = do
        e1'  <- simplE e1
        tau' <- simplType tau
        withUniqBoundVar v $ \v' ->
          extendVars [(bVar v', tau)] $
          extendDefinitions [(bVar v', BoundToExp Nothing Nested e1')] $ do
          e2' <- simplE e2
          rewrite
          return $ LetE (LetLD v' tau' e1' s) e2' s

    --
    -- Avoid an identity assignment
    --
    --   { v <- !x; x := v; ... } -> { v <- !x; ... }
    --
    simplBind (TameV v) tau e1@(DerefE e_rhs _ ) e_rest _
      | let (e2, mkBind) = unBind e_rest
      , AssignE e_lhs (VarE v' _) _ <- e2
      , v' == bVar v
      , e_lhs == e_rhs
      = do
        rewrite
        simplBind (TameV v) tau e1 (mkBind (returnE unitE)) s

    --
    -- Default command bind
    --
    simplBind (TameV v) tau e1 e2 s = do
        e1'  <- simplE e1
        tau' <- simplType tau
        withUniqBoundVar v $ \v' ->
          extendVars [(bVar v', tau)] $
          extendDefinitions [(bVar v', Unknown)] $ do
          e2' <- simplE e2
          return $ BindE (TameV v') tau' e1' e2' s

    -- Default code for simplifying a WildV binding
    simplWildBind :: Type
                  -> Exp
                  -> Exp
                  -> SrcLoc
                  -> SimplM l m Exp
    simplWildBind tau e1 e2 s = do
        tau' <- simplType tau
        e1'  <- simplE e1
        e2'  <- simplE e2
        return $ BindE WildV tau' e1' e2' s

    -- This gives us a handy way to pull apart binds so we don't have to
    -- separately handle the cases { e1; e2; } and { e1; e2; ... }
    unBind :: Exp -> (Exp, Exp -> Exp)
    unBind (BindE wv tau e1 e2 s) = (e1, \e1' -> BindE wv tau e1' e2 s)
    unBind e                      = (e, id)

simplE (LutE sz e) =
    LutE sz <$> simplE e

simplE (GenE e gs s) =
    checkGenerators gs $ \_ ->
    GenE <$> simplE e <*> pure gs <*> pure s

isTrue :: Exp -> Bool
isTrue (ConstE (BoolC True) _) = True
isTrue _                       = False

isFalse :: Exp -> Bool
isFalse (ConstE (BoolC False) _) = True
isFalse _                        = False

return1 :: Monad m => a -> m [a]
return1 x = return [x]

isSimple :: Exp -> Bool
isSimple e =
    go e && Set.size (fvs e :: Set Var) Prelude.<= 1
  where
    go :: Exp -> Bool
    go VarE{}             = True
    go ConstE{}           = True
    go (UnopE Len _ _)    = True
    go (UnopE _ e _)      = go e
    go (BinopE _ e1 e2 _) = go e1 && go e2
    go (IfE e1 e2 e3 _)   = go e1 && go e2 && go e3
    go (IdxE e1 e2 _ _)   = go e1 && go e2
    go (ProjE e _ _)      = go e
    go _                  = False

shouldInlineExpUnconditionally :: MonadTc m
                               => InExp -> SimplM l m Bool
shouldInlineExpUnconditionally e | isSimple e =
    asksConfig (testDynFlag MayInlineVal)

shouldInlineExpUnconditionally _ =
    return False

shouldInlineFunUnconditionally :: MonadTc m
                               => [Tvk]
                               -> [(Var, Type)]
                               -> Type
                               -> OutExp
                               -> SimplM l m Bool
shouldInlineFunUnconditionally _ _ _ e | isSimple e =
    asksConfig (testDynFlag MayInlineFun)

shouldInlineFunUnconditionally _ _ _ _ =
    return False

shouldInlineCompUnconditionally :: MonadTc m
                                => InComp l -> SimplM l m Bool
shouldInlineCompUnconditionally _ =
    asksConfig (testDynFlag AlwaysInlineComp)

shouldInlineCompFunUnconditionally :: MonadTc m
                                   => [Tvk]
                                   -> [(Var, Type)]
                                   -> Type
                                   -> OutComp l
                                   -> SimplM l m Bool
shouldInlineCompFunUnconditionally _ _ _ _ =
    asksConfig (testDynFlag AlwaysInlineComp)
