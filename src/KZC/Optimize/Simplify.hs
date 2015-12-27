{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Simplify
-- Copyright   :  (c) Drexel University 2015
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Simplify (
    SimplStats(..),
    SimplM,
    runSimplM,

    simplProgram
  ) where

import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            modify)
import Data.IORef
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Traversable (traverse)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Name
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

type InVar  = Var
type InExp  = Exp
type InComp = LComp

type OutVar  = Var
type OutExp  = Exp
type OutComp = LComp

type Theta = Map InVar SubstRng

data SubstRng = SuspExp     Theta InExp
              | SuspFun     Theta [IVar] [(Var, Type)] Type InExp
              | SuspComp    Theta InComp
              | SuspFunComp Theta [IVar] [(Var, Type)] Type InComp
              | DoneExp     OutExp
              | DoneFun     [IVar] [(Var, Type)] Type OutExp
              | DoneComp    OutComp
              | DoneFunComp [IVar] [(Var, Type)] Type OutComp
  deriving (Eq, Ord, Read, Show)

type VarDefs = Map OutVar Definition

data Definition = Unknown
                | BoundToExp     (Maybe OccInfo) Level OutExp
                | BoundToFun     (Maybe OccInfo) [IVar] [(Var, Type)] Type OutExp
                | BoundToComp    (Maybe OccInfo) OutComp
                | BoundToFunComp (Maybe OccInfo) [IVar] [(Var, Type)] Type OutComp
  deriving (Eq, Ord, Read, Show)

data Level = Top | Nested
  deriving (Eq, Ord, Read, Show)

type Phi = Map IVar Iota

type Psi = Map TyVar Type

data SimplStats = SimplStats
    { simplDrop   :: Int
    , simplInline :: Int
    }
  deriving (Eq, Ord, Show)

instance Monoid SimplStats where
    mempty =
        SimplStats { simplDrop   = 0
                   , simplInline = 0
                   }

    s1 `mappend` s2 =
        SimplStats { simplDrop   = simplDrop s1 + simplDrop s2
                   , simplInline = simplInline s1 + simplInline s2
                   }

data SimplEnv = SimplEnv
    { simplTcEnv   :: !TcEnv
    , simplTheta   :: !Theta
    , simplVarDefs :: !VarDefs
    , simplPhi     :: !Phi
    , simplPsi     :: !Psi
    }

defaultSimplEnv :: TcEnv -> SimplEnv
defaultSimplEnv tcenv = SimplEnv tcenv mempty mempty mempty mempty

data SimplState = SimplState
    { simplStats :: SimplStats }

defaultSimplState :: SimplState
defaultSimplState = SimplState
    { simplStats = mempty }

newtype SimplM a = SimplM { unSimplM :: StateT SimplState (ReaderT SimplEnv KZC) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader SimplEnv,
              MonadState SimplState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runSimplM :: SimplM a -> TcEnv -> KZC (a, SimplStats)
runSimplM m tcenv = do
    (x, st) <- runReaderT (runStateT (unSimplM m) defaultSimplState) (defaultSimplEnv tcenv)
    return (x, simplStats st)

instance MonadTc SimplM where
    askTc = SimplM $ asks simplTcEnv
    localTc f m =
        SimplM $ local (\env -> env { simplTcEnv = f (simplTcEnv env) }) $
        unSimplM m

mappendStats :: SimplStats -> SimplM ()
mappendStats stats =
    modify $ \s -> s { simplStats = simplStats s <> stats }

dropBinding :: BoundVar -> SimplM ()
dropBinding _ =
    mappendStats mempty { simplDrop = 1 }

inlineBinding :: Var -> SimplM ()
inlineBinding _v =
    mappendStats mempty { simplInline = 1 }

askSubst :: SimplM Theta
askSubst = asks simplTheta

lookupSubst :: InVar -> SimplM (Maybe SubstRng)
lookupSubst v = asks (Map.lookup v . simplTheta)

killVars :: [InVar] -> SimplM a -> SimplM a
killVars vs k =
    local
    (\env -> env { simplTheta = foldl' (flip Map.delete) (simplTheta env) vs }) k

extendSubst :: InVar -> SubstRng -> SimplM a -> SimplM a
extendSubst v rng k =
    local (\env -> env { simplTheta = Map.insert v rng (simplTheta env) }) k

withSubst :: Theta -> SimplM a -> SimplM a
withSubst theta k =
    local (\env -> env { simplTheta = theta }) k

isInScope :: InVar -> SimplM Bool
isInScope v = asks (Map.member v . simplVarDefs)

lookupDefinition :: InVar -> SimplM (Maybe Definition)
lookupDefinition v = asks (Map.lookup v . simplVarDefs)

extendDefinitions :: [(OutVar, Definition)] -> SimplM a -> SimplM a
extendDefinitions defs k =
    local (\env -> env { simplVarDefs = foldl' insert (simplVarDefs env) defs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

withUniqVar :: Var
            -> (Var -> SimplM a)
            -> SimplM a
withUniqVar v k = do
    inscope <- isInScope v
    if inscope
      then do v' <- mkUniq v
              extendSubst v ((DoneExp . varE) v') $ k v'
      else killVars [v] $ k v

withUniqVars :: [Var]
             -> ([Var] -> SimplM a)
             -> SimplM a
withUniqVars [] k =
    k []

withUniqVars (v:vs) k =
    withUniqVar  v  $ \v'  ->
    withUniqVars vs $ \vs' ->
    k (v':vs')

withUniqBoundVar :: BoundVar
                 -> (BoundVar -> SimplM a)
                 -> SimplM a
withUniqBoundVar v k = do
    inscope <- isInScope (bVar v)
    if inscope
      then do v' <- mkUniq v
              extendSubst (bVar v) ((DoneExp . varE . bVar) v') $ k v'
      else killVars [bVar v] $ k v

askIVarSubst :: SimplM Phi
askIVarSubst = asks simplPhi

extendIVarSubst :: [(IVar, Iota)] -> SimplM a -> SimplM a
extendIVarSubst ivs k =
    local (\env -> env { simplPhi = foldl' insert (simplPhi env) ivs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

askTyVarSubst :: SimplM Psi
askTyVarSubst = asks simplPsi

extendTyVarSubst :: [(TyVar, Type)] -> SimplM a -> SimplM a
extendTyVarSubst tvs k =
    local (\env -> env { simplPsi = foldl' insert (simplPsi env) tvs }) k
  where
    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context.
withInstantiatedTyVars :: Type -> SimplM a ->SimplM a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarSubst [(alpha, tau) | (TyVarT alpha _, tau) <-
                                       [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

simplProgram :: LProgram -> SimplM LProgram
simplProgram (Program decls comp tau) = do
  (decls', comp') <-
      simplDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      simplComp comp
  return $ Program decls' comp' tau

simplType :: Type -> SimplM Type
simplType tau = do
    phi <- askTyVarSubst
    psi <- askIVarSubst
    return $ subst psi mempty (subst phi mempty tau)

simplIota :: Iota -> SimplM Iota
simplIota iota = do
    psi <- askIVarSubst
    return $ subst psi mempty iota

simplDecls :: [LDecl]
           -> SimplM a
           -> SimplM ([LDecl], a)
simplDecls [] m = do
    x <- m
    return ([], x)

simplDecls (d:ds) m = do
    (maybe_d', (ds', x)) <- simplDecl d $ simplDecls ds $ m
    return (maybe ds' (:ds') maybe_d', x)

simplDecl :: forall a . LDecl
          -> SimplM a
          -> SimplM (Maybe LDecl, a)
simplDecl (LetD decl s) m = do
    (maybe_decl', x) <- simplLocalDecl decl m
    case maybe_decl' of
      Nothing    -> return (Nothing, x)
      Just decl' -> return (Just (LetD decl' s), x)

simplDecl decl m = do
    mayInline <- asksFlags (testDynFlag MayInline)
    preInlineUnconditionally mayInline decl
  where
    -- | Drop a dead binding and unconditionally inline a binding that occurs only
    -- once.
    preInlineUnconditionally :: Bool -> LDecl -> SimplM (Maybe LDecl, a)
    preInlineUnconditionally _mayInline (LetD {}) =
        faildoc $ text "preInlineUnconditionally: can't happen"

    preInlineUnconditionally mayInline decl@(LetFunD f ivs vbs tau_ret e _)
        | isDead    = dropBinding f >> withoutBinding m
        | isOnce &&
          mayInline = do theta <- askSubst
                         extendSubst (bVar f) (SuspFun theta ivs vbs tau_ret e) $ do
                         dropBinding f
                         withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    preInlineUnconditionally mayInline decl@(LetExtFunD f _ _ _ _)
        | isDead    = dropBinding f >> withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead :: Bool
        isDead = bOccInfo f == Just Dead

    preInlineUnconditionally mayInline decl@(LetStructD {}) =
        postInlineUnconditionally mayInline decl

    preInlineUnconditionally mayInline decl@(LetCompD v _ comp _)
        | isDead    = dropBinding v >> withoutBinding m
        | isOnce &&
          mayInline = do theta <- askSubst
                         extendSubst (bVar v) (SuspComp theta comp) $ do
                         dropBinding v
                         withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo v == Just Dead
        isOnce = bOccInfo v == Just Once

    preInlineUnconditionally mayInline (LetFunCompD f ivs vbs tau_ret comp _)
        | isDead    = dropBinding f >> withoutBinding m
        | isOnce &&
          mayInline = do theta <- askSubst
                         extendSubst (bVar f)
                                     (SuspFunComp theta ivs vbs tau_ret comp) $ do
                         dropBinding f
                         withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo f == Just Dead
        isOnce = bOccInfo f == Just Once

    -- | Simplify the right-hand-side of a binding and then see if we want to
    -- inline it unconditionally. If so, add it to the current
    -- substitution. Otherwise, rename it if needed and add it to the current
    -- set of in scope bindings.
    postInlineUnconditionally :: Bool -> LDecl -> SimplM (Maybe LDecl, a)
    postInlineUnconditionally _mayInline (LetD {}) =
        faildoc $ text "postInlineUnconditionally: can't happen"

    postInlineUnconditionally _mayInline (LetFunD f ivs vbs tau_ret e l) = do
        (ivs', vbs', tau_ret', e') <-
            extendVars [(bVar f, tau)] $
            extendIVars (ivs `zip` repeat IotaK) $
            extendVars vbs $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $
            inSTScope tau_ret $
            inLocalScope $ do
            tau_ret' <- simplType tau_ret
            e'       <- simplExp e
            return (ivs, (vs' `zip` taus), tau_ret', e')
        inlineIt <- shouldInlineFunUnconditionally ivs' vbs' tau_ret' e'
        if inlineIt
          then extendSubst (bVar f) (DoneFun ivs' vbs' tau_ret' e') $ do
               dropBinding f
               withoutBinding m
          else extendVars [(bVar f, tau)] $
               withUniqBoundVar f $ \f' ->
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

    postInlineUnconditionally _mayInline (LetExtFunD f iotas vbs tau_ret l) =
        extendVars [(bVar f, tau)] $
        withBinding (LetExtFunD f iotas vbs tau_ret l) $
        m
      where
        tau :: Type
        tau = FunT iotas (map snd vbs) tau_ret l

    postInlineUnconditionally _mayInline decl@(LetStructD s flds l) =
        extendStructs [StructDef s flds l] $
        withBinding decl $
        m

    postInlineUnconditionally _mayInline (LetCompD v tau comp l) = do
        comp' <- inSTScope tau $
                 inLocalScope $
                 simplComp comp
        inlineIt <- shouldInlineCompUnconditionally comp'
        if inlineIt
          then extendSubst (bVar v) (DoneComp comp') $ do
               dropBinding v
               withoutBinding m
          else extendVars [(bVar v, tau)] $
               withUniqBoundVar v $ \v' ->
               extendDefinitions [(bVar v', BoundToComp (bOccInfo v') comp')] $
               withBinding (LetCompD v' tau comp' l) $
               m

    postInlineUnconditionally _mayInline (LetFunCompD f ivs vbs tau_ret comp l) = do
        (ivs', vbs', tau_ret', comp') <-
            extendVars [(bVar f, tau)] $
            extendIVars (ivs `zip` repeat IotaK) $
            extendVars vbs $
            withUniqVars vs $ \vs' ->
            extendDefinitions (vs `zip` repeat Unknown) $
            inSTScope tau_ret $
            inLocalScope $ do
            tau_ret' <- simplType tau_ret
            comp'    <- simplComp comp
            return (ivs, (vs' `zip` taus), tau_ret', comp')
        inlineIt <- shouldInlineCompFunUnconditionally ivs' vbs' tau_ret' comp'
        if inlineIt
          then extendSubst (bVar f) (DoneFunComp ivs' vbs' tau_ret' comp') $ do
               dropBinding f
               withoutBinding m
          else extendVars [(bVar f, tau)] $
               withUniqBoundVar f $ \f' ->
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

    withoutBinding :: SimplM a -> SimplM (Maybe LDecl, a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: LDecl -> SimplM a -> SimplM (Maybe LDecl, a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

simplLocalDecl :: forall a . LocalDecl
               -> SimplM a
               -> SimplM (Maybe LocalDecl, a)
simplLocalDecl decl m = do
    mayInline <- asksFlags (testDynFlag MayInline)
    preInlineUnconditionally mayInline decl
  where
    preInlineUnconditionally :: Bool -> LocalDecl -> SimplM (Maybe LocalDecl, a)
    preInlineUnconditionally mayInline decl@(LetLD v _ e _)
        | isDead    = dropBinding v >> withoutBinding m
        | isOnce &&
          mayInline = do theta <- askSubst
                         extendSubst (bVar v) (SuspExp theta e) $ do
                         dropBinding v
                         withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead, isOnce :: Bool
        isDead = bOccInfo v == Just Dead
        isOnce = bOccInfo v == Just Once

    preInlineUnconditionally mayInline decl@(LetRefLD v _ _ _)
        | isDead    = dropBinding v >> withoutBinding m
        | otherwise = postInlineUnconditionally mayInline decl
      where
        isDead :: Bool
        isDead = bOccInfo v == Just Dead

    postInlineUnconditionally :: Bool -> LocalDecl -> SimplM (Maybe LocalDecl, a)
    postInlineUnconditionally _mayInline (LetLD v tau e s) = do
        e'       <- simplExp e
        tau'     <- simplType tau
        inlineIt <- shouldInlineExpUnconditionally e'
        if inlineIt
          then extendSubst (bVar v) (DoneExp e') $ do
               dropBinding v
               withoutBinding m
          else extendVars [(bVar v, tau)] $
               withUniqBoundVar v $ \v' ->
               extendDefinitions [(bVar v', BoundToExp (bOccInfo v') Top e')] $
               withBinding (LetLD v' tau' e' s) m

    postInlineUnconditionally _mayInline (LetRefLD v tau e s) = do
        e'   <- traverse simplExp e
        tau' <- simplType tau
        extendVars [(bVar v, refT tau)] $
            withUniqBoundVar v $ \v' ->
            extendDefinitions [(bVar v', Unknown)] $
            withBinding (LetRefLD v' tau' e' s) m

    withoutBinding :: SimplM a -> SimplM (Maybe LocalDecl, a)
    withoutBinding m = (,) <$> pure Nothing <*> m

    withBinding :: LocalDecl -> SimplM a -> SimplM (Maybe LocalDecl, a)
    withBinding decl m = (,) <$> pure (Just decl) <*> m

simplComp :: LComp -> SimplM LComp
simplComp (Comp steps) = Comp <$> simplSteps steps

simplSteps :: [LStep] -> SimplM [LStep]
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
    go :: [LStep] -> Type -> WildVar -> SimplM [LStep]
    go [step'] tau' (TameV v) | bOccInfo v == Just Dead = do
        dropBinding v
        go [step'] tau' WildV

    go [ReturnC {}] _tau' WildV =
        simplSteps steps

    go [ReturnC l e s] tau' (TameV v) =
        extendVars [(bVar v, tau)] $
        withUniqBoundVar v $ \v' ->
        extendDefinitions [(bVar v', BoundToExp Nothing Nested e)] $ do
        steps' <- simplSteps steps
        return $ LetC l (LetLD v' tau' e s) s : steps'

    go [step'] tau' WildV = do
        steps' <- simplSteps steps
        return $ step' : BindC l WildV tau' s : steps'

    go [step'] tau' (TameV v) =
        extendVars [(bVar v, tau)] $
        withUniqBoundVar v $ \v' ->
        extendDefinitions [(bVar v', Unknown)] $ do
        steps' <- simplSteps steps
        return $ step' : BindC l (TameV v') tau' s : steps'

    go [] _tau' _wv =
        faildoc $ text "simplSteps: can't happen"

    go step' tau' wv = do
        (++) <$> pure hd <*> go [tl] tau' wv
      where
        hd :: [LStep]
        tl :: LStep
        hd = init step'
        tl = last step'

simplSteps (step : steps) =
    (++) <$> simplStep step <*> simplSteps steps

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

simplStep :: LStep -> SimplM [LStep]
simplStep step@(VarC l v _) =
    lookupSubst v >>= go
  where
    go :: Maybe SubstRng -> SimplM [LStep]
    go Nothing = do
        mayInline <- asksFlags (testDynFlag MayInline)
        lookupDefinition v >>= callSiteInline mayInline

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

    callSiteInline :: Bool -> Maybe Definition -> SimplM [LStep]
    callSiteInline mayInline (Just (BoundToComp occ rhs)) | mayInline && inline occ rhs =
        inlineCompRhs rhs

    callSiteInline _ _ =
        return [step]

    inline :: Maybe OccInfo -> OutComp -> Bool
    inline _occ _rhs = True

    inlineCompRhs :: LComp -> SimplM [LStep]
    inlineCompRhs comp =
        withSubst mempty $ do
        inlineBinding v
        unComp <$> (simplComp comp >>= uniquifyCompLabels) >>= rewriteStepsLabel l

simplStep (CallC l f0 iotas0 args0 s) = do
    iotas <- mapM simplIota iotas0
    args  <- mapM simplArg args0
    lookupSubst f0 >>= go f0 iotas args
  where
    go :: Var -> [Iota] -> [LArg] -> Maybe SubstRng -> SimplM [LStep]
    go f iotas args Nothing = do
        mayInline <- asksFlags (testDynFlag MayInline)
        lookupDefinition f >>= callSiteInline mayInline f iotas args

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

    callSiteInline :: Bool
                   -> Var
                   -> [Iota]
                   -> [LArg]
                   -> Maybe Definition
                   -> SimplM [LStep]
    callSiteInline mayInline _ iotas args (Just (BoundToFunComp occ ivs vbs tau_ret rhs))
        | mayInline && inline occ iotas args ivs vbs tau_ret rhs =
            inlineFunCompRhs iotas args ivs vbs tau_ret rhs

    callSiteInline _mayInline f iotas args _ =
        return1 $ CallC l f iotas args s

    inline :: Maybe OccInfo
           -> [Iota]
           -> [LArg]
           -> [IVar]
           -> [(Var, Type)]
           -> Type
           -> LComp
           -> Bool
    inline _iotas _occ _args _ivs _vbs _tau_ret _rhs = True

    inlineFunCompRhs :: [Iota]
                     -> [LArg]
                     -> [IVar]
                     -> [(Var, Type)]
                     -> Type
                     -> LComp
                     -> SimplM [LStep]
    inlineFunCompRhs iotas args ivs vbs tau_ret comp =
        withSubst mempty $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $
        withInstantiatedTyVars tau_ret $ do
        inlineBinding f0
        unComp <$> (simplComp comp >>= uniquifyCompLabels) >>= rewriteStepsLabel l

    simplArg :: LArg -> SimplM LArg
    simplArg (ExpA e)  = ExpA  <$> simplExp e
    simplArg (CompA c) = CompA <$> simplComp c

    extendArgs :: [(Var, LArg)] -> SimplM a -> SimplM a
    extendArgs []                   k = k
    extendArgs ((v, ExpA e):vargs)  k = extendSubst v (DoneExp e)  $
                                        extendArgs vargs k
    extendArgs ((v, CompA c):vargs) k = extendSubst v (DoneComp c) $
                                        extendArgs vargs k

simplStep (IfC l e c1 c2 s) =
    IfC l <$> simplExp e <*> simplComp c1 <*> simplComp c2 <*> pure s >>= return1

simplStep (LetC {}) =
    faildoc $ text "Cannot occ let step."

simplStep (WhileC l e c s) = do
    WhileC l <$> simplExp e <*> simplComp c <*> pure s >>= return1

simplStep (ForC l ann v tau e1 e2 c s) = do
    e1' <- simplExp e1
    e2' <- simplExp e2
    extendVars [(v, tau)] $
        withUniqVar v $ \v' ->
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

simplExp :: Exp -> SimplM Exp
simplExp e@(ConstE {}) =
    return e

simplExp e0@(VarE v _) =
    lookupSubst v >>= go
  where
    go :: Maybe SubstRng -> SimplM Exp
    go Nothing = do
        mayInline <- asksFlags (testDynFlag MayInline)
        lookupDefinition v >>= callSiteInline mayInline

    go (Just (SuspExp theta e)) =
        withSubst theta $ do
        inlineBinding v
        simplExp e

    go (Just (DoneExp e)) =
        inlineRhs e

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "substituted with non-expression."

    callSiteInline :: Bool -> Maybe Definition -> SimplM Exp
    callSiteInline mayInline (Just (BoundToExp occ lvl rhs)) | mayInline && inline rhs occ lvl =
        inlineRhs rhs

    callSiteInline _mayInline _ =
        return e0

    inline :: OutExp -> Maybe OccInfo -> Level -> Bool
    inline _rhs Nothing            _lvl = False
    inline _rhs (Just Dead)        _lvl = error "inline: Dead"
    inline _rhs (Just Once)        _lvl = error "inline: Once"
    inline _rhs (Just OnceInFun)   _lvl = False
    inline _rhs (Just ManyBranch)  _lvl = False
    inline _rhs (Just Many)        _lvl = False

    inlineRhs :: Exp -> SimplM Exp
    inlineRhs rhs =
        withSubst mempty $ do
        inlineBinding v
        simplExp rhs

simplExp (UnopE op e s) =
    UnopE op <$> simplExp e <*> pure s

simplExp (BinopE op e1 e2 s) =
    BinopE op <$> simplExp e1 <*> simplExp e2 <*> pure s

simplExp (IfE e1 e2 e3 s) =
    IfE <$> simplExp e1 <*> simplExp e2 <*> simplExp e3 <*> pure s

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
    go :: Var -> [Iota] -> [Exp] -> Maybe SubstRng -> SimplM Exp
    go f iotas args Nothing = do
        mayInline <- asksFlags (testDynFlag MayInline)
        lookupDefinition f >>= callSiteInline mayInline f iotas args

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

    callSiteInline :: Bool -> Var -> [Iota] -> [Exp] -> Maybe Definition -> SimplM Exp
    callSiteInline mayInline _ iotas args (Just (BoundToFun occ ivs vbs tau_ret rhs))
        | mayInline && inline occ iotas args ivs vbs tau_ret rhs =
            inlineFunRhs iotas args ivs vbs tau_ret rhs

    callSiteInline _mayInline f iotas args _ =
        return $ CallE f iotas args s

    inline :: Maybe OccInfo
           -> [Iota]
           -> [Exp]
           -> [IVar]
           -> [(Var, Type)]
           -> Type
           -> Exp
           -> Bool
    inline _iotas _occ _args _ivs _vbs _tau_ret _rhs = True

    inlineFunRhs :: [Iota]
                 -> [Exp]
                 -> [IVar]
                 -> [(Var, Type)]
                 -> Type
                 -> Exp
                 -> SimplM Exp
    inlineFunRhs iotas args ivs vbs _tau_ret e =
        withSubst mempty $
        extendIVarSubst (ivs `zip` iotas) $
        extendArgs (map fst vbs `zip` args) $ do
        inlineBinding f0
        simplExp e

    extendArgs :: [(Var, Exp)] -> SimplM a -> SimplM a
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
    go :: Exp -> Type -> WildVar -> SimplM Exp
    go e tau' (TameV v) | bOccInfo v == Just Dead = do
        dropBinding v
        go e tau' WildV

    go (ReturnE {}) _tau' WildV =
        simplExp e2

    go (ReturnE _ e1' _) tau' (TameV v) = do
        decl <- extendVars [(bVar v, tau)] $
                withUniqBoundVar v $ \v' ->
                extendDefinitions [(bVar v', BoundToExp Nothing Nested e1')] $
                return $ LetLD v' tau' e1' s
        e2'  <- simplExp e2
        return $ LetE decl e2' s

    go e1' tau' WildV = do
        e2' <- simplExp e2
        return $ BindE WildV tau' e1' e2' s

    go e1' tau' (TameV v) =
       extendVars [(bVar v, tau)] $
       withUniqBoundVar v $ \v' ->
       extendDefinitions [(bVar v', Unknown)] $ do
       e2' <- simplExp e2
       return $ BindE wv tau' e1' e2' s

return1 :: Monad m => a -> m [a]
return1 x = return [x]

isSimple :: Exp -> Bool
isSimple (ConstE {}) = True
isSimple (VarE {})   = True
isSimple _           = False

shouldInlineExpUnconditionally :: InExp -> SimplM Bool
shouldInlineExpUnconditionally e | isSimple e =
    asksFlags (testDynFlag MayInline)

shouldInlineExpUnconditionally _ =
    return False

shouldInlineFunUnconditionally :: [IVar]
                               -> [(Var, Type)]
                               -> Type
                               -> OutExp
                               -> SimplM Bool
shouldInlineFunUnconditionally _ _ _ e | isSimple e =
    asksFlags (testDynFlag MayInline)

shouldInlineFunUnconditionally _ _ _ _ =
    return False

shouldInlineCompUnconditionally :: InComp -> SimplM Bool
shouldInlineCompUnconditionally _ = do
  fuse <- asksFlags (testDynFlag Fuse)
  if fuse
    then return True
    else return False

shouldInlineCompFunUnconditionally :: [IVar]
                                   -> [(Var, Type)]
                                   -> Type
                                   -> OutComp
                                   -> SimplM Bool
shouldInlineCompFunUnconditionally _ _ _ _ = do
  fuse <- asksFlags (testDynFlag Fuse)
  if fuse
    then return True
    else return False
