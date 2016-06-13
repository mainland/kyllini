{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Fuse
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Fuse (
    fuseProgram
  ) where

#if MIN_VERSION_base(4,8,0)
import Control.Applicative (Alternative)
#else /* !MIN_VERSION_base(4,8,0) */
import Control.Applicative (Alternative, Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (MonadPlus(..),
                      guard,
                      when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO(..),
                               liftIO)
import Control.Monad.Logic.Class (MonadLogic(..),
                                  ifte)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor)
import Control.Monad.Trans (lift)
import Data.Foldable (toList)
import Data.Loc (srclocOf)
import Data.Map (Map)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Optimize.Simplify (simplComp)
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

type Joint l = (l, l)

data FEnv l = FEnv
    { kont      :: !l         -- Current continuation label
    , leftLoop  :: !(Maybe l) -- Label of left loop head
    , rightLoop :: !(Maybe l) -- Label of right loop head
    }

defaultFEnv :: (IsLabel l, MonadUnique m) => m (FEnv l)
defaultFEnv = do
    l <- gensym "end"
    return FEnv { kont      = l
                , leftLoop  = Nothing
                , rightLoop = Nothing
                }

newtype FState l = FState { seen :: Set (Joint l) }

defaultFState :: IsLabel l => FState l
defaultFState = FState mempty

data FusionStats = FusionStats
    { fusedPars      :: !Int
    , fusionFailures :: !Int
    }

instance Monoid FusionStats where
    mempty = FusionStats 0 0

    x `mappend` y = FusionStats
        { fusedPars      = fusedPars x + fusedPars y
        , fusionFailures = fusionFailures x + fusionFailures y
        }

instance Pretty FusionStats where
    ppr stats =
        text "     Fused pars:" <+> ppr (fusedPars stats) </>
        text "Fusion failures:" <+> ppr (fusionFailures stats)

newtype F l m a = F { unF :: ReaderT (FEnv l)
                               (WriterT (Seq (Step (Joint l)))
                                 (StateT (FState l)
                                   (SEFKT (StateT FusionStats m)))) a }
    deriving (Functor, Applicative, Monad,
              Alternative, MonadPlus,
              MonadIO,
              MonadReader (FEnv l),
              MonadWriter (Seq (Step (Joint l))),
              MonadState (FState l),
              MonadException,
              MonadLogic,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

runF :: forall l m a . (IsLabel l, MonadTc m)
     => F l m a
     -> m a
runF m = do
  env <- defaultFEnv
  fst <$> evalStateT (runSEFKT
                       (evalStateT
                         (runWriterT
                           (runReaderT (unF m) env))
                         defaultFState))
                     mempty

withKont :: (IsLabel l, MonadTc m) => [Step l] -> F l m a -> F l m a
withKont steps m = do
    klabel <- stepsLabel steps
    local (\env -> env { kont = klabel }) m

currentKont :: MonadTc m => F l m l
currentKont = asks kont

stepsLabel :: MonadTc m => [Step l] -> F l m l
stepsLabel []                    = currentKont
stepsLabel (RepeatC _ _ c _ : _) = stepsLabel (unComp c)
stepsLabel (step : _)            = stepLabel step

joint :: (IsLabel l, MonadTc m)
      => [Step l]
      -> [Step l]
      -> F l m (Joint l)
joint lss rss = (,) <$> stepsLabel lss <*> stepsLabel rss

jointStep :: (IsLabel l, MonadTc m) => Step (Joint l) -> F l m ()
jointStep step = do
    l <- stepLabel step
    recordLabel l
    tell (Seq.singleton step)

collectSteps :: MonadTc m => F l m a -> F l m (a, [Step (Joint l)])
collectSteps m =
    censor (const mempty) $ do
    (x, steps) <- listen m
    return (x, toList steps)

repeatLabel :: forall l m . MonadTc m => F l m (Maybe (Joint l))
repeatLabel = do
    maybe_left  <- asks leftLoop
    maybe_right <- asks rightLoop
    case (maybe_left, maybe_right) of
      (Just left, Just right) -> return $ Just (left, right)
      _                       -> return Nothing

runRepeat :: forall l m . (IsLabel l, MonadTc m)
          => [Step l]
          -> [Step l]
          -> (l -> l -> F l m [Step l])
          -> F l m [Step l]
runRepeat lss rss k = do
    l_repeat    <- repeatLabel
    l_left      <- stepsLabel lss
    l_right     <- stepsLabel rss
    let l_joint =  (l_left, l_right)
    saw         <- sawLabel l_joint
    if saw
      then do when (l_repeat /= Just l_joint) $ do
                traceFusion $ text "Unaligned repeat loops"
                fusionFailed
                mzero
              jointStep $ LoopC l_joint
              return []
      else do when (l_repeat == Just l_joint) $
                modify $ \s -> s { seen = mempty }
              k l_left l_right

leftRepeat :: (IsLabel l, MonadTc m)
           => [Step l]
           -> [Step l]
           -> F l m [Step l]
leftRepeat lss rss =
    runRepeat lss rss $ \l_left _ ->
    local (\env -> env { leftLoop = Just l_left }) $
    runLeft lss rss

rightRepeat :: (IsLabel l, MonadTc m)
            => [Step l]
            -> [Step l]
            -> F l m [Step l]
rightRepeat lss rss =
    runRepeat lss rss $ \_ l_right ->
    local (\env -> env { rightLoop = Just l_right }) $
    runRight lss rss

sawLabel :: (IsLabel l, MonadTc m)
         => Joint l -> F l m Bool
sawLabel l = gets (Set.member l . seen)

recordLabel :: (IsLabel l, MonadTc m)
            => Joint l -> F l m ()
recordLabel l = modify $ \s -> s { seen = Set.insert l (seen s) }

getStats :: MonadTc m => F l m FusionStats
getStats = F $ lift $ lift $ lift get

modifyStats :: MonadTc m => (FusionStats -> FusionStats) -> F l m ()
modifyStats = F . lift . lift . lift . modify

parFused :: MonadTc m => F l m ()
parFused =
    modifyStats $ \s -> s { fusedPars = fusedPars s + 1 }

fusionFailed :: MonadTc m => F l m ()
fusionFailed =
    modifyStats $ \s -> s { fusionFailures = fusionFailures s + 1 }

fuseProgram :: forall l m . (IsLabel l, MonadPlus m, MonadIO m, MonadTc m)
            => Program l -> m (Program l)
fuseProgram = runF . fuseProg
  where
    fuseProg :: Program l -> F l m (Program l)
    fuseProg prog = do
        prog'     <- programT prog
        dumpStats <- asksFlags (testDynFlag ShowFusionStats)
        when dumpStats $ do
            stats  <- getStats
            liftIO $ putDocLn $ nest 2 $
                text "Fusion statistics:" </> ppr stats
        return prog'

instance (IsLabel l, MonadTc m) => TransformExp (F l m) where

instance (IsLabel l, MonadTc m) => TransformComp l (F l m) where
  stepsT (ParC ann b c1 c2 sloc : steps) = do
      (s, a, c) <- askSTIndTypes
      c1'       <- localSTIndTypes (Just (s, a, b)) $
                   compT c1
      c2'       <- localSTIndTypes (Just (b, b, c)) $
                   compT c2
      steps1    <- ifte (fusePar c1' c2')
                        return
                        (return [ParC ann b c1' c2' sloc])
      steps'    <- stepsT steps
      return $ steps1 ++ steps'
    where
      fusePar :: Comp l -> Comp l -> F l m [Step l]
      fusePar left right0 = do
          traceFusion $ text "Attempting to fuse" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right)
          l    <- compLabel right0
          comp <- withKont steps $
                  fuse left right >>=
                  recoverRepeat >>=
                  setFirstLabel l >>=
                  simplComp
          parFused
          traceFusion $ text "Fused" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right) </>
              text "into:" </> indent 2 (ppr comp)
          return $ unComp comp
        where
          -- We need to make sure that the producer and consumer have unique
          -- sets of binders, so we freshen all binders in the consumer. Why the
          -- consumer? Because >>> is left-associative, so we hopefully avoid
          -- repeated re-naming of binders by renaming the consumer.
          right :: Comp l
          right = unquify right0

          unquify :: Subst Exp Var a => a -> a
          unquify = subst (mempty :: Map Var Exp) (allVars left :: Set Var)

          setFirstLabel :: l -> Comp l -> F l m (Comp l)
          setFirstLabel l' comp = do
              l <- compLabel comp
              return $ subst1 (l /-> l') comp

  stepsT steps =
      transSteps steps

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    (_, rss') <- collectSteps $ runRight (unComp left) (unComp right)
    return $ jointLabel <$> mkComp rss'

runRight :: forall l m . (IsLabel l, MonadTc m)
         => [Step l]
         -> [Step l]
         -> F l m [Step l]
runRight lss [] =
    return lss

runRight lss (rs@(IfC _l e c1 c2 s) : rss) =
    ifte joinIf
         (\lss' -> runRight lss' rss)
         divergeIf
  where
    joinIf :: F l m [Step l]
    joinIf = do
        l'          <- joint lss (rs:rss)
        (lss1, c1') <- collectSteps $
                       withKont rss $
                       runRight lss (unComp c1)
        (lss2, c2') <- collectSteps $
                       withKont rss $
                       runRight lss (unComp c2)
        guardConvergence lss1 lss2
        jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
        return lss1

    divergeIf :: F l m [Step l]
    divergeIf = do
        l'       <- joint lss (rs:rss)
        (_, c1') <- collectSteps $ runRight lss (unComp c1 ++ rss)
        (_, c2') <- collectSteps $ runRight lss (unComp c2 ++ rss)
        jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
        return []

runRight lss (rs@(WhileC _l e c s) : rss) =
    ifte joinWhile
         (const $ runRight lss rss)
         divergeWhile
  where
    joinWhile :: F l m ()
    joinWhile = do
        l'         <- joint lss (rs:rss)
        (lss', c') <- collectSteps $
                      withKont rss $
                      runRight lss (unComp c)
        guardConvergence lss lss'
        jointStep $ WhileC l' e (mkComp c') s

    divergeWhile :: F l m [Step l]
    divergeWhile = do
        traceFusion $ text "Encountered diverging while in consumer"
        fusionFailed
        mzero

-- See the comment in the ForC case for runLeft.
runRight lss (rs@(ForC _ ann v tau e1 e2 c s) : rss) =
    ifte joinFor
         (const $ runRight lss rss)
         divergeFor
  where
    joinFor :: F l m ()
    joinFor = do
        l'            <- joint lss (rs:rss)
        (lss', steps) <- collectSteps $
                         withKont rss $
                         runRight lss (unComp c)
        guardConvergence lss lss'
        jointStep $ ForC l' ann v tau e1 e2 (mkComp steps) s

    divergeFor :: F l m [Step l]
    divergeFor = do
        traceFusion $ text "Encountered diverging for in consumer"
        fusionFailed
        mzero

runRight lss rss@(TakeC{} : _) =
    runLeft lss rss

runRight lss rss@(TakesC{} : _) =
    runLeft lss rss

runRight lss rss@(RepeatC _ _ c _ : _) =
    rightRepeat lss (unComp c ++ rss)

runRight _lss (ParC{} : _rss) =
    nestedPar

runRight lss (rs:rss) = do
    l' <- joint lss (rs:rss)
    relabelStep l' rs $
      runRight lss rss

runLeft :: forall l m . (IsLabel l, MonadTc m)
        => [Step l]
        -> [Step l]
        -> F l m [Step l]
runLeft [] rss =
    return rss

runLeft (ls@(IfC _l e c1 c2 s) : lss) rss =
    ifte joinIf
         (\rss' -> runLeft lss rss')
         divergeIf
  where
    joinIf :: F l m [Step l]
    joinIf = do
        l'          <- joint (ls:lss) rss
        (rss1, c1') <- collectSteps $
                       withKont lss $
                       runLeft (unComp c1) rss
        (rss2, c2') <- collectSteps $
                       withKont lss $
                       runLeft (unComp c2) rss
        guardConvergence rss1 rss2
        jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
        return rss1

    divergeIf :: F l m [Step l]
    divergeIf = do
        l'       <- joint (ls:lss) rss
        (_, c1') <- collectSteps $ runLeft (unComp c1 ++ lss) rss
        (_, c2') <- collectSteps $ runLeft (unComp c2 ++ lss) rss
        jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
        return []

runLeft (ls@(WhileC _l e c s) : lss) rss =
    ifte joinWhile
         (const $ runLeft lss rss)
         divergeWhile
  where
    joinWhile :: F l m ()
    joinWhile = do
        l'         <- joint (ls:lss) rss
        (rss', c') <- collectSteps $
                      withKont lss $
                      runLeft (unComp c) rss
        guardConvergence rss rss'
        jointStep $ WhileC l' e (mkComp c') s

    divergeWhile :: F l m [Step l]
    divergeWhile = do
        traceFusion $ text "Encountered diverging while in producer"
        fusionFailed
        mzero

-- We attempt to fuse a for loop by running the body of the for with the
-- consumer. If we end up back where we started in the consumer's
-- computation, that means we can easily construct a new for loop whose body
-- is the body of the producer's for loop merged with the consumer. This
-- typically works when the consumer is a repeated computation.
runLeft (ls@(ForC _ ann v tau e1 e2 c s) : lss) rss =
    ifte joinFor
         (const $ runLeft lss rss)
         divergeFor
  where
    joinFor :: F l m ()
    joinFor = do
        l'            <- joint (ls:lss) rss
        (rss', steps) <- collectSteps $
                         withKont lss $
                         runLeft (unComp c) rss
        guardConvergence rss rss'
        jointStep $ ForC l' ann v tau e1 e2 (mkComp steps) s

    divergeFor :: F l m [Step l]
    divergeFor = do
        traceFusion $ text "Encountered diverging for in producer"
        fusionFailed
        mzero

runLeft (EmitC _ e _ : lss) (TakeC{} : rss) =
    emitTake e lss rss

runLeft (ls@EmitC{} : _) (rs@TakesC{} : _) = do
    traceFusion $ ppr ls <+> text "paired with" <+> ppr rs
    fusionFailed
    mzero

runLeft (EmitC{} : _) _ =
    faildoc $ text "emit paired with non-take."

runLeft (EmitsC _ e _ : lss) (rs@TakeC{} : rss) = do
    -- We can only fuse an emits and a take when we statically know the
    -- size of the array being emitted.
    n <- inferExp e >>= knownArraySize
    if n == 1
      then emitTake (idxE e 0) lss rss
      else emitsNTake n
  where
    -- If we are emitting an array with more than one element, we rewrite
    -- the emits as a for loop that yields each element of the array one by
    -- one and try to fuse the rewritten computation.
    emitsNTake :: Int -> F l m [Step l]
    emitsNTake n = do
        body <- runK $ forC 0 n $ \i -> emitC (idxE e i)
        runLeft (unComp body ++ lss) (rs:rss)

runLeft (EmitsC _ e _ : lss) (rs@(TakesC _ n' _ _) : rss) = do
    n <- inferExp e >>= knownArraySize
    when (n' /= n) $ do
        (iota, _) <- inferExp e >>= checkArrT
        traceFusion $ text "emits" <+> ppr iota <+> text "paired with" <+>
                      ppr rs
        fusionFailed
        mzero
    emitTake e lss rss

runLeft (EmitsC{} : _) _ =
    faildoc $ text "emits paired with non-take."

runLeft lss@(RepeatC _ _ c _ : _) rss =
    leftRepeat (unComp c ++ lss) rss

runLeft (ParC{} : _lss) _rss =
    nestedPar

runLeft (ls:lss) rss = do
    l' <- joint (ls:lss) rss
    relabelStep l' ls $
      runLeft lss rss

-- | Run the right side of a par when we've hit a emit/take combination.
emitTake :: forall l m . (IsLabel l, MonadTc m)
         => Exp
         -> [Step l]
         -> [Step l]
         -> F l m [Step l]
emitTake e lss rss =
    runRight (bind unitE lss) (bind e rss)
  where
    bind :: Exp -> [Step l] -> [Step l]
    bind _e (BindC _l WildV    _tau _ : ss) = ss
    bind  e (BindC l (TameV v)  tau s : ss) = LetC l (LetLD v tau e s) s : ss
    bind _e                             ss  = ss

-- | Indicate that a nested par was encountered during fusion.
nestedPar :: MonadTc m => F l m a
nestedPar = do
    traceFusion $ text "Saw nested par in producer during par fusion."
    fusionFailed
    mzero

knownArraySize :: MonadTc m => Type -> F l m Int
knownArraySize tau = do
    (iota, _) <- checkArrT tau
    case iota of
      ConstI n _ -> return n
      _          -> do traceFusion $ text "Unknown array size"
                       fusionFailed
                       mzero

{- Note [Convergence]

When fusing loops and if-the-else computations, we test for convergence of the
"other" side of the par we're fusing. For example, we test that the two branches
of an if, when run, end up at the same point in the computation on the other
side of the par. Similarly, we test that the body of a loop ends up at the same
point in the other side of the computation as it started---if so, we can
directly output a loop as part of the fused computation.

We used to test for equality of the two computations, but now we just test for
the equality of their label.
-}

-- | Guard the convergence of two branches of computation.
guardConvergence :: (IsLabel l, MonadPlus m)
                 => [Step l]
                 -> [Step l]
                 -> m ()
guardConvergence ss ss' = guard (stepsLabel ss' == stepsLabel ss)
  where
    stepsLabel :: [Step l] -> Maybe l
    stepsLabel []       = Nothing
    stepsLabel (step:_) = stepLabel step

{- Note [Fusing Repeat]

We fuse repeat by unrolling the repeat loop on demand.

The only time that fusion will produce a repeat loop is when both sides of the
par are repeats. We detect a loop by keeping track of the labels of all fused
steps that have been produced so far and inserting a `LoopC` construct when we
encounter a step we have seen before *and* we are in a state where both the left
and right sides of the par are at a loop header.

We need to make sure that both computations are at a loop header because
otherwise we can end up in a situation where the fused loop starts halfway
through the body of one of the two loops being fused, meaning the binders that
occurred earlier in the loop body are not valid!

The `LoopC` will be removed by `recoverRepeat`, which we use to process every
fused computation. Because a repeat must be a terminal computation, i.e.,
nothing can come after it, a `LoopC` will only ever be present at the end of a
fused computation. This makes it easy to find and turn into a new, fused repeat
construct.
-}

recoverRepeat :: forall l m . (IsLabel l, MonadUnique m)
              => Comp l
              -> m (Comp l)
recoverRepeat comp =
    case last steps of
      LoopC l -> mkComp <$> recover l (init steps)
      _       -> return $ mkComp steps
  where
    steps :: [Step l]
    steps = unComp comp

    recover :: l -> [Step l] -> m [Step l]
    recover _ [] =
        return []

    recover l (step:steps) | stepLabel step == Just l =
        (: []) <$> repeatC (mkComp (step:steps))

    recover l (step:steps) =
        (step :) <$> recover l steps

    repeatC :: Comp l -> m (Step l)
    repeatC c = do
        l <- gensym "repeatk"
        return $ RepeatC l AutoVect c (srclocOf c)

relabelStep :: (IsLabel l, MonadTc m)
            => Joint l
            -> Step l
            -> F l m a
            -> F l m a
relabelStep _ step@VarC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw variable bound to a computation during fusion"

relabelStep _ step@CallC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw call to a computation function during fusion"

relabelStep l (LetC _ decl@(LetLD v tau _ _) s) k =
    extendVars [(bVar v, tau)] $ do
    jointStep $ LetC l decl s
    k

relabelStep l (LetC _ decl@(LetRefLD v tau _ _) s) k =
    extendVars [(bVar v, refT tau)] $ do
    jointStep $ LetC l decl s
    k

relabelStep l (LiftC _ e s) k = do
    jointStep $ LiftC l e s
    k

relabelStep l (ReturnC _ e s) k = do
    jointStep $ ReturnC l e s
    k

relabelStep l (BindC _ wv tau s) k =
    extendWildVars [(wv, tau)] $ do
    jointStep $ BindC l wv tau s
    k

relabelStep l (TakeC _ tau s) k = do
    jointStep $ TakeC l tau s
    k

relabelStep l (TakesC _ i tau s) k = do
    jointStep $ TakesC l i tau s
    k

relabelStep l (EmitC _ e s) k = do
    jointStep $ EmitC l e s
    k

relabelStep l (EmitsC _ e s) k = do
    jointStep $ EmitsC l e s
    k

relabelStep _ _ _k =
    fail "relabelStep: can't happen"
