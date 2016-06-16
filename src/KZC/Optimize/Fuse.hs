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
                      unless,
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
    { leftKont  :: !l -- Current left continuation label
    , rightKont :: !l -- Current right continuation label
    }

defaultFEnv :: (IsLabel l, MonadUnique m) => m (FEnv l)
defaultFEnv = do
    l <- gensym "end"
    return FEnv { leftKont  = l
                , rightKont = l
                }

data FState l = FState
    { seen          :: !(Set (Joint l))   -- All seen labels
    , loopHead      :: !(Maybe (Joint l)) -- Label of loop head
    , leftLoopHead  :: !(Maybe l)         -- Label of head of left repeat
    , rightLoopHead :: !(Maybe l)         -- Label of head of right repeat
    }

defaultFState :: IsLabel l => FState l
defaultFState = FState
    { seen          = mempty
    , loopHead      = Nothing
    , leftLoopHead  = Nothing
    , rightLoopHead = Nothing
    }

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

withLeftKont :: (IsLabel l, MonadTc m) => [Step l] -> F l m a -> F l m a
withLeftKont steps m = do
    klabel <- leftStepsLabel steps
    local (\env -> env { leftKont = klabel }) m

withRightKont :: (IsLabel l, MonadTc m) => [Step l] -> F l m a -> F l m a
withRightKont steps m = do
    klabel <- rightStepsLabel steps
    local (\env -> env { rightKont = klabel }) m

leftStepsLabel :: MonadTc m => [Step l] -> F l m l
leftStepsLabel []                    = asks leftKont
leftStepsLabel (RepeatC _ _ c _ : _) = leftStepsLabel (unComp c)
leftStepsLabel (step : _)            = stepLabel step

rightStepsLabel :: MonadTc m => [Step l] -> F l m l
rightStepsLabel []                    = asks rightKont
rightStepsLabel (RepeatC _ _ c _ : _) = rightStepsLabel (unComp c)
rightStepsLabel (step : _)            = stepLabel step

joint :: (IsLabel l, MonadTc m)
      => [Step l]
      -> [Step l]
      -> F l m (Joint l)
joint lss rss = (,) <$> leftStepsLabel lss <*> rightStepsLabel rss

jointStep :: (IsLabel l, MonadTc m)
          => Step (Joint l)
          -> F l m [Step l]
          -> F l m [Step l]
jointStep step k = do
    l_repeat <- repeatLabel
    l_joint  <- stepLabel step
    whenVerbLevel 2 $ traceFusion $
        text "jointStep:" <+> ppr l_joint <> colon </> ppr (jointLabel <$> step)
    saw <- sawLabel l_joint
    if saw
      then do when (l_repeat /= Just l_joint)
                unalignedRepeats
              modify $ \s -> s { loopHead = Just l_joint }
              return []
      else do when (l_repeat == Just l_joint) $
                modify $ \s -> s { seen = mempty }
              recordLabel l_joint
              tell (Seq.singleton step)
              k

collectSteps :: MonadTc m => F l m a -> F l m (a, [Step (Joint l)])
collectSteps m =
    censor (const mempty) $ do
    (x, steps) <- listen m
    return (x, toList steps)

repeatLabel :: forall l m . MonadTc m => F l m (Maybe (Joint l))
repeatLabel = do
    maybe_left  <- gets leftLoopHead
    maybe_right <- gets rightLoopHead
    case (maybe_left, maybe_right) of
      (Just left, Just right) -> return $ Just (left, right)
      _                       -> return Nothing

leftRepeat :: (IsLabel l, MonadTc m)
           => Comp l
           -> F l m ()
leftRepeat c = do
    l <- leftStepsLabel (unComp c)
    modify $ \s -> s { leftLoopHead = Just l }

rightRepeat :: (IsLabel l, MonadTc m)
            => Comp l
            -> F l m ()
rightRepeat c = do
    l <- rightStepsLabel (unComp c)
    modify $ \s -> s { rightLoopHead = Just l }

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
      fusePar left0 right0 = do
          traceFusion $ text "Attempting to fuse" <+>
              text "producer:" </> indent 2 (ppr left0) </>
              text "and consumer:" </> indent 2 (ppr right0)
          -- We need to make sure that the producer and consumer have unique
          -- sets of binders, so we freshen all binders in the consumer. Why the
          -- consumer? Because >>> is left-associative, so we hopefully avoid
          -- repeated re-naming of binders by renaming the consumer.
          left  <- unrollEmits left0
          right <- alphaRename (allVars left) <$> unrollTakes right0
          l     <- compLabel right0
          comp  <- withLeftKont steps $
                   withRightKont steps $
                   fuse left right >>=
                   return . setCompLabel l >>=
                   simplComp
          parFused
          traceFusion $ text "Fused" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right) </>
              text "into:" </> indent 2 (ppr comp)
          return $ unComp comp

  stepsT steps =
      transSteps steps

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    (_, steps) <- collectSteps $
                  runRight (unComp left) (unComp right)
    maybe_l    <- gets loopHead
    let comp   =  mkComp steps
    case maybe_l of
      Nothing -> return $ jointLabel <$> comp
      Just l  -> recoverRepeat l comp

runRight :: forall l m . (IsLabel l, MonadTc m)
         => [Step l]
         -> [Step l]
         -> F l m [Step l]
runRight lss [] =
    return lss

runRight lss (rs@(IfC _l e c1 c2 s) : rss) =
    ifte joinIf
         (\(step, lss') -> jointStep step $ runRight lss' rss)
         divergeIf
  where
    joinIf :: F l m (Step (Joint l), [Step l])
    joinIf = do
        l'          <- joint lss (rs:rss)
        (lss1, c1') <- collectSteps $
                       withRightKont rss $
                       runRight lss (unComp c1)
        (lss2, c2') <- collectSteps $
                       withRightKont rss $
                       runRight lss (unComp c2)
        guardLeftConvergence lss1 lss2
        return (IfC l' e (mkComp c1') (mkComp c2') s, lss1)

    divergeIf :: F l m [Step l]
    divergeIf = do
        l'       <- joint lss (rs:rss)
        (_, c1') <- collectSteps $ runRight lss (unComp c1 ++ rss)
        (_, c2') <- collectSteps $ runRight lss (unComp c2 ++ rss)
        jointStep (IfC l' e (mkComp c1') (mkComp c2') s) $
          return []

runRight lss (rs@(WhileC _l e c s) : rss) =
    ifte joinWhile
         (\step -> jointStep step $ runRight lss rss)
         divergeWhile
  where
    joinWhile :: F l m (Step (Joint l))
    joinWhile = do
        l'         <- joint lss (rs:rss)
        (lss', c') <- collectSteps $
                      withRightKont rss $
                      runRight lss (unComp c)
        guardLeftConvergence lss lss'
        return $ WhileC l' e (mkComp c') s

    divergeWhile :: F l m [Step l]
    divergeWhile = do
        traceFusion $ text "Encountered diverging while in consumer"
        fusionFailed
        mzero

-- See Note [Fusing For Loops]
runRight lss (rs@(ForC l ann v tau e1 e2 c s) : rss) =
    ifte joinFor
         (\step -> jointStep step $ runRight lss rss)
         divergeFor
  where
    joinFor :: F l m (Step (Joint l))
    joinFor = do
        l'            <- joint lss (rs:rss)
        (lss', steps) <- collectSteps $
                         withRightKont rss $
                         runRight lss (unComp c)
        guardLeftConvergence lss lss'
        return $ ForC l' ann v tau e1 e2 (mkComp steps) s

    divergeFor :: F l m [Step l]
    divergeFor = do
        unrollingFor
        unrolled <- unrollFor l v e1 e2 c
        runRight lss (unComp unrolled ++ rss)

runRight lss rss@(TakeC{} : _) =
    runLeft lss rss

runRight _ (TakesC{} : _) =
    faildoc $ text "Saw takes in consumer."

runRight lss rss@(RepeatC _ _ c _ : _) =
    withRightKont rss $ do
    rightRepeat c
    runRight lss (unComp c ++ rss)

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
         (\(step, rss') -> jointStep step $ runLeft lss rss')
         divergeIf
  where
    joinIf :: F l m (Step (Joint l), [Step l])
    joinIf = do
        l'          <- joint (ls:lss) rss
        (rss1, c1') <- collectSteps $
                       withLeftKont lss $
                       runLeft (unComp c1) rss
        (rss2, c2') <- collectSteps $
                       withLeftKont lss $
                       runLeft (unComp c2) rss
        guardRightConvergence rss1 rss2
        return (IfC l' e (mkComp c1') (mkComp c2') s, rss1)

    divergeIf :: F l m [Step l]
    divergeIf = do
        l'       <- joint (ls:lss) rss
        (_, c1') <- collectSteps $ runLeft (unComp c1 ++ lss) rss
        (_, c2') <- collectSteps $ runLeft (unComp c2 ++ lss) rss
        jointStep (IfC l' e (mkComp c1') (mkComp c2') s) $
          return []

runLeft (ls@(WhileC _l e c s) : lss) rss =
    ifte joinWhile
         (\step -> jointStep step $ runLeft lss rss)
         divergeWhile
  where
    joinWhile :: F l m (Step (Joint l))
    joinWhile = do
        l'         <- joint (ls:lss) rss
        (rss', c') <- collectSteps $
                      withLeftKont lss $
                      runLeft (unComp c) rss
        guardRightConvergence rss rss'
        return $ WhileC l' e (mkComp c') s

    divergeWhile :: F l m [Step l]
    divergeWhile = do
        traceFusion $ text "Encountered diverging while in producer"
        fusionFailed
        mzero

-- See Note [Fusing For Loops]
runLeft (ls@(ForC l ann v tau e1 e2 c s) : lss) rss =
    ifte joinFor
         (\step -> jointStep step $ runLeft lss rss)
         divergeFor
  where
    joinFor :: F l m (Step (Joint l))
    joinFor = do
        l'            <- joint (ls:lss) rss
        (rss', steps) <- collectSteps $
                         withLeftKont lss $
                         runLeft (unComp c) rss
        guardRightConvergence rss rss'
        return $ ForC l' ann v tau e1 e2 (mkComp steps) s

    divergeFor :: F l m [Step l]
    divergeFor = do
        unrollingFor
        unrolled <- unrollFor l v e1 e2 c
        runLeft (unComp unrolled ++ lss) rss

runLeft lss@(EmitC _ e _ : _) rss@(TakeC{} : _) =
    emitTake e lss rss

runLeft (ls@EmitC{} : _) (rs@TakesC{} : _) = do
    traceFusion $ ppr ls <+> text "paired with" <+> ppr rs
    fusionFailed
    mzero

runLeft (EmitC{} : _) _ =
    faildoc $ text "emit paired with non-take."

runLeft (EmitsC{} : _) _ =
    faildoc $ text "Saw emits in producer."

runLeft lss@(RepeatC _ _ c _ : _) rss =
    withLeftKont lss $ do
    leftRepeat c
    runLeft (unComp c ++ lss) rss

runLeft (ParC{} : _lss) _rss =
    nestedPar

runLeft (ls:lss) rss = do
    l' <- joint (ls:lss) rss
    relabelStep l' ls $
      runLeft lss rss

-- | Add a step to the fused computation after re-labeling it with the given
-- label, and then execute the continuation ensuring that the step's binders
-- scope over it.
relabelStep :: (IsLabel l, MonadTc m)
            => Joint l
            -> Step l
            -> F l m [Step l]
            -> F l m [Step l]
relabelStep _ step@VarC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw variable bound to a computation during fusion"

relabelStep _ step@CallC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw call to a computation function during fusion"

relabelStep l (LetC _ decl@(LetLD v tau _ _) s) k =
    extendVars [(bVar v, tau)] $
    jointStep (LetC l decl s) k

relabelStep l (LetC _ decl@(LetRefLD v tau _ _) s) k =
    extendVars [(bVar v, refT tau)] $
    jointStep (LetC l decl s) k

relabelStep l (LiftC _ e s) k =
    jointStep (LiftC l e s) k

relabelStep l (ReturnC _ e s) k =
    jointStep (ReturnC l e s) k

relabelStep l (BindC _ wv tau s) k =
    extendWildVars [(wv, tau)] $
    jointStep (BindC l wv tau s) k

relabelStep l (TakeC _ tau s) k =
    jointStep (TakeC l tau s) k

relabelStep l (TakesC _ i tau s) k =
    jointStep (TakesC l i tau s) k

relabelStep l (EmitC _ e s) k =
    jointStep (EmitC l e s) k

relabelStep l (EmitsC _ e s) k =
    jointStep (EmitsC l e s) k

relabelStep _ _ _k =
    fail "relabelStep: can't happen"

-- | Run the right side of a par when we've hit a emit/take combination.
emitTake :: forall l m . (IsLabel l, MonadTc m)
         => Exp
         -> [Step l]
         -> [Step l]
         -> F l m [Step l]
emitTake e lss rss = do
    l                <- joint lss rss
    let lss'         =  bindIn unitE (tail lss)
    let (step, rss') =  bindAnd l e (tail rss)
    jointStep step $
      runRight lss' rss'
  where
    bindIn :: Exp -> [Step l] -> [Step l]
    bindIn _e (BindC _l WildV    _   _ : ss) = ss
    bindIn  e (BindC l (TameV v) tau _ : ss) = letC l v tau e : ss
    bindIn _e                            ss  = ss

    bindAnd :: Joint l -> Exp -> [Step l] -> (Step (Joint l), [Step l])
    bindAnd l e (BindC _ (TameV v) tau _ : ss) = (letC l v tau e, ss)
    bindAnd l _ (BindC _ WildV     _   _ : ss) = (returnC l unitE, ss)
    bindAnd l _                            ss  = (returnC l unitE, ss)

    letC :: l' -> BoundVar -> Type -> Exp -> Step l'
    letC l v tau e = LetC l (LetLD v tau e (srclocOf e)) (srclocOf e)

    returnC :: l' -> Exp -> Step l'
    returnC l e = ReturnC l e (srclocOf e)

-- | Indicate that a nested par was encountered during fusion.
nestedPar :: MonadTc m => F l m a
nestedPar = do
    traceFusion $ text "Saw nested par in producer during par fusion."
    fusionFailed
    mzero

-- | Indicate that we are unrolling a for loop during fusion. This will fail
-- unless the appropriate flag has been specified.
unrollingFor :: MonadTc m => F l m ()
unrollingFor = do
    doUnroll <- asksFlags (testDynFlag FuseUnroll)
    unless doUnroll $ do
        traceFusion $ text "Encountered diverging loop during fusion."
        mzero

unalignedRepeats :: MonadTc m => F l m ()
unalignedRepeats = do
    traceFusion $ text "Unaligned repeat loops"
    fusionFailed
    mzero

-- | Alpha-rename binders given an in-scope set of binders.
alphaRename :: Subst Exp Var a => Set Var -> a -> a
alphaRename = subst (mempty :: Map Var Exp)

-- | Return the given array type's size, which must be statically known.
knownArraySize :: MonadTc m => Type -> m Int
knownArraySize tau = do
    (iota, _) <- checkArrT tau
    case iota of
      ConstI n _ -> return n
      _          -> fail "Unknown emitted array size"

-- | Attempt to extract a constant integer from an 'Exp'.
tryFromIntE :: (MonadPlus m, MonadTrace m) => Exp -> m Int
tryFromIntE (ConstE c _) = fromIntC c
tryFromIntE _            = do traceFusion $ text "Non-constant for loop bound"
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

-- | Guard the convergence of two left branches of computation.
guardLeftConvergence :: (IsLabel l, MonadTc m)
                     => [Step l]
                     -> [Step l]
                     -> F l m ()
guardLeftConvergence lss lss' = do
    l  <- leftStepsLabel lss
    l' <- leftStepsLabel lss'
    when (l' /= l) $
        traceFusion $ text "Left branches did not converge"
    guard (l' == l)

-- | Guard the convergence of two right branches of computation.
guardRightConvergence :: (IsLabel l, MonadTc m)
                     => [Step l]
                     -> [Step l]
                     -> F l m ()
guardRightConvergence rss rss' = do
    l  <- rightStepsLabel rss
    l' <- rightStepsLabel rss'
    when (l' /= l) $
        traceFusion $ text "Right branches did not converge"
    guard (l' == l)

{- Note [Fusing Repeat]

We fuse repeat by unrolling the repeat loop on demand.

The only time that fusion will produce a repeat loop is when both sides of the
par are repeats. We detect a loop by keeping track of the labels of all fused
steps that have been produced so far and recording the loop header label when we
encounter a step we have seen before *and* we are in a state where both the left
and right sides of the par are at a loop header.

We need to make sure that both computations are at a loop header because
otherwise we can end up in a situation where the fused loop starts halfway
through the body of one of the two loops being fused, meaning the binders that
occurred earlier in the loop body are not valid!

When we detect a loop, we save the loop's label, which is then used by
`recoverRepeat` to recover the loop.
-}

recoverRepeat :: forall l m . (IsLabel l, MonadTc m)
              => Joint l
              -> Comp (Joint l)
              -> m (Comp l)
recoverRepeat l comp =
    go (unComp comp) []
  where
    go :: [Step (Joint l)] -- ^ Remaining steps in the computation
       -> [Step (Joint l)] -- ^ Prefix (reversed) of the computation
       -> m (Comp l)
    go [] prefix =
        return $ jointLabel <$> mkComp (reverse prefix)

    go (step:steps) prefix | stepLabel step == Just l = do
        l_repeat <- gensym "repeatk"
        return $ (jointLabel <$> mkComp (reverse prefix)) <>
                 mkComp [RepeatC l_repeat AutoVect c (srclocOf c)]
      where
        c :: Comp l
        c = jointLabel <$> mkComp (step:steps)

    go (step:steps) prefix =
        go steps (step:prefix)

{- Note [Fusing For Loops]

We first attempt to fuse a for loop by fusing the body of the for with the other
side of the par. If, after running the body, we end up back where we started in
the other computation, that means we can easily construct a new for loop whose
body is the fusion of the body with the other side of the par. This typically
works when the other computation is a repeat.

If that doesn't work, we then completely unroll the loop. We need to be careful
to re-label the steps in the peeled loop bodies, but we must also maintain the
label of the first step so that it matches the label of the loop. Maintaining
the initial label is necessary to allow accurate determination of the next
computational step.
-}

unrollFor :: forall l m . (IsLabel l, MonadTc m)
          => l
          -> Var
          -> Exp
          -> Exp
          -> Comp l
          -> F l m (Comp l)
unrollFor l v e1 e2 c = do
    i   <- tryFromIntE e1
    len <- tryFromIntE e2
    return $ setCompLabel l $ unrollBody i len $ \j -> subst1 (v /-> intE j) c

unrollBody :: IsLabel l
           => Int
           -> Int
           -> (Int -> Comp l)
           -> Comp l
unrollBody z n f =
    mconcat [indexLabel i <$> f i | i <- [z..(z+n-1)]]

{- Note [Unrolling takes and emits]

These are two small program transformartions that convert takes and emits into
for loops whose bodies do nothing except take/emit. This allows us to use the
usual fusion mechanisms to handle takes and emits. After fusion, we convert
loops of take/emit back into single takes/emits.
-}

unrollTakes :: (IsLabel l, MonadPlus m, MonadTc m)
            => Comp l -> m (Comp l)
unrollTakes = runUT . compT

newtype UT m a = UT { runUT :: m a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadFlags,
            MonadTrace,
            MonadTc)

instance MonadTc m => TransformExp (UT m) where

instance (IsLabel l, MonadTc m) => TransformComp l (UT m) where
    stepsT (TakesC _ n tau _ : steps) = do
        comp  <- runK $
                 letrefC "xs" (arrKnownT n tau) $ \xs -> do
                 forC 0 n $ \i -> do
                   x <- takeC tau
                   liftC $ assignE (idxE xs i) x
                 liftC $ derefE xs
        steps' <- stepsT steps
        return $ unComp comp ++ steps'

    stepsT steps =
        transSteps steps

unrollEmits :: (IsLabel l, MonadPlus m, MonadTc m)
            => Comp l -> m (Comp l)
unrollEmits = runUE . compT

newtype UE m a = UE { runUE :: m a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadFlags,
            MonadTrace,
            MonadTc)

instance MonadTc m => TransformExp (UE m) where

instance (IsLabel l, MonadTc m) => TransformComp l (UE m) where
    stepsT (EmitsC _ e _ : steps) = do
        n      <- inferExp e >>= knownArraySize
        comp   <- runK $
                  forC 0 n $ \i ->
                    emitC (idxE e i)
        steps' <- stepsT steps
        return $ unComp comp ++ steps'

    stepsT steps =
        transSteps steps
