{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
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
                      void,
                      when,
                      zipWithM)
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
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import KZC.Analysis.Rate
import qualified KZC.Core.Comp as C
import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Name
import KZC.Optimize.Simplify (simplComp)
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

data Joint l = JointL l l
             | NewL l
  deriving (Eq, Ord, Read, Show)

collapseJoint :: IsLabel l => Joint l -> l
collapseJoint (JointL l1 l2) = jointLabel l1 l2
collapseJoint (NewL l)       = l

instance IsString l => IsString (Joint l) where
    fromString s = NewL (fromString s)

instance Pretty l => Pretty (Joint l) where
    ppr (JointL l1 l2) = ppr (l1, l2)
    ppr (NewL l)       = ppr l

instance IsLabel l => C.ToIdent (Joint l) where
    toIdent = C.toIdent . collapseJoint

instance IsLabel l => Gensym (Joint l) where
    gensym s = NewL <$> gensym s

    uniquify l = NewL <$> uniquify (collapseJoint l)

instance Ord l => Fvs (Joint l) (Joint l) where
    fvs = singleton

instance Ord l => Subst (Joint l) (Joint l) (Joint l) where
    substM x (theta, _) = fromMaybe x (Map.lookup x theta)

instance IsLabel l => IsLabel (Joint l) where
    indexLabel i l   = NewL $ indexLabel i (collapseJoint l)
    jointLabel l1 l2 = NewL $ jointLabel (collapseJoint l1) (collapseJoint l2)

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
joint lss rss = JointL <$> leftStepsLabel lss <*> rightStepsLabel rss

jointStep :: (IsLabel l, MonadTc m)
          => Step (Joint l)
          -> F l m [Step l]
          -> F l m [Step l]
jointStep step k = do
    l_repeat <- repeatLabel
    l_joint  <- stepLabel step
    whenVerbLevel 2 $ traceFusion $
        text "jointStep:" <+> ppr l_joint <> colon </> ppr step
    saw <- sawLabel l_joint
    if saw
      then do when (l_repeat /= Just l_joint)
                unalignedRepeats
              setLoopHead l_joint
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

setLoopHead :: MonadTc m => Joint l -> F l m ()
setLoopHead l = modify $ \s -> s { loopHead = Just l }

collectLoopHead :: MonadTc m => F l m a -> F l m (a, Maybe (Joint l))
collectLoopHead m = do
    old_loopHead <- gets loopHead
    modify $ \s -> s { loopHead = Nothing }
    x <- m
    l <- gets loopHead
    modify $ \s -> s { loopHead = old_loopHead }
    return (x, l)

repeatLabel :: forall l m . MonadTc m => F l m (Maybe (Joint l))
repeatLabel = do
    maybe_left  <- gets leftLoopHead
    maybe_right <- gets rightLoopHead
    case (maybe_left, maybe_right) of
      (Just left, Just right) -> return $ Just $ JointL left right
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
                        (fusionFailed c1' c2' >> return [ParC ann b c1' c2' sloc])
      steps'    <- stepsT steps
      return $ steps1 ++ steps'
    where
      fusePar :: Comp l -> Comp l -> F l m [Step l]
      fusePar left0 right0 = do
          left <- unrollEmits left0
          -- We need to make sure that the producer and consumer have unique sets of
          -- binders, so we freshen all binders in the consumer. Why the consumer?
          -- Because >>> is left-associative, so we hopefully avoid repeated re-naming
          -- of binders by renaming the consumer.
          right <- unrollTakes $ alphaRename (allVars left0) right0
          traceFusion $ text "Attempting to fuse" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right)
          comp <- withLeftKont steps $
                  withRightKont steps $
                  fuse left right >>=
                  simplComp
          checkFusionBlowup (size left + size right) (size comp)
          fusionSucceeded left right comp
          return $ unComp comp

      checkFusionBlowup :: Int -> Int -> F l m ()
      checkFusionBlowup s1 s2 = do
          k <- asksFlags maxFusionBlowup
          when (r > k) $ do
              traceFusion $ text "Blowup factor too large" <+> parens (ppr r)
              mzero
        where
          r :: Double
          r = fromIntegral s2 / fromIntegral s1

      fusionSucceeded :: Comp l -> Comp l -> Comp l -> F l m ()
      fusionSucceeded left right result = do
          modifyStats $ \s -> s { fusedPars = fusedPars s + 1 }
          traceFusion $ text "Fused" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right) </>
              text "into:" </> indent 2 (ppr result)

      fusionFailed :: Comp l -> Comp l -> F l m ()
      fusionFailed left right = do
          modifyStats $ \s -> s { fusionFailures = fusionFailures s + 1 }
          traceFusion $ text "Failed to fuse" <+>
              text "producer:" </> indent 2 (ppr left) </>
              text "and consumer:" </> indent 2 (ppr right)

  stepsT steps =
      transSteps steps

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    comp <- recoverRepeat_ $
            void $ runRight (unComp left) (unComp right)
    return $ collapseJoint <$> comp

pprFirstStep :: IsLabel l => [Step l] -> Doc
pprFirstStep []       = empty
pprFirstStep (step:_) = ppr step

runRight :: forall l m . (IsLabel l, MonadTc m)
         => [Step l]
         -> [Step l]
         -> F l m [Step l]
runRight lss rss = do
    whenVerb $ traceFusion $ text "runRight:" </>
        indent 2 (nest 2 $ text "left:" </> pprFirstStep lss) </>
        indent 2 (nest 2 $ text "right:" </> pprFirstStep rss)
    run lss rss
  where
    run :: [Step l] -> [Step l] -> F l m [Step l]
    run lss [] =
        return lss

    {- Note ["Free" Left Steps]

    We want to go ahead and run all "free" left steps so that they have already
    been executed when we look for confluence. Consider:

        { let x = ...; let y = ...; repeat { ... }} >>> repeat { ... }

    We want to be at the left computation's repeat head when we fuse pars so
    that the trace will align when we fuse the repeats.

    When running a "free" return or lift, we need to be sure to also run the
    subsequent bind. However, we don't want to run a final lift or return,
    because those would be the final value of the overall fused computation---we
    need to wait until the right side is done running before running a final
    lift or return on the left.
    -}
    run (ls1:ls2:lss) rss | isFree ls1 ls2 = do
        l1' <- joint (ls1:ls2:lss) rss
        l2' <- joint (ls2:lss) rss
        relabelStep l1' ls1 $
          relabelStep l2' ls2 $
          runRight lss rss
      where
        isFree :: Step l -> Step l -> Bool
        isFree ReturnC{} BindC{} = True
        isFree LiftC{}   BindC{} = True
        isFree _         _       = False

    -- lss@(_:_) ensures we won't match a final lift/return. A final let is weird
    -- and useless anyway, so we don't worry about it :)
    run (ls:lss@(_:_)) rss | isFree ls = do
        l' <- joint (ls:lss) rss
        relabelStep l' ls $
          runRight lss rss
      where
        isFree :: Step l -> Bool
        isFree LetC{}              = True
        isFree ReturnC{}           = True
        isFree LiftC{}             = True
        isFree (BindC _ WildV _ _) = True
        isFree _                   = False

    run lss (rs@(IfC _l e c1 c2 s) : rss) =
        ifte joinIf
             (\(step, lss') -> jointStep step $ runRight lss' rss)
             divergeIf
      where
        joinIf :: F l m (Step (Joint l), [Step l])
        joinIf = do
            l'          <- joint lss (rs:rss)
            (lss1, c1') <- recoverRepeat $
                           withRightKont rss $
                           runRight lss (unComp c1)
            (lss2, c2') <- recoverRepeat $
                           withRightKont rss $
                           runRight lss (unComp c2)
            guardLeftConvergence lss1 lss2
            return (IfC l' e c1' c2' s, lss1)

        divergeIf :: F l m [Step l]
        divergeIf = do
            l'  <- joint lss (rs:rss)
            c1' <- recoverRepeat_ $ void $ runRight lss (unComp c1 ++ rss)
            c2' <- recoverRepeat_ $ void $ runRight lss (unComp c2 ++ rss)
            jointStep (IfC l' e c1' c2' s) $
              return []

    run lss (rs@(WhileC _l e c s) : rss) =
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
            mzero

    -- See Note [Fusing For Loops]
    run lss (rs@(ForC l ann v tau e1 e2 c s) : rss) =
        ifte joinFor
             (\step -> jointStep step $ runRight lss rss)
             divergeFor
      where
        joinFor :: F l m (Step (Joint l))
        joinFor = do
            l'            <- joint lss (rs:rss)
            (lss', steps) <- collectSteps $
                             withRightKont rss $
                             extendVars [(v, tau)] $
                             runRight lss (unComp c)
            guardLeftConvergence lss lss'
            return $ ForC l' ann v tau e1 e2 (mkComp steps) s

        divergeFor :: F l m [Step l]
        divergeFor = do
            unrollingFor ann c
            unrolled <- unrollFor l v e1 e2 c
            runRight lss (unComp unrolled ++ rss)

    run lss rss@(TakeC{} : _) =
        runLeft lss rss

    run _ (TakesC{} : _) =
        faildoc $ text "Saw takes in consumer."

    run lss rss@(RepeatC _ _ c _ : _) =
        withRightKont rss $ do
        rightRepeat c
        runRight lss (unComp c ++ rss)

    run _lss (ParC{} : _rss) =
        nestedPar

    run lss (rs:rss) = do
        l' <- joint lss (rs:rss)
        relabelStep l' rs $
          runRight lss rss

runLeft :: forall l m . (IsLabel l, MonadTc m)
        => [Step l]
        -> [Step l]
        -> F l m [Step l]
runLeft lss rss = do
    whenVerb $ traceFusion $ text "runLeft:" </>
        indent 2 (nest 2 $ text "left:" </> pprFirstStep lss) </>
        indent 2 (nest 2 $ text "right:" </> pprFirstStep rss)
    run lss rss
  where
    run :: [Step l] -> [Step l] -> F l m [Step l]
    run [] rss =
        return rss

    run (ls@(IfC _l e c1 c2 s) : lss) rss =
        ifte joinIf
             (\(step, rss') -> jointStep step $ runLeft lss rss')
             divergeIf
      where
        joinIf :: F l m (Step (Joint l), [Step l])
        joinIf = do
            l'          <- joint (ls:lss) rss
            (rss1, c1') <- recoverRepeat $
                           withLeftKont lss $
                           runLeft (unComp c1) rss
            (rss2, c2') <- recoverRepeat $
                           withLeftKont lss $
                           runLeft (unComp c2) rss
            guardRightConvergence rss1 rss2
            return (IfC l' e c1' c2' s, rss1)

        divergeIf :: F l m [Step l]
        divergeIf = do
            l'  <- joint (ls:lss) rss
            c1' <- recoverRepeat_ $ void $ runLeft (unComp c1 ++ lss) rss
            c2' <- recoverRepeat_ $ void $ runLeft (unComp c2 ++ lss) rss
            jointStep (IfC l' e c1' c2' s) $
              return []

    run (ls@(WhileC _l e c s) : lss) rss =
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
            mzero

    -- See Note [Fusing For Loops]
    run (ls@(ForC l ann v tau e1 e2 c s) : lss) rss =
        ifte joinFor
             (\step -> jointStep step $ runLeft lss rss)
             divergeFor
      where
        joinFor :: F l m (Step (Joint l))
        joinFor = do
            l'            <- joint (ls:lss) rss
            (rss', steps) <- collectSteps $
                             withLeftKont lss $
                             extendVars [(v, tau)] $
                             runLeft (unComp c) rss
            guardRightConvergence rss rss'
            return $ ForC l' ann v tau e1 e2 (mkComp steps) s

        divergeFor :: F l m [Step l]
        divergeFor = do
            unrollingFor ann c
            unrolled <- unrollFor l v e1 e2 c
            runLeft (unComp unrolled ++ lss) rss

    run lss@(EmitC _ e _ : _) rss@(TakeC{} : _) =
        emitTake e lss rss

    run (ls@EmitC{} : _) (rs@TakesC{} : _) = do
        traceFusion $ ppr ls <+> text "paired with" <+> ppr rs
        mzero

    run (EmitC{} : _) _ =
        faildoc $ text "emit paired with non-take."

    run (EmitsC{} : _) _ =
        faildoc $ text "Saw emits in producer."

    run lss@(RepeatC _ _ c _ : _) rss =
        withLeftKont lss $ do
        leftRepeat c
        runLeft (unComp c ++ lss) rss

    run (ParC{} : _lss) _rss =
        nestedPar

    run (ls:lss) rss = do
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
    mzero

-- | Indicate that we are unrolling a for loop with the given body during
-- fusion. This will fail unless the appropriate flag has been specified or if
-- the loop is one that we always unroll.
unrollingFor :: (IsLabel l, MonadTc m) => UnrollAnn -> Comp l -> F l m ()
unrollingFor ann body = do
    doUnroll <- asksFlags (testDynFlag FuseUnroll)
    unless (ann == Unroll || alwaysUnroll body || (doUnroll && mayUnroll ann)) $ do
      traceFusion $ text "Encountered diverging loop during fusion."
      mzero
  where
    alwaysUnroll :: Comp l -> Bool
    alwaysUnroll comp = allEmits (unComp comp) || allTakes (unComp comp)
      where
        allEmits :: [Step l] -> Bool
        allEmits []           = True
        allEmits (EmitC{}:ss) = allEmits ss
        allEmits _            = False

        allTakes :: [Step l] -> Bool
        allTakes [] =
            True

        allTakes (TakeC{}:BindC _ (TameV bv) _ _:LiftC _ (AssignE _ (VarE v' _) _) _:ss) =
            v' == bVar bv && allTakes ss

        allTakes _ =
            False

unalignedRepeats :: MonadTc m => F l m ()
unalignedRepeats =
    traceFusion $ text "Unaligned repeat loops"

-- | Alpha-rename binders given an in-scope set of binders.
alphaRename :: Subst Exp Var a => Set Var -> a -> a
alphaRename = subst (mempty :: Map Var Exp)

-- | Return the given array type's size, which must be statically known.
knownArraySize :: MonadTc m => Type -> m (Int, Type)
knownArraySize tau = do
    (iota, tau_elem) <- checkArrT tau
    case iota of
      ConstI n _ -> return (n, tau_elem)
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
encounter a step we have seen before. This label is then used by `recoverRepeat`
to recover the loop.

When the repeat loops are unaligned, we take care to save and restore variables
that are bound by the shifted repeat loop prefix.
-}

recoverRepeat :: forall a l m . (IsLabel l, MonadTc m)
              => F l m a
              -> F l m (a, Comp (Joint l))
recoverRepeat m = do
    ((x, steps), maybe_l) <- collectLoopHead $ collectSteps m
    case maybe_l of
      Nothing -> return (x, mkComp steps)
      Just l  -> (,) <$> pure x <*> recover l steps []
  where
    recover :: Joint l
            -> [Step (Joint l)]       -- ^ Remaining steps in the computation
            -> [Step (Joint l)]       -- ^ Prefix (reversed) of the computation
            -> F l m (Comp (Joint l)) -- ^ Computation with recovered repeat
    recover l = loop
      where
        loop :: [Step (Joint l)] -> [Step (Joint l)] -> F l m (Comp (Joint l))
        loop [] _prefix = do
            traceFusion $ text "Could not find repeat label!"
            -- XXX We could try this...but would we still be able to recover the
            -- loop?
            --
            --   return $ mkComp $ reverse prefix
            --
            mzero

        loop steps@(step:_) prefix | stepLabel step == Just l = do
            taus                       <- mapM (inferFv c_prefix) vs
            (c_let, c_restore, c_save) <- mconcat <$>
                                            zipWithM mkDeclSaveRestore vs taus
            c_repeat                   <- C.repeatC AutoVect $
                                            c_restore <> c_body <> c_save
            return $ c_prefix <> c_let <> c_repeat
          where
            -- Variables bound by the shifted prefix of the unaligned repeat
            -- loops
            vs :: [Var]
            vs = Set.toList $ fvs c_body `Set.intersection` binders c_body

            c_prefix, c_body :: Comp (Joint l)
            c_prefix = mkComp (reverse prefix)
            c_body   = mkComp steps

        loop (step:steps) prefix =
            loop steps (step:prefix)

    inferFv :: Comp (Joint l) -> Var -> F l m Type
    inferFv c v = do
        (tau, _, _, _) <- inferComp (c <> mkComp [returnVarC]) >>=
                          checkSTC
        return tau
      where
        returnVarC :: Step (Joint l)
        returnVarC = ReturnC "dummy" (varE v) (srclocOf v)

    mkDeclSaveRestore :: Var
                      -> Type
                      -> F l m (Comp (Joint l), Comp (Joint l), Comp (Joint l))
    mkDeclSaveRestore v tau | isRefT tau = do
        v'       <- gensym (namedString v ++ "_save")
        t1       <- gensym (namedString v ++ "_temp1")
        t2       <- gensym (namedString v ++ "_temp2")
        t3       <- gensym (namedString v ++ "_temp3")
        letc     <- mkSteps [C.liftC $ derefE (varE v)
                            ,C.bindC (TameV (mkBoundVar t1)) (unRefT tau)
                            ,C.letrefC v' (unRefT tau) (Just (varE t1))]
        restorec <- mkSteps [C.liftC $ derefE (varE v')
                            ,C.bindC (TameV (mkBoundVar t2)) (unRefT tau)
                            ,C.liftC $ assignE (varE v) (varE t2)]
        savec    <- mkSteps [C.liftC $ derefE (varE v)
                            ,C.bindC (TameV (mkBoundVar t3)) (unRefT tau)
                            ,C.liftC $ assignE (varE v') (varE t3)]
        return (letc, restorec, savec)

    mkDeclSaveRestore v tau = do
        v'       <- gensym (namedString v ++ "_save")
        letc     <- mkSteps [C.letrefC v' tau (Just (varE v))]
        restorec <- mkSteps [C.liftC $ derefE (varE v')
                            ,C.bindC (TameV (mkBoundVar v)) tau]
        savec    <- mkSteps [C.liftC $ assignE (varE v') (varE v)]
        return (letc, restorec, savec)

    mkSteps :: [F l m (Comp (Joint l))] -> F l m (Comp (Joint l))
    mkSteps = fmap mconcat . sequence

recoverRepeat_ :: forall l m . (IsLabel l, MonadTc m)
               => F l m ()
               -> F l m (Comp (Joint l))
recoverRepeat_ m = snd <$> recoverRepeat m

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
        comp'  <- rateComp comp
        steps' <- stepsT steps
        return $ unComp comp' ++ steps'

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
        (n, tau) <- inferExp e >>= knownArraySize
        comp     <- runK $
                    letC "xs" (arrKnownT n tau) e $ \xs ->
                    forC 0 n $ \i ->
                      emitC (idxE xs i)
        comp'    <- rateComp comp
        steps'   <- stepsT steps
        return $ unComp comp' ++ steps'

    stepsT steps =
        transSteps steps
