{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Fuse
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Fuse (
    fuseProgram
  ) where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus(..),
                      guard,
                      unless,
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
import Control.Monad.Trans (lift)
import Data.Foldable (toList)
import Data.Loc (noLoc,
                 srclocOf)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq, (|>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Rate
import KZC.Config
import qualified KZC.Core.Comp as C
import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Fuel
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Name
import KZC.Optimize.Autolut (autolutComp)
import KZC.Optimize.FloatViews (floatViewsComp)
import KZC.Optimize.Simplify (simplComp)
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Logic
import KZC.Util.SetLike
import KZC.Util.Trace
import KZC.Util.Uniq
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
    l_left  <- gensym "end_left"
    l_right <- gensym "end_right"
    return FEnv { leftKont  = l_left
                , rightKont = l_right
                }

data FState l = FState
    { code          :: !(Seq (Step (Joint l))) -- Fused code
    , seen          :: !(Set (Joint l))        -- All seen labels
    , loopHead      :: !(Maybe (Joint l))      -- Label of loop head
    , leftLoopHead  :: !(Maybe l)              -- Label of head of left repeat
    , rightLoopHead :: !(Maybe l)              -- Label of head of right repeat
    }

defaultFState :: IsLabel l => FState l
defaultFState = FState
    { code          = mempty
    , seen          = mempty
    , loopHead      = Nothing
    , leftLoopHead  = Nothing
    , rightLoopHead = Nothing
    }

data FusionStats = FusionStats
    { fusedPars      :: !Int
    , fusionFailures :: !Int
    , fusionTopRate  :: !(Maybe (Rate M))
    }

instance Monoid FusionStats where
    mempty = FusionStats 0 0 Nothing

    x `mappend` y = FusionStats
        { fusedPars      = fusedPars x + fusedPars y
        , fusionFailures = fusionFailures x + fusionFailures y
        , fusionTopRate  = fusionTopRate y
        }

instance Pretty FusionStats where
    ppr stats =
        text "      Fused pars:" <+> ppr (fusedPars stats) </>
        text " Fusion failures:" <+> ppr (fusionFailures stats) </>
        text " In multiplicity:" <+> pprRate (fmap inMult (fusionTopRate stats)) </>
        text "Out multiplicity:" <+> pprRate (fmap outMult (fusionTopRate stats))
      where
        pprRate :: Maybe M -> Doc
        pprRate m = ppr (fromMaybe (0 :: Int) (m >>= toCount))

newtype F l m a = F { unF :: ReaderT (FEnv l)
                               (StateT (FState l)
                                 (SEFKT (StateT FusionStats m))) a }
    deriving (Functor, Applicative, Monad,
              Alternative, MonadPlus,
              MonadIO,
              MonadReader (FEnv l),
              MonadState (FState l),
              MonadException,
              MonadLogic,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadFuel,
              MonadPlatform,
              MonadTrace,
              MonadTc)

runF :: forall l m a . (IsLabel l, MonadTc m)
     => F l m a
     -> m a
runF m = do
  env <- defaultFEnv
  evalStateT (runSEFKT (evalStateT (runReaderT (unF m) env) defaultFState))
             mempty

withLeftKont :: MonadTc m => [Step l] -> F l m a -> F l m a
withLeftKont steps m = do
    klabel <- leftStepsLabel steps
    local (\env -> env { leftKont = klabel }) m

withRightKont :: MonadTc m => [Step l] -> F l m a -> F l m a
withRightKont steps m = do
    klabel <- rightStepsLabel steps
    local (\env -> env { rightKont = klabel }) m

leftStepsLabel :: MonadTc m => [Step l] -> F l m l
leftStepsLabel []         = asks leftKont
leftStepsLabel (step : _) = stepLabel step

rightStepsLabel :: MonadTc m => [Step l] -> F l m l
rightStepsLabel []         = asks rightKont
rightStepsLabel (step : _) = stepLabel step

joint :: MonadTc m
      => [Step l]
      -> [Step l]
      -> F l m (Joint l)
joint lss rss = JointL <$> leftStepsLabel lss <*> rightStepsLabel rss

-- | Given the right side of a computation, return a function that will compute
-- a joint label when given a label for the left side of the computation.
jointRight :: MonadTc m
           => [Step l]
           -> F l m (l -> Joint l)
jointRight rss = do
    l_r <- rightStepsLabel rss
    return (`JointL` l_r)

-- | Given the left side of a computation, return a function that will compute a
-- joint label when given a label for the right side of the computation.
jointLeft :: MonadTc m
          => [Step l]
          -> F l m (l -> Joint l)
jointLeft lss = do
    l_l <- leftStepsLabel lss
    return (l_l `JointL`)

-- | Record a joint step.
jointStep :: (IsLabel l, MonadTc m)
          => Step (Joint l)
          -> F l m [Step l]
          -> F l m [Step l]
jointStep step k = do
    l_joint  <- stepLabel step
    l_repeat <- repeatLabel
    saw      <- sawLabel l_joint
    if saw
      then do setLoopHead l_joint
              c <- gets code
              whenVerbLevel 2 $ traceFusion $
                  text "Found loop with label:" <+> ppr l_joint </>
                  text "final code:" </> indent 2 (ppr (toList c))
              return []
{- Note [Duplicate labels in loops]

If we hit the joint loop head, that means the loops aligned. Now we need to
forget all the steps we've seen and record steps until we hit the loop head
again. Note that we *still* record, the loop head! Also note that this can lead
to steps with duplicate labels since steps with the same label may occur in the
loop prefix as well as the loop body.
-}
      else do when (l_repeat == Just l_joint) $
                modify $ \s -> s { seen = mempty }
              recordLabel l_joint
              whenVerbLevel 2 $ traceFusion $
                text "jointStep:" <+> ppr l_joint <> colon </> ppr step
              modify $ \s -> s { code = code s |> step }
              whenVerbLevel 3 $ do
                  c <- gets code
                  traceFusion $ text "Joint code:" </> ppr (toList c)
              extendStepVars step k

extendStepVars :: MonadTc m
               => Step l
               -> F l' m a
               -> F l' m a
extendStepVars (LetC _ (LetLD v tau _ _) _) k =
    extendVars [(bVar v, tau)] k

extendStepVars (LetC _ (LetRefLD v tau _ _) _) k =
    extendVars [(bVar v, refT tau)] k

extendStepVars (BindC _ wv tau _) k =
    extendWildVars [(wv, tau)] k

extendStepVars _ k =
    k

setLoopHead :: MonadTc m => Joint l -> F l m ()
setLoopHead l = modify $ \s -> s { loopHead = Just l }

{- Note [Fusing Repeat]

We fuse repeat by unrolling the repeat loop on demand.

The only time that fusion will produce a repeat loop is when both sides of the
par are repeats. We detect a loop by keeping track of the labels of all fused
steps that have been produced so far and recording the loop header label when we
encounter a step we have seen before. This label is then used by `collectSteps`
to recover the loop.

When the repeat loops are unaligned, we take care to save and restore variables
that are bound by the shifted repeat loop prefix.
-}

collectSteps :: forall a l m . (IsLabel l, MonadTc m)
             => F l m a
             -> F l m (a, [Step (Joint l)])
collectSteps m = do
    old_code     <- gets code
    old_seen     <- gets seen
    old_loopHead <- gets loopHead
    modify $ \s -> s { code     = mempty
                     , loopHead = Nothing
                     }
    x <- m
    l_head <- gets loopHead
    steps  <- toList <$> gets code
    modify $ \s -> s { code     = old_code
                     , seen     = old_seen
                     , loopHead = old_loopHead
                     }
    case l_head of
      Nothing -> return (x, steps)
      Just l  -> do c <- recover l steps
                    whenVerb $ traceFusion $ nest 2 $ text "Recovered loop:" </> ppr c
                    return (x, unComp c)
  where
    recover :: Joint l                -- ^ Label of the head of the repeat loop
            -> [Step (Joint l)]       -- ^ Computation steps
            -> F l m (Comp (Joint l)) -- ^ Computation with recovered repeat
    recover l steps = loop steps []
      where
        loop :: [Step (Joint l)]       -- ^ Remaining steps in the computation
             -> [Step (Joint l)]       -- ^ Prefix (reversed) of the computation
             -> F l m (Comp (Joint l)) -- ^ Computation with recovered repeat
        loop [] _prefix = do
            traceFusion $ text "Could not find repeat label!"
            -- XXX We could try this...but would we still be able to recover the
            -- loop?
            --
            --   return $ mkComp $ reverse prefix
            --
            mzero

        loop steps@(step:_) [] | stepLabel step == Just l =
            return $ mkComp [RepeatC l AutoVect c_body (srclocOf c_body)]
          where
            c_body :: Comp (Joint l)
            c_body = mkComp steps

        loop steps@(step:_) prefix | stepLabel step == Just l = do
            unalignedRepeats
            taus                       <- mapM (inferFv c_prefix) vs
            (c_let, c_restore, c_save) <- mconcat <$>
                                            zipWithM mkDeclSaveRestore vs taus
            c_repeat                   <- C.repeatC AutoVect $
                                            c_restore <> c_body <> c_save
            -- See Note [Duplicate labels in loops]
            c_prefix' <- traverse uniquify c_prefix
            return $ c_prefix' <> c_let <> c_repeat
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

collectSteps_ :: (IsLabel l, MonadTc m)
              => F l m a
              -> F l m [Step (Joint l)]
collectSteps_ k = snd <$> collectSteps k

collectComp :: (IsLabel l, MonadTc m)
            => F l m a
            -> F l m (a, Comp (Joint l))
collectComp k = do
    (x, steps) <- collectSteps k
    return (x, mkComp steps)

collectComp_ :: (IsLabel l, MonadTc m)
             => F l m a
             -> F l m (Comp (Joint l))
collectComp_ k = snd <$> collectComp k

collectLeftLoopBody :: forall a l m . (IsLabel l, MonadTc m)
                    => l
                    -> Comp l
                    -> [Step l]
                    -> ([Step l] -> F l m a)
                    -> F l m (Comp (Joint l))
collectLeftLoopBody l_left c rss k = do
    l_right     <- rightStepsLabel rss
    let l_joint =  l_left `JointL` l_right
    steps <- collectSteps_ $
             withLeftKont [noopStep l_left] $
             k (labelLoopBody l_left c)
    collectLoopBody l_joint steps

collectRightLoopBody :: forall a l m . (IsLabel l, MonadTc m)
                     => [Step l]
                     -> l
                     -> Comp l
                     -> ([Step l] -> F l m a)
                     -> F l m (Comp (Joint l))
collectRightLoopBody lss l_right c k = do
    l_left      <- leftStepsLabel lss
    let l_joint =  l_left `JointL` l_right
    steps <- collectSteps_ $
             withRightKont [noopStep l_right] $
             k (labelLoopBody l_right c)
    collectLoopBody l_joint steps

collectJointLoopBody :: forall a l m . (IsLabel l, MonadTc m)
                     => l
                     -> Comp l
                     -> l
                     -> Comp l
                     -> ([Step l] -> [Step l] -> F l m a)
                     -> F l m (Comp (Joint l))
collectJointLoopBody l_left c_left l_right c_right k = do
    steps <- collectSteps_ $
             withLeftKont  [noopStep l_left] $
             withRightKont [noopStep l_right] $
             k (labelLoopBody l_left c_left)
               (labelLoopBody l_right c_right)
    collectLoopBody l_joint steps
  where
    l_joint :: Joint l
    l_joint = l_left `JointL` l_right

-- | Modify a loop body so that the given label, which should be the label of
-- the loop header, comes both before and after the loop body.
labelLoopBody :: l -> Comp l -> [Step l]
labelLoopBody l c = noopStep l : unComp c ++ [noopStep l]

collectLoopBody :: (IsLabel l, MonadTc m)
                => Joint l
                -> [Step (Joint l)]
                -> F l m (Comp (Joint l))
collectLoopBody l_joint [RepeatC l _ c _] | l == l_joint =
    return c

collectLoopBody l_joint [RepeatC l _ c _] = do
    whenVerbLevel 2 $ traceFusion $ nest 2 $
      text "Expected loop head" <+> ppr l_joint <+>
      text "but got" <+> ppr l </> ppr c
    mzero

collectLoopBody _l_joint steps = do
    whenVerbLevel 2 $ traceFusion $ nest 2 $
      text "Expected loop but got:" </> ppr steps
    mzero

repeatLabel :: forall l m . MonadTc m => F l m (Maybe (Joint l))
repeatLabel = do
    maybe_left  <- gets leftLoopHead
    maybe_right <- gets rightLoopHead
    case (maybe_left, maybe_right) of
      (Just left, Just right) -> return $ Just $ JointL left right
      _                       -> return Nothing

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

fuseProgram :: forall l m . (IsLabel l, MonadIO m, MonadTc m)
            => Program l -> m (Program l)
fuseProgram = runF . fuseProg
  where
    fuseProg :: Program l -> F l m (Program l)
    fuseProg prog = do
        prog'     <- programT prog
        modifyStats $ \s -> s { fusionTopRate = progRate prog' }
        dumpStats <- asksConfig (testDynFlag ShowFusionStats)
        when dumpStats $ do
            stats  <- getStats
            liftIO $ putDocLn $ nest 2 $
                text "Fusion statistics:" </> ppr stats
        return prog'
      where
        progRate :: Program l -> Maybe (Rate M)
        progRate (Program _ _ (Just (Main c _))) = compRate c
        progRate _                               = Nothing

instance MonadTc m => TransformExp (F l m) where

instance (IsLabel l, MonadTc m) => TransformComp l (F l m) where
    mainT (Main comp tau) = do
        comp' <- inSTScope tau $
                 inLocalScope $
                 withLocContext comp (text "In definition of main") $
                 go comp (uncoalesce comp) >>= rateComp
        return $ Main comp' tau
      where
        go :: Comp l
           -> Maybe (Type, Type, Comp l, Comp l, Comp l)
           -> F l m (Comp l)
        go _ (Just (b, c, c1, c2, c3)) = do
          (s, a, d) <- askSTIndices
          c2'       <- localSTIndices (Just (b, b, c)) $
                       withLeftKont [] $
                       withRightKont [] $
                       compT c2
          ifte (do ssfuse1 <- localSTIndices (Just (s, a, c)) $
                              ifte (fusePar c1 c2')
                                   return
                                   (fusionFailed c1 c2' >> mzero)
                   cfuse1  <- rateComp (mkComp ssfuse1)
                   ssfuse2 <- localSTIndices (Just (s, a, d)) $
                              ifte (fusePar cfuse1 c3)
                                   return
                                   (fusionFailed cfuse1 c3 >> mzero)
                   cfuse2  <- rateComp (mkComp ssfuse2)
                   cfuse1' <- floatViewsComp cfuse1 >>= autolutComp
                   cfuse2' <- floatViewsComp cfuse2 >>= autolutComp
                   return $ if lutSize cfuse2' > lutSize cfuse1'
                            then cfuse2 else cfuse1)
                return
                (return c2')

        go comp _ =
            compT comp

        uncoalesce :: Comp l
                   -> Maybe (Type, Type, Comp l, Comp l, Comp l)
        uncoalesce Comp{unComp=[ParC _ c Comp{unComp=[ParC _ b c1 c2 _]} c3 _]}
          | isIdentityC c1 && isIdentityC c3 = Just (b, c, c1, c2, c3)

        uncoalesce Comp{unComp=[ParC _ b c1 Comp{unComp=[ParC _ c c2 c3 _]} _]}
          | isIdentityC c1 && isIdentityC c3 = Just (b, c, c1, c2, c3)

        uncoalesce _ =
            Nothing

    stepsT (ParC ann b c1 c2 sloc : steps) = do
        conf      <- askConfig
        (s, a, c) <- askSTIndices
        c1'       <- localSTIndices (Just (s, a, b)) $
                     compT c1
        c2'       <- localSTIndices (Just (b, b, c)) $
                     compT c2
        steps1    <- if shouldFuse conf ann
                     then ifte (withLeftKont steps $
                                withRightKont steps $
                                fusePar c1' c2')
                               return
                               (fusionFailed c1' c2' >> didntFusePar c1' c2')
                     else return [ParC ann b c1' c2' sloc]
        steps' <- stepsT steps
        return $ steps1 ++ steps'
      where
        -- We fuse a par unless it is marked always pipeline /and/ pipelining is
        -- enabled.
        shouldFuse :: Config -> PipelineAnn -> Bool
        shouldFuse conf AlwaysPipeline | testDynFlag Pipeline conf =
            False

        shouldFuse _ _ =
            True

        didntFusePar :: Comp l -> Comp l -> F l m [Step l]
        didntFusePar left right | isIdentityC left = do
            warndoc $ text "Dropping left identity coercion"
            traceFusion $ text "Dropping left identity:" </> ppr left
            return (unComp right)

        didntFusePar left right | isIdentityC right = do
            warndoc $ text "Dropping right identity coercion"
            traceFusion $ text "Dropping right identity:" </> ppr right
            return (unComp left)

        didntFusePar left right =
            return [ParC ann b left right sloc]

    stepsT steps =
        transSteps steps

fusionFailed :: (IsLabel l, MonadTc m) => Comp l -> Comp l -> F l m ()
fusionFailed left right = do
    modifyStats $ \s -> s { fusionFailures = fusionFailures s + 1 }
    warndocWhen WarnFusionFailure $ text "Failed to fuse par."
    traceFusion $ text "Failed to fuse" <+>
        text "producer:" </> indent 2 (ppr left) </>
        text "and consumer:" </> indent 2 (ppr right)

fusePar :: forall l m . (IsLabel l, MonadTc m)
        => Comp l
        -> Comp l
        -> F l m [Step l]
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
    comp0 <- prune 3 $ fuse left right
    comp  <- simplComp comp0 >>= rateComp
    traceFusion $ text "Fused" <+>
        text "producer:" </> indent 2 (ppr left) </>
        text "and consumer:" </> indent 2 (ppr right) </>
        text "into:" </> indent 2 (ppr comp0) </>
        text "which simplified to:" </> indent 2 (ppr comp)
    checkFusionBlowup left right comp
    fusionSucceeded
    return $ unComp comp
  where
    checkFusionBlowup :: Comp l -> Comp l -> Comp l -> F l m ()
    checkFusionBlowup left right comp = do
        k <- asksConfig maxFusionBlowup
        when (r > k) $
          askConfig >>= tryAutoLUT
      where
        sz_orig :: Int
        sz_orig = size left + size right

        r :: Double
        r = fromIntegral (size comp) / fromIntegral sz_orig

        tryAutoLUT :: Config -> F l m ()
        -- XXX if we don't cut off search based on the size of the original
        -- computation, we hang on, e.g., test_encdec_18mbps.blk.
        tryAutoLUT flags | testDynFlag AutoLUT flags && sz_orig < 1000 = do
            comp'  <- autolutComp comp
            let r' =  fromIntegral (size comp') / fromIntegral sz_orig
            when (r' > maxFusionBlowup flags) $
              tooBig r'
            let nbytes = lutSize comp' - (lutSize left + lutSize right)
            when (nbytes > 256*1024) $
              lutTooBig nbytes

        tryAutoLUT _ =
            tooBig r

        tooBig :: Double -> F l m ()
        tooBig r = do
          traceFusion $ text "Blowup factor too large" <+> parens (ppr r)
          whenVerb $ traceFusion $ indent 2 $ ppr comp
          warndoc $ text "Blowup factor too large during fusion" <+> parens (ppr r)
          mzero

        lutTooBig :: Integer -> F l m ()
        lutTooBig nbytes = do
          traceFusion $ text "LUT too large" <+> parens (ppr nbytes)
          whenVerb $ traceFusion $ indent 2 $ ppr comp
          warndoc $ text "LUT too large too large during fusion" <+> parens (ppr nbytes)
          mzero

    fusionSucceeded :: F l m ()
    fusionSucceeded =
        modifyStats $ \s -> s { fusedPars = fusedPars s + 1 }

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    comp <- collectComp_ $
            runRight (unComp left) (unComp right)
    return $ collapseJoint <$> comp

pprFirstStep :: forall l . IsLabel l => [Step l] -> Doc
pprFirstStep []       = empty
pprFirstStep (step:_) = pprLabel (stepLabel step) <+> ppr step
  where
    pprLabel :: Maybe l -> Doc
    pprLabel Nothing  = empty
    pprLabel (Just l) = ppr l <> colon

runRight :: forall l m . (IsLabel l, MonadTc m)
         => [Step l]
         -> [Step l]
         -> F l m [Step l]
runRight lss rss = do
    whenVerb $ traceFusion $ nest 2 $ text "runRight:" </>
        text "left:"  </> indent 2 (pprFirstStep lss) </>
        text "right:" </> indent 2 (pprFirstStep rss)
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
        relabel <- jointRight rss
        jointStep (fmap relabel ls1) $
          jointStep (fmap relabel ls2) $
          runRight lss rss
      where
        isFree :: Step l -> Step l -> Bool
        isFree ReturnC{} BindC{} = True
        isFree LiftC{}   BindC{} = True
        isFree _         _       = False

    -- lss@(_:_) ensures we won't match a final lift/return. A final let is
    -- weird and useless anyway, so we don't worry about it :)
    run (ls:lss@(_:_)) rss | isFree ls = do
        relabel <- jointRight rss
        jointStep (fmap relabel ls) $
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
            (lss1, c1') <- collectComp $
                           withRightKont rss $
                           runRight lss (unComp c1)
            (lss2, c2') <- collectComp $
                           withRightKont rss $
                           runRight lss (unComp c2)
            guardLeftConvergence lss1 lss2
            return (IfC l' e c1' c2' s, lss1)

        divergeIf :: F l m [Step l]
        divergeIf = do
            l'  <- joint lss (rs:rss)
            c1' <- collectComp_ $
                   runRight lss (unComp c1 ++ rss)
            c2' <- collectComp_ $
                   runRight lss (unComp c2 ++ rss)
            jointStep (IfC l' e c1' c2' s) $
              return []

    run lss (rs@(WhileC l e c s) : rss) =
        ifte joinWhile
             (\step -> jointStep step $ runRight lss rss)
             divergeWhile
      where
        joinWhile :: F l m (Step (Joint l))
        joinWhile = do
            c' <- collectRightLoopBody lss l c $ \rss' ->
                  runRight lss rss'
            l' <- joint lss (rs:rss)
            return $ WhileC l' e c' s

        divergeWhile :: F l m [Step l]
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in consumer"
            mzero

    run lss@(RepeatC _ _ c_l _:_) rss@(ForC _ _ _ _ gint c_r _:_)
      | Just m   <- compOutCount c_l
      , Just len <- fromIntE elen
      , Just n   <- compInCount c_r
      -- Repeat must produce
      , m > 0
      -- Loop must consume
      , n > 0
      -- Repeat loop needs to produce at least as fast as for loop consumes
      , m >= n*len
      = do
        traceFusion $ text "runRight: unrolling left repeat"
        withLeftKont lss $ do
          lss' <- unrollLeftRepeat lss
          runLeft lss' rss
      where
        (_, elen) = toStartLenGenInt gint

    -- See Note [Fusing For Loops]. This fuses rate-matched for loops.
    run (ls@(ForC l_l _ i_l tau_l gint_l c_l _):lss) (rs@(ForC l_r _ i_r tau_r gint_r c_r s):rss)
      | Just start_l <- fromIntE estart_l
      , Just len_l   <- fromIntE elen_l
      , Just start_r <- fromIntE estart_r
      , Just len_r   <- fromIntE elen_r
      , Just m       <- compOutCount c_l
      , Just n       <- compInCount c_r
      -- Rates of loop bodies equal and they are executed the same number of
      -- times.
      , m == n && len_l == len_r
      = do
        traceFusion $ text "runRight: attempting to merge rate-matched for loops"
        c <- collectJointLoopBody l_l c_l l_r c_r $ \lss' rss' ->
             extendVars [(i_l, tau_l), (i_r, tau_r)] $
             runRight lss' rss'
        l_joint <- joint (ls:lss) (rs:rss)
        traceFusion $ text "runRight: merged for loops"
        let step = ForC l_joint AutoUnroll i_r tau_r (startLenGenInt estart_r elen_r)
                   (subst1 (i_l /-> varE i_r + asintE tau_r (start_l - start_r)) c)
                   s
        jointStep step $ runRight lss rss
      where
        (estart_l, elen_l) = toStartLenGenInt gint_l
        (estart_r, elen_r) = toStartLenGenInt gint_r

    -- Fuse for loops that aren't rate matched.
    run lss@(ForC{}:_) rss@(ForC{}:_) =
        splitRightFor   lss rss `mplus`
        splitLeftFor    lss rss `mplus`
        joinRightFor    lss rss `mplus`
        joinLeftFor     lss rss `mplus`
        divergeRightFor lss rss `mplus`
        divergeLeftFor  lss rss `mplus`
        stepLeft        lss rss

    run lss rss@(ForC{}:_) =
        splitRightFor   lss rss `mplus`
        joinRightFor    lss rss `mplus`
        divergeRightFor lss rss `mplus`
        stepLeft        lss rss

    run lss@(ForC{}:_) rss@(RepeatC{} : _) =
        splitLeftFor   lss rss `mplus`
        joinLeftFor    lss rss `mplus`
        divergeLeftFor lss rss

    run lss rss@(RepeatC{} : _) = do
        traceFusion $ text "runRight: unrolling right repeat"
        withRightKont rss $ do
          rss' <- unrollRightRepeat rss
          runRight lss rss'

    run _lss (ParC{} : _rss) =
        nestedPar

    run lss rss@(TakeC{} : _) =
        runLeft lss rss

    run _ (TakesC{} : _) =
        faildoc $ text "Saw takes in consumer."

    run lss (rs:rss) = do
        relabel <- jointLeft lss
        jointStep (fmap relabel rs) $
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
            traceFusion $ text "Attempting to join left if"
            l'          <- joint (ls:lss) rss
            (rss1, c1') <- collectComp $
                           withLeftKont lss $
                           runLeft (unComp c1) rss
            (rss2, c2') <- collectComp $
                           withLeftKont lss $
                           runLeft (unComp c2) rss
            guardRightConvergence rss1 rss2
            return (IfC l' e c1' c2' s, rss1)

        divergeIf :: F l m [Step l]
        divergeIf = do
            traceFusion $ text "Left if diverged"
            l'  <- joint (ls:lss) rss
            c1' <- collectComp_ $
                   runLeft (unComp c1 ++ lss) rss
            c2' <- collectComp_ $
                   runLeft (unComp c2 ++ lss) rss
            jointStep (IfC l' e c1' c2' s) $
              return []

    run (ls@(WhileC l e c s) : lss) rss =
        ifte joinWhile
             (\step -> jointStep step $ runLeft lss rss)
             divergeWhile
      where
        joinWhile :: F l m (Step (Joint l))
        joinWhile = do
            c' <- collectLeftLoopBody l c rss $ \lss' ->
                  runRight lss' rss
            l' <- joint (ls:lss) rss
            return $ WhileC l' e c' s

        divergeWhile :: F l m [Step l]
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in producer"
            mzero

    -- We fuse two for loops using the same method no matter which side is
    -- running.
    run lss@(ForC{}:_) rss@(ForC{}:_) =
        runRight lss rss

    run lss@(ForC{}:_) rss =
        splitLeftFor   lss rss `mplus`
        joinLeftFor    lss rss `mplus`
        divergeLeftFor lss rss

    run lss@(EmitC _ e _ : _) rss@(TakeC{} : _) =
        emitTake e lss rss

    run lss@(EmitC{} : _) rss =
        runRight lss rss

    run (EmitsC{} : _) _ =
        faildoc $ text "Saw emits in producer."

    run lss@(RepeatC{}:_) rss = do
        traceFusion $ text "runLeft: unrolling left repeat"
        withLeftKont lss $ do
            lss' <- unrollLeftRepeat lss
            runLeft lss' rss

    run (ParC{} : _lss) _rss =
        nestedPar

    run (ls:lss) rss = do
        relabel <- jointRight rss
        jointStep (fmap relabel ls) $
          runLeft lss rss

splitRightFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
splitRightFor lss ~(rs:rss) = do
    steps <- trySplitFor "right" rs lss compInCount compOutCount
    runRight lss (steps ++ rss)

splitLeftFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
splitLeftFor ~(ls:lss) rss = do
    steps <- trySplitFor "left" ls rss compOutCount compInCount
    runRight (steps ++ lss) rss

trySplitFor :: forall l m . (IsLabel l, MonadTc m)
            => String                -- ^ Description of for loop being split
            -> Step l                -- ^ For loop
            -> [Step l]              -- ^ Body of other loop
            -> (Comp l -> F l m Int) -- ^ Compute rate of for loop
            -> (Comp l -> F l m Int) -- ^ Compute rate of other loop
            -> F l m [Step l]        -- ^ New split for loop
trySplitFor which for@(ForC l _ann v tau gint c_for _) ss_loop toCount_for toCount_loop = do
    i       <- tryFromIntE ei
    len_for <- tryFromIntE elen
    -- Extract loop body and iteration count
    (len_loop, c_loop) <- loopBody ss_loop
    -- Rate of a body for loop
    r_for_body <- toCount_for c_for
    -- Rate of body of other loop
    r_loop_body <- toCount_loop c_loop
    -- Rates must both be greater than 0
    guard $ r_for_body > 0 && r_loop_body > 0
    -- Total rates
    let r_for  = r_for_body*len_for
    let r_loop = r_loop_body*len_loop
    guard $ r_for > r_loop || len_for > len_loop
    -- Try to match the rate of the for loop body with that of the body of the
    -- other loop if the two loops have trhe same total rate, otherwise try to
    -- match the body of the for loop body with the rate of the entire other
    -- loop.
    let m = if r_for == r_loop then r_loop_body else r_loop
    let (q, r) = r_for `quotRem` m
    traceFusion $ text "Considering splitting" <+> text which <+> "for loop" </>
        text "  For loop body rate:" <+> ppr r_for_body </>
        text "Other loop body rate:" <+> ppr r_loop_body </>
        text "       For loop rate:" <+> ppr r_for </>
        text "     Other loop rate:" <+> ppr r_loop </>
        text "          Match rate:" <+> ppr m </>
        text "               (q,r):" <+> ppr (q, r)
    when (r /= 0) $ do
        traceFusion $ text "Will not split loop (r /= 0)"
        mzero
    when (q == 1) $ do
        traceFusion $ text "Will not split loop (q == 1)"
        mzero
    when (q >= len_for) $ do
        traceFusion $ text "Will not split loop (q >= len_for)"
        mzero
    c_for' <- splitFor l v tau i len_for q c_for
    whenVerb $ traceFusion $
      text "Split for loop:" </>
      indent 2 (ppr for) </>
      text "into:" </>
      indent 2 (ppr c_for')
    return $ unComp c_for'
  where
    ei, elen :: Exp
    (ei, elen) = toStartLenGenInt gint

    loopBody :: [Step l] -> F l m (Int, Comp l)
    loopBody [] =
        mzero

    loopBody (RepeatC _ _ c _:_) =
        return (1, c)

    loopBody (ForC _ _ _ _ gint c _:_) = do
        len <- tryFromIntE e
        return (len, c)
      where
        (_, e) = toStartLenGenInt gint

    loopBody ss = do
        c <- rateComp (mkComp ss)
        return (1, c)

trySplitFor _ _ _ _ _ =
    panicdoc $ text "trySplitFor: not a for loop"

joinRightFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
joinRightFor lss (rs@(ForC l ann v tau gint c s) : rss) = do
    traceFusion $ text "runRight: attempting to join right for" </>
        text "Left:" </> indent 2 (ppr lss) </>
        text "Right:" </> indent 2 (ppr rs)
    c' <- collectRightLoopBody lss l c $ \rss' ->
          extendVars [(v, tau)] $
          runRight lss rss'
    traceFusion $ text "runRight: joined right for"
    l' <- joint lss (rs:rss)
    jointStep (ForC l' ann v tau (startLenGenInt e1 e2) c' s) $
        runRight lss rss
  where
    (e1, e2) = toStartLenGenInt gint

joinRightFor _ _ =
    panicdoc $ text "joinRightFor: not a for loop"

joinLeftFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
joinLeftFor (ls@(ForC l _ann v tau gint c s) : lss) rss = do
    traceFusion $ text "runRight: attempting to join left for"
    c' <- collectLeftLoopBody l c rss $ \lss' ->
          extendVars [(v, tau)] $
          runRight lss' rss
    traceFusion $ text "runRight: joined left for"
    l' <- joint (ls:lss) rss
    jointStep (ForC l' AutoUnroll v tau (startLenGenInt e1 e2) c' s) $
        runRight lss rss
  where
    (e1, e2) = toStartLenGenInt gint

joinLeftFor _ _ =
    panicdoc $ text "joinLeftFor: not a for loop"

divergeRightFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
divergeRightFor lss (forc@(ForC _l ann _v _tau _gint c _) : rss) = do
    traceFusion $ nest 2 $ text "Considering unrolling right for:" </> ppr forc
    shouldUnroll <- shouldUnrollFor ann c
    when (not shouldUnroll) $ do
      traceFusion $ text "Encountered diverging loop during fusion."
      mzero
    unrolled <- unrollFor forc
    traceFusion $ text "runRight: unrolling right for"
    runRight lss (unComp unrolled ++ rss)

divergeRightFor _ _ =
    panicdoc $ text "divergeRightFor: not a for loop"

divergeLeftFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
divergeLeftFor (forc@(ForC _l ann _v _tau _gint c _) : lss) rss = do
    traceFusion $ nest 2 $ text "Considering unrolling left for:" </> ppr forc
    shouldUnroll <- shouldUnrollFor ann c
    when (not shouldUnroll) $ do
      traceFusion $ text "Encountered diverging loop during fusion."
      mzero
    unrolled <- unrollFor forc
    traceFusion $ text "runRight: unrolling left for"
    runRight (unComp unrolled ++ lss) rss

divergeLeftFor _ _ =
    panicdoc $ text "divergeLeftFor: not a for loop"

-- If we can't fuse the right for loop and the left side doesn't emit, we
-- attempt to step the left side hoping we can fuse the rest of the
-- computation.
stepLeft :: forall l m . (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
stepLeft [] _ = do
    traceFusion $ text "Failed to step left"
    mzero

stepLeft (ls:lss) rss = do
    traceFusion $ text "Attempting to step left" </> indent 2 (ppr ls)
    noEmit <- doesNotEmit ls
    unless noEmit $ do
      traceFusion $ text "Failed to step left"
      mzero
    l_right <- rightStepsLabel rss
    let ls' =  fmap (`JointL` l_right) ls
    jointStep ls' $
      runLeft lss rss
  where
    doesNotEmit :: Step l -> F l m Bool
    doesNotEmit step = do
        m <- rateComp (mkComp [step]) >>= compOutM
        return $ m == N 0

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

-- | Decide whether or not we should unroll a for loop with the given body
-- during fusion.
shouldUnrollFor :: (IsLabel l, MonadTc m) => UnrollAnn -> Comp l -> F l m Bool
shouldUnrollFor ann body = do
    doUnroll <- asksConfig (testDynFlag FuseUnroll)
    return (ann == Unroll || alwaysUnroll body || (doUnroll && mayUnroll ann))
  where
    alwaysUnroll :: Comp l -> Bool
    alwaysUnroll comp = allEmits (unComp comp) || allTakes (unComp comp)

    allEmits :: [Step l] -> Bool
    allEmits [] =
        True

    allEmits (EmitC{}:ss) =
        allEmits ss

    allEmits (ReturnC _ e _:ss) =
        isUnitE e && allEmits ss

    allEmits _ =
        False

    allTakes :: [Step l] -> Bool
    allTakes [] =
        True

    allTakes (TakeC{}:BindC _ (TameV bv) _ _:LiftC _ (AssignE _ (VarE v' _) _) _:ss) =
        v' == bVar bv && allTakes ss

    allTakes (TakeC{}:BindC _ WildV _ _:ss) =
        allTakes ss

    allTakes (TakeC{}:ss) =
        allTakes ss

    allTakes (ReturnC _ e _:BindC _ WildV _ _:ss) =
        isUnitE e && allTakes ss

    allTakes (ReturnC _ e _:ss) =
        isUnitE e && allTakes ss

    allTakes _ =
        False

    isUnitE :: Exp -> Bool
    isUnitE (ConstE UnitC{} _) = True
    isUnitE _                  = False

unalignedRepeats :: MonadTc m => F l m ()
unalignedRepeats =
    traceFusion $ text "Unaligned repeat loops"

-- | Alpha-rename binders given an in-scope set of binders.
alphaRename :: Subst Exp Var a => Set Var -> a -> a
alphaRename = subst (mempty :: Map Var Exp)

-- | Return the given array type's size, which must be statically known.
knownArraySize :: MonadTc m => Type -> m (Int, Type)
knownArraySize tau = do
    (nat, tau_elem) <- checkArrT tau
    case nat of
      NatT n _ -> return (n, tau_elem)
      _        -> fail "Unknown emitted array size"

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

-- | Return a no-op step with the given label.
noopStep :: l -> Step l
noopStep l = ReturnC l unitE noLoc

-- | Return a no-op computation with the given label.
noopComp :: l -> Comp l
noopComp l = mkComp [noopStep l]

-- | Unroll a left repeat loop.
unrollLeftRepeat :: (IsLabel l, MonadTc m)
                 => [Step l]
                 -> F l m [Step l]
unrollLeftRepeat steps@(RepeatC l _ann c _s : _) = do
    modify $ \s -> s { leftLoopHead = Just l }
    return $ noopStep l : unComp c ++ steps

unrollLeftRepeat steps =
    faildoc $ nest 2 $ text "unrollLeftRepeat: not a repeat" </> ppr steps

-- | Unroll a right repeat loop.
unrollRightRepeat :: (IsLabel l, MonadTc m)
                  => [Step l]
                  -> F l m [Step l]
unrollRightRepeat steps@(RepeatC l _ann c _s : _) = do
    modify $ \s -> s { rightLoopHead = Just l }
    return $ noopStep l : unComp c ++ steps

unrollRightRepeat steps =
    faildoc $ nest 2 $ text "unrollRightRepeat: not a repeat" </> ppr steps

-- | Unroll a for loop.
unrollFor :: forall l m . (IsLabel l, MonadTc m)
          => Step l
          -> F l m (Comp l)
unrollFor (ForC l _ann v tau gint c _) = do
    i   <- tryFromIntE e1
    len <- tryFromIntE e2
    return $ noopComp l <> unrollBody i len (\j -> subst1 (v /-> asintE tau j) c)
  where
   (e1, e2) = toStartLenGenInt gint

unrollFor step =
    faildoc $ nest 2 $ text "unrollFor: not a for" </> ppr step

-- | Unroll the body of a for loop.
unrollBody :: IsLabel l
           => Int             -- ^ Initial index
           -> Int             -- ^ Number of iterations to unroll
           -> (Int -> Comp l) -- ^ Function to generate loop body
           -> Comp l
unrollBody z n f =
    mconcat [indexLabel i <$> f i | i <- [z..(z+n-1)]]

splitFor :: forall l m . (IsLabel l, MonadTc m)
         => l              -- ^ Label of for loop
         -> Var            -- ^ Loop variable
         -> Type           -- ^ Type of loop variable
         -> Int            -- ^ Loop start
         -> Int            -- ^ Loop length
         -> Int            -- ^ Number of iterations of outer loop
         -> Comp l         -- ^ Loop body
         -> F l m (Comp l) -- ^ Split loop
splitFor l v tau start len k c = do
    i         <- gensym "i"
    let i_int =  startLenGenInt (asintE tau (0 :: Integer)) (asintE tau k)
    j         <- gensym "j"
    body1 <- rateComp $ subst1 (v /-> varE i * asintE tau q + asintE tau start + varE j) c
    body2 <- C.forC AutoUnroll j tau (asintE tau (0 :: Integer)) (asintE tau q) body1
    -- body2 <- rateComp $ mkComp [ForC l AutoUnroll j tau j_int body1 noLoc]
    rateComp $ mkComp [ForC l AutoUnroll i tau i_int body2 noLoc]
  where
    q :: Int
    q = len `quot` k

{- Note [Unrolling takes and emits]

These are two small program transformartions that convert takes and emits into
for loops whose bodies do nothing except take/emit. This allows us to use the
usual fusion mechanisms to handle takes and emits. After fusion, we convert
loops of take/emit back into single takes/emits.
-}

unrollTakes :: (IsLabel l, MonadTc m)
            => Comp l -> m (Comp l)
unrollTakes = runUT . compT

newtype UT m a = UT { runUT :: m a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadFuel,
            MonadPlatform,
            MonadTrace,
            MonadTc)

instance MonadTc m => TransformExp (UT m) where

instance (IsLabel l, MonadTc m) => TransformComp l (UT m) where
    stepsT (TakesC _ n tau _ : steps) = do
        n'    <- evalNat n
        comp  <- runK $
                 letrefC "xs_unrolltakes" (arrKnownT n' tau) $ \xs -> do
                 forC 0 n' $ \i -> do
                   x <- takeC tau
                   liftC $ assignE (idxE xs i) x
                 liftC $ derefE xs
        comp'  <- rateComp comp
        steps' <- stepsT steps
        return $ unComp comp' ++ steps'

    stepsT steps =
        transSteps steps

unrollEmits :: (IsLabel l, MonadTc m)
            => Comp l -> m (Comp l)
unrollEmits = runUE . compT

newtype UE m a = UE { runUE :: m a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadFuel,
            MonadPlatform,
            MonadTrace,
            MonadTc)

instance MonadTc m => TransformExp (UE m) where

instance (IsLabel l, MonadTc m) => TransformComp l (UE m) where
    stepsT (EmitsC _ e _ : steps) = do
        (n, tau) <- inferExp e >>= knownArraySize
        comp     <- runK $
                    letC "xs_unrollemits" (arrKnownT n tau) e $ \xs ->
                    forC 0 n $ \i ->
                      emitC (idxE xs i)
        comp'    <- rateComp comp
        steps'   <- stepsT steps
        return $ unComp comp' ++ steps'

    stepsT steps =
        transSteps steps
