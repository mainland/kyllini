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
import Control.Monad.Trans (lift)
import Data.Foldable (toList)
import Data.Loc (srclocOf)
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
    l <- gensym "end"
    return FEnv { leftKont  = l
                , rightKont = l
                }

data FState l = FState
    { code          :: !(Seq (Step (Joint l))) -- Fused code
    , seen          :: !(Set (Joint l))        -- All seen labels
    , loopHead      :: !(Maybe (Joint l))      -- Label of loop head
    , leftLoopHead  :: !(Maybe l)              -- Label of head of left repeat
    , rightLoopHead :: !(Maybe l)              -- Label of head of right repeat
    , codeCache     :: !(Map l (Comp l))
    }

defaultFState :: IsLabel l => FState l
defaultFState = FState
    { code          = mempty
    , seen          = mempty
    , loopHead      = Nothing
    , leftLoopHead  = Nothing
    , rightLoopHead = Nothing
    , codeCache     = mempty
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
        pprRate m = ppr (fromMaybe (0 :: Int) (m >>= fromP))

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
leftStepsLabel []                    = asks leftKont
leftStepsLabel (RepeatC _ _ c _ : _) = leftStepsLabel (unComp c)
leftStepsLabel (step : _)            = stepLabel step

rightStepsLabel :: MonadTc m => [Step l] -> F l m l
rightStepsLabel []                    = asks rightKont
rightStepsLabel (RepeatC _ _ c _ : _) = rightStepsLabel (unComp c)
rightStepsLabel (step : _)            = stepLabel step

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

jointStep :: (IsLabel l, MonadTc m)
          => Step (Joint l)
          -> F l m [Step l]
          -> F l m [Step l]
jointStep step k =
    extendStepVars step $ do
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
{- Note [Duplicate labels in loops]

If we hit the joint loop head, that means the loops aligned. Now we need to
forget all the steps we've seen and record steps until we hit the loop head
again. Note that we *still* record, the loop head! Also note that this can lead
to steps with duplicate labels since steps with teh same label may occur in the
loop prefix as well as the loop body.
-}
      else do when (l_repeat == Just l_joint) $
                modify $ \s -> s { seen = mempty }
              recordLabel l_joint
              modify $ \s -> s { code = code s |> step }
              k

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

collectSteps :: MonadTc m => F l m a -> F l m (a, [Step (Joint l)])
collectSteps m = do
    old_code <- gets code
    modify $ \s -> s { code = mempty }
    x <- m
    steps <- toList <$> gets code
    modify $ \s -> s { code = old_code }
    return (x, steps)

collectLoopBody :: forall a l m . (IsLabel l, MonadTc m)
                => F l m a
                -> F l m (a, Comp (Joint l))
collectLoopBody m = do
    ((x, steps), maybe_l) <- collectLoopHead $ collectSteps m
    case maybe_l of
      Nothing -> return (x, mkComp steps)
      Just _  -> faildoc $ text "Unexpected loop head in body of computation."

setLoopHead :: MonadTc m => Joint l -> F l m ()
setLoopHead l = modify $ \s -> s { loopHead = Just l }

collectLoopHead :: (IsLabel l, MonadTc m)
                => F l m a
                -> F l m (a, Maybe (Joint l))
collectLoopHead m = do
    old_seen     <- gets seen
    old_loopHead <- gets loopHead
    modify $ \s -> s { seen     = mempty
                     , loopHead = Nothing
                     }
    x <- m
    new_seen <- gets seen
    l        <- gets loopHead
    modify $ \s -> s { seen     = new_seen <> old_seen
                     , loopHead = old_loopHead
                     }
    return (x, l)

repeatLabel :: forall l m . MonadTc m => F l m (Maybe (Joint l))
repeatLabel = do
    maybe_left  <- gets leftLoopHead
    maybe_right <- gets rightLoopHead
    case (maybe_left, maybe_right) of
      (Just left, Just right) -> return $ Just $ JointL left right
      _                       -> return Nothing

leftRepeat :: MonadTc m
           => Comp l
           -> F l m ()
leftRepeat c = do
    l <- leftStepsLabel (unComp c)
    modify $ \s -> s { leftLoopHead = Just l }

rightRepeat :: MonadTc m
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

-- Cache generated code. When we rewrite code on the fly, we must ensure that if
-- we rewrite the same code more than once, we rewrite it in exactly the same
-- way---including code labels. Otherwise loop detection will not work. This bit
-- us when trying to fuse repeat04.wpl!
cacheCode :: forall l m . (IsLabel l, MonadTc m)
          => l
          -> F l m (Comp l)
          -> F l m (Comp l)
cacheCode l m =
    gets (Map.lookup l . codeCache) >>= go
  where
    go :: Maybe (Comp l) -> F l m (Comp l)
    go (Just c) =
        return c

    go Nothing = do
        c <- setCompLabel l <$> m >>= rateComp
        modify $ \s -> s { codeCache = Map.insert l c (codeCache s)}
        return c

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
    checkFusionBlowup left right comp
    fusionSucceeded left right comp0 comp
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

    fusionSucceeded :: Comp l -> Comp l -> Comp l -> Comp l -> F l m ()
    fusionSucceeded left right result simplResult = do
        modifyStats $ \s -> s { fusedPars = fusedPars s + 1 }
        traceFusion $ text "Fused" <+>
            text "producer:" </> indent 2 (ppr left) </>
            text "and consumer:" </> indent 2 (ppr right) </>
            text "into:" </> indent 2 (ppr result) </>
            text "which simplified to:" </> indent 2 (ppr simplResult)

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    comp <- recoverRepeat_ $
            void $ runRight (unComp left) (unComp right)
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
            (lss', c') <- collectLoopBody $
                          withRightKont rss $
                          runRight lss (unComp c)
            guardLeftConvergence lss lss'
            return $ WhileC l' e c' s

        divergeWhile :: F l m [Step l]
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in consumer"
            mzero

    run lss@(RepeatC _ _ c_l _:_) rss@(ForC _ _ _ _ gint c_r _:_)
      | Just m   <- compOutP c_l
      , Just len <- fromIntE elen
      , Just n   <- compInP c_r
      -- Repeat must produce
      , m > 0
      -- Loop must consume
      , n > 0
      -- Repeat loop needs to produce at least as fast as for loop consumes
      , m >= n*len
      = runLeftUnroll lss rss
      where
        (_, elen) = toStartLenGenInt gint

    -- See Note [Fusing For Loops]. This fuses rate-matched for loops.
    run (ls@(ForC _ _ i_l tau_l gint_l c_l _):lss) (rs@(ForC _ _ i_r tau_r gint_r c_r s):rss)
      | Just start_l <- fromIntE estart_l
      , Just len_l   <- fromIntE elen_l
      , Just start_r <- fromIntE estart_r
      , Just len_r   <- fromIntE elen_r
      , Just m       <- compOutP c_l
      , Just n       <- compInP c_r
      -- Rates of loop bodies equal and they are executed the same number of
      -- times.
      , m == n && len_l == len_r
      = do
        traceFusion $ text "runRight: attempting to merge rate-matched for loops"
        (lss', c) <- collectLoopBody $
                     extendVars [(i_l, tau_l), (i_r, tau_r)] $
                     runRight (unComp c_l) (unComp c_r)
        unless (null lss') $
            traceFusion $ text "runRight: failed to merge with left for"
        guard (null lss')
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
    run (ls@ForC{}:lss) (rs@ForC{}:rss) = do
        traceFusion $ text "runRight: attempting to merge non-rate-matched for loops"
        ifte   (splitRightFor (ls:lss) rs)       (\steps -> runRight (ls:lss) (steps ++ rss)) $
          ifte (splitLeftFor  ls       (rs:rss)) (\steps -> runRight (steps ++ lss) (rs:rss)) $
          ifte (joinRightFor  (ls:lss) (rs:rss)) (\step  -> jointStep step $ runRight (ls:lss) rss) $
          ifte (joinLeftFor   (ls:lss) (rs:rss)) (\step  -> jointStep step $ runRight lss (rs:rss)) $
          divergeRightFor     (ls:lss) (rs:rss) `mplus`
          divergeLeftFor      (ls:lss) (rs:rss) `mplus`
          stepLeft            (ls:lss) (rs:rss)

    run lss (rs@ForC{}:rss) =
        ifte (splitRightFor lss rs)       (\steps -> runRight lss (steps ++ rss)) $
        ifte (joinRightFor  lss (rs:rss)) (\step  -> jointStep step $ runRight lss rss) $
        divergeRightFor     lss (rs:rss) `mplus`
        stepLeft            lss (rs:rss)

    run (ls@ForC{}:lss) rss =
        ifte (splitLeftFor   ls       rss) (\steps -> runRight (steps ++ lss) rss) $
        ifte (joinLeftFor    (ls:lss) rss) (\step -> jointStep step $ runRight lss rss) $
        divergeLeftFor       (ls:lss) rss

    run lss rss@(RepeatC _ _ c _ : _) = do
        traceFusion $ text "runRight: unrolling right repeat"
        withRightKont rss $ do
          rightRepeat c
          runRight lss (unComp c ++ rss)

    run _lss (ParC{} : _rss) =
        nestedPar

    run lss rss@(TakeC{} : _) =
        runLeftUnroll lss rss

    run _ (TakesC{} : _) =
        faildoc $ text "Saw takes in consumer."

    run lss (rs:rss) = do
        relabel <- jointLeft lss
        jointStep (fmap relabel rs) $
          runRight lss rss

    splitRightFor :: (IsLabel l, MonadTc m) => [Step l] -> Step l -> F l m [Step l]
    splitRightFor lss rs =
        trySplitFor "right" rs lss compInP compOutP

    splitLeftFor :: (IsLabel l, MonadTc m) => Step l -> [Step l] -> F l m [Step l]
    splitLeftFor ls rss =
        trySplitFor "left" ls rss compOutP compInP

    joinRightFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m (Step (Joint l))
    joinRightFor lss (rs@(ForC _l ann v tau gint c s) : rss) = do
        traceFusion $ text "runRight: attempting to join right for"
        (lss', c') <- collectLoopBody $
                      withRightKont rss $
                      extendVars [(v, tau)] $
                      runRight lss (unComp c)
        guardLeftConvergence lss lss'
        traceFusion $ text "runRight: joined right for"
        l' <- joint lss (rs:rss)
        return $ ForC l' ann v tau (startLenGenInt e1 e2) c' s
      where
        (e1, e2) = toStartLenGenInt gint

    joinRightFor _ _ =
        panicdoc $ text "joinRightFor: not a for loop"

    joinLeftFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m (Step (Joint l))
    joinLeftFor (ls@(ForC _l _ann v tau gint c s) : lss) rss = do
        traceFusion $ text "runRight: attempting to join left for"
        (rss', c') <- collectLoopBody $
                      withLeftKont lss $
                      extendVars [(v, tau)] $
                      runRight (unComp c) rss
        guardRightConvergence rss rss'
        traceFusion $ text "runRight: joined left for"
        l' <- joint (ls:lss) rss
        return $ ForC l' AutoUnroll v tau (startLenGenInt e1 e2) c' s
      where
        (e1, e2) = toStartLenGenInt gint

    joinLeftFor _ _ =
        panicdoc $ text "joinLeftFor: not a for loop"

    divergeRightFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
    divergeRightFor lss (ForC l ann v tau gint c _ : rss) = do
        traceFusion $ nest 2 $ text "Considering unrolling right for:" </> ppr c
        shouldUnroll <- shouldUnrollFor ann c
        when (not shouldUnroll) $ do
          traceFusion $ text "Encountered diverging loop during fusion."
          mzero
        unrolled <- unrollFor l v tau e1 e2 c
        traceFusion $ text "runRight: unrolling right for"
        runRight lss (unComp unrolled ++ rss)
      where
        (e1, e2) = toStartLenGenInt gint

    divergeRightFor _ _ =
        panicdoc $ text "divergeRightFor: not a for loop"

    divergeLeftFor :: (IsLabel l, MonadTc m) => [Step l] -> [Step l] -> F l m [Step l]
    divergeLeftFor (ForC l ann v tau gint c _ : lss) rss = do
        traceFusion $ nest 2 $ text "Considering unrolling left for:" </> ppr c
        shouldUnroll <- shouldUnrollFor ann c
        when (not shouldUnroll) $ do
          traceFusion $ text "Encountered diverging loop during fusion."
          mzero
        unrolled <- unrollFor l v tau e1 e2 c
        traceFusion $ text "runRight: unrolling left for"
        runRight (unComp unrolled ++ lss) rss
      where
        (e1, e2) = toStartLenGenInt gint

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

runLeftUnroll :: forall l m . (IsLabel l, MonadTc m)
              => [Step l]
              -> [Step l]
              -> F l m [Step l]
runLeftUnroll lss@(RepeatC _ _ c _ : _) rss = do
    traceFusion $ text "runLeftUnroll: unrolling left repeat"
    withLeftKont lss $ do
      leftRepeat c
      runLeft (unComp c ++ lss) rss

runLeftUnroll lss rss =
    runLeft lss rss

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
            (rss', c') <- collectLoopBody $
                          withLeftKont lss $
                          runLeft (unComp c) rss
            guardRightConvergence rss rss'
            return $ WhileC l' e c' s

        divergeWhile :: F l m [Step l]
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in producer"
            mzero

    -- We run all for loops on the right.
    run lss@(ForC{}:_) rss =
        runRight lss rss

    run lss@(EmitC _ e _ : _) rss@(TakeC{} : _) =
        emitTake e lss rss

    run lss@(EmitC{} : _) rss =
        runRight lss rss

    run (EmitsC{} : _) _ =
        faildoc $ text "Saw emits in producer."

    -- We only unroll left repeats on the right so the loop merger there has a
    -- chance to see it first.
    run lss@(RepeatC{}:_) rss =
        runRight lss rss

    run (ParC{} : _lss) _rss =
        nestedPar

    run (ls:lss) rss = do
        relabel <- jointRight rss
        jointStep (fmap relabel ls) $
          runLeft lss rss

trySplitFor :: forall l m . (IsLabel l, MonadTc m)
            => String                -- ^ Description of for loop being split
            -> Step l                -- ^ For loop
            -> [Step l]              -- ^ Other loop
            -> (Comp l -> F l m Int) -- ^ Compute rate of for loop
            -> (Comp l -> F l m Int) -- ^ Compute rate of other loop
            -> F l m [Step l]        -- ^ New split for loop
trySplitFor which (ForC l _ann v tau gint c_for _) ss_loop fromP_for fromP_loop = do
    i       <- tryFromIntE ei
    len_for <- tryFromIntE elen
    -- Extract loop body and iteration count
    (len_loop, c_loop) <- loopBody ss_loop
    -- Rate of a single iteration
    n_fori  <- fromP_for c_for
    n_loopi <- fromP_loop c_loop
    -- Rates must both be greater than 0
    guard $ n_fori > 0 && n_loopi > 0
    -- Total rates
    let n_for  = n_fori*len_for
    let n_loop = n_loopi*len_loop
    guard $ n_for > n_loop || len_for > len_loop
    let m = if n_for == n_loop then n_loopi else n_loop
    let (q, r) = n_for `quotRem` m
    traceFusion $ text "Considering splitting" <+> text which <+> "for loop" </>
        text "  For loop body rate:" <+> ppr n_fori </>
        text "Other loop body rate:" <+> ppr n_loopi </>
        text "       For loop rate:" <+> ppr n_for </>
        text "     Other loop rate:" <+> ppr n_loop </>
        text "          Match rate:" <+> ppr m </>
        text "               (q,r):" <+> ppr (q, r)
    guard $ r == 0
    guard $ q /= 1 && q < len_for
    c_for' <- splitFor l v tau i len_for q c_for
    whenVerb $ traceFusion $
      text "Split for loop:" </> indent 2 (ppr c_for')
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
          -> Type
          -> Exp
          -> Exp
          -> Comp l
          -> F l m (Comp l)
unrollFor l v tau e1 e2 c = do
    i   <- tryFromIntE e1
    len <- tryFromIntE e2
    return $ setCompLabel l $ unrollBody i len $ \j -> subst1 (v /-> asintE tau j) c

splitFor :: forall l m . (IsLabel l, MonadTc m)
         => l
         -> Var
         -> Type
         -> Int
         -> Int
         -> Int
         -> Comp l
         -> F l m (Comp l)
splitFor l v tau i len k c =
    cacheCode l $ do
    v' <- gensym "i"
    C.forC AutoUnroll v' tau (asintE tau (0 :: Integer)) (asintE tau k) $
      unrollBody 0 q $ \j -> subst1 (v /-> varE v' * asintE tau q + asintE tau (i+j)) c
  where
    q = len `quot` k

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
