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
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans (lift)
import Data.Loc (srclocOf)
import Data.Map (Map)
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
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

newtype FState l = FState { seen :: Set (l, l) }

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

newtype F l m a = F { unF :: StateT (FState l) (SEFKT (StateT FusionStats m)) a }
    deriving (Functor, Applicative, Monad,
              Alternative, MonadPlus,
              MonadIO,
              MonadState (FState l),
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

runF :: forall l m a . (IsLabel l, MonadErr m)
     => F l m a
     -> m a
runF m = evalStateT (runSEFKT (evalStateT (unF m) defaultFState)) mempty

sawLabel :: (IsLabel l, MonadTc m)
         => (l, l) -> F l m Bool
sawLabel l = gets (Set.member l . seen)

recordLabel :: (IsLabel l, MonadTc m)
            => (l, l) -> F l m ()
recordLabel l = modify $ \s -> s { seen = Set.insert l (seen s) }

getStats :: MonadTc m => F l m FusionStats
getStats = F $ lift $ lift get

modifyStats :: MonadTc m => (FusionStats -> FusionStats) -> F l m ()
modifyStats = F . lift . lift . modify

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
      steps1    <- fusePar c1' c2' `mplus` return [ParC ann b c1' c2' sloc]
      steps'    <- stepsT steps
      return $ steps1 ++ steps'
    where
      fusePar :: Comp l -> Comp l -> F l m [Step l]
      fusePar left right0 = do
          l      <- compLabel right0
          klabel <- case steps of
                      []       -> gensym "end"
                      (step:_) -> stepLabel step
          comp   <- fuse left right klabel >>= setFirstLabel l
          parFused
          traceFusion $ text "Fused" <+>
              (nest 2 $ text "producer:" </> ppr left) </>
              (nest 2 $ text "and consumer:" </> ppr right) </>
              (nest 2 $ text "into:" </> ppr comp)
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

{- Note [Fusing Repeat]

We fuse repeat by unrolling the loop on demand until we reach a joint state that
we have already been in. When we reach a state we have already seen,
@whenNotBeenThere@ will insert a @LoopC@ command, labeled with the repeated
state---this is currently the only way a @LoopC@ command can be introduced.

Who will consume, i.e., remove, the @LoopC@? Whoever initiated the repeat
should. The originator of the repeat can tell if the fused stream of
computations it gets back is a repeat because it will end in a @LoopC@ with an
appropriate label.

There is one catch: we /could/ be fusing two repeat loops. Consider the
following example, which actually shows up, e.g., when inserting automatic
casts:

    repeat { x <- take; emit x)
    >>>
    repeat { x <- take; emit x)

Here's what happens when we see this example: we will run the consumer, unroll
the repeat, immediately see a take, and run the producer. The producer will
unroll the repeat, emit, and then run the consumer. The consumer emits, then
unrolls again and immediately runs the producer because it hits a take. The
producer unrolls, and hits its take, and it is now in a joint state it has
already been in, since we have run each loop once. The producer immediately see
a result consisting of a single @LoopC@ generated by 'whenNotBeenThere' /and no
other computations/. Furthermore, it has the right joint label, and the producer
was indeed executing a repeat! However, we need to pass the sequence of steps
back to the producer so it can detect the real loop.

Note that the only time we end up with this singleton @LoopC@ step is when we
are fusing repeats, thus the ugly @isNonEmptyRepeatLoop test@ in runRepeat.
-}

recoverRepeat :: forall l m . (IsLabel l, MonadTc m)
              => (l, l)                      -- ^ The label to be used for the
                                             -- resulting repeat
              -> VectAnn                     -- ^ Annotation for the resulting
                                             -- repeat
              -> (l, l)                      -- ^ Label of the loop header
              -> [Step l]                    -- ^ Remaining steps for the
                                             -- "other" side of the par
              -> [Step (l, l)]               -- ^ Fusion result.
              -> m ([Step l], [Step (l, l)]) -- ^ Pair of the remaining steps
                                             -- for the other side of the par
                                             -- and the fusion result.
recoverRepeat l ann l_repeat ss_other ss =
    return (ss_other, ss')
  where
    ss' :: [Step (l, l)]
    ss' | isNonEmptyRepeatLoop ss = mkRepeat (init ss)
        | otherwise               = ss

    mkRepeat :: [Step (l, l)] -> [Step (l, l)]
    mkRepeat steps = [RepeatC l ann (mkComp steps) (srclocOf steps)]

    isNonEmptyRepeatLoop :: [Step (l, l)] -> Bool
    isNonEmptyRepeatLoop steps = length steps > 1 && last ss == LoopC l_repeat

-- | Given a list of computation steps for the "other" side of the
-- producer/consumer loop and a label, @l@, for the current joint
-- producer/consumer state, see if we have been in the current state before. If
-- we have, return the remaining "other" side of the computation and the single
-- step @'LoopC' l@, which indicates that we have encountered a loop. Otherwise,
-- record the fact that we have seen the label @l@ and call our
-- continuation. The function 'whenNotBeenThere' is the only way a 'LoopC' step
-- can be introduced into a computation. It will be removed by 'recoverRepeat'.
whenNotBeenThere :: (IsLabel l, MonadTc m)
                 => [Step l]
                 -> (l, l)
                 -> F l m ([Step l], [Step (l, l)])
                 -> F l m ([Step l], [Step (l, l)])
whenNotBeenThere ss l k = do
    beenThere <- sawLabel l
    if beenThere
      then return (ss, [LoopC l])
      else recordLabel l >> k

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> l              -- ^ The continuation label of the par
     -> F l m (Comp l)
fuse left right klabel = do
    (_, rss') <- runRight (unComp left) (unComp right)
    return $ uncurry pairLabel <$> mkComp rss'
  where
    -- | A "free" left step is one we can go ahead and run even if the
    -- right-hand side has not yet reached a take action.
    isFreeLeftStep :: Step l -> Bool
    isFreeLeftStep LetC{}    = True
    isFreeLeftStep LiftC{}   = True
    isFreeLeftStep ReturnC{} = True
    isFreeLeftStep BindC{}   = True
    isFreeLeftStep _         = False

    runRight :: [Step l] -> [Step l] -> F l m ([Step l], [Step (l, l)])
    -- We want to go ahead and run all "free" left steps so that they have
    -- already been executed when we look for confluence. Consider:
    --
    -- { let x = ...; let y = ...; repeat { ... }} >>> repeat { ... }
    --
    -- We want to be at the left computation's repeat head when we fuse pars so
    -- that the trace will align when we fuse the repeats.
    --
    runRight (ls:lss) rss | isFreeLeftStep ls = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $
          relabelStep l' ls $ \step -> do
          (lss', steps) <- runRight lss rss
          return (lss', step:steps)

    runRight lss [] =
        return (lss, [])

    runRight lss (rs@(IfC _l e c1 c2 s) : rss) =
        joinIf `mplus` divergeIf
      where
        joinIf :: F l m ([Step l], [Step (l, l)])
        joinIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
              (lss1, c1') <- runRight lss (unComp c1)
              (lss2, c2') <- runRight lss (unComp c2)
              guard (lss2 == lss1)
              let step      =  IfC l' e (mkComp c1') (mkComp c2') s
              (lss', steps) <- runRight lss1 rss
              return (lss', step:steps)

        divergeIf :: F l m ([Step l], [Step (l, l)])
        divergeIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
              (_, c1') <- runRight lss (unComp c1 ++ rss)
              (_, c2') <- runRight lss (unComp c2 ++ rss)
              return ([], [IfC l' e (mkComp c1') (mkComp c2') s])

    runRight lss (rs@(WhileC _l e c s) : rss) =
        joinWhile `mplus` divergeWhile
      where
        joinWhile :: F l m ([Step l], [Step (l, l)])
        joinWhile = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
              (lss', c') <- runRight lss (unComp c)
              guard (lss' == lss)
              let step      =  WhileC l' e (mkComp c') s
              (lss', steps) <- runRight lss rss
              return (lss', step:steps)

        divergeWhile :: F l m ([Step l], [Step (l, l)])
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in consumer"
            fusionFailed
            mzero

    -- See the comment in the ForC case for runLeft.
    runRight lss (rs@(ForC _ ann v tau e1 e2 c sloc) : rss) =
        joinFor `mplus` divergeFor
      where
        joinFor :: F l m ([Step l], [Step (l, l)])
        joinFor = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
              (lss', steps) <- runRight lss (unComp c)
              guard (lss' == lss)
              let step      =  ForC l' ann v tau e1 e2 (mkComp steps) sloc
              (lss', steps) <- runRight lss rss
              return (lss', step:steps)

        divergeFor :: F l m ([Step l], [Step (l, l)])
        divergeFor = do
            traceFusion $ text "Encountered diverging for in consumer"
            fusionFailed
            mzero

    runRight lss rss@(TakeC {} : _) =
        runLeft lss rss

    runRight lss rss@(TakesC {} : _) =
        runLeft lss rss

    runRight lss rss@(RepeatC _ ann c _s : _) = do
        l          <- jointLabel lss rss
        l_repeat   <- jointRepeatLabel lss rss
        (lss', ss) <- runRight lss (unComp c ++ rss)
        recoverRepeat l ann l_repeat lss' ss

    runRight _lss (ParC {} : _rss) = do
        traceFusion $ text "Saw nested par in producer during par fusion."
        fusionFailed
        mzero

    runRight lss (rs:rss) = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $
          relabelStep l' rs $ \step -> do
          (lss', steps) <- runRight lss rss
          return (lss', step:steps)

    runLeft :: [Step l] -> [Step l] -> F l m ([Step l], [Step (l, l)])
    runLeft [] rss =
        return (rss, [])

    runLeft (ls@(IfC _l e c1 c2 s) : lss) rss =
        joinIf `mplus` divergeIf
      where
        joinIf :: F l m ([Step l], [Step (l, l)])
        joinIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
              (rss1, c1') <- runLeft (unComp c1) rss
              (rss2, c2') <- runLeft (unComp c2) rss
              guard (rss2 == rss1)
              let step      =  IfC l' e (mkComp c1') (mkComp c2') s
              (rss', steps) <- runLeft lss rss1
              return (rss', step:steps)

        divergeIf :: F l m ([Step l], [Step (l, l)])
        divergeIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
              (_, c1') <- runLeft (unComp c1 ++ lss) rss
              (_, c2') <- runLeft (unComp c2 ++ lss) rss
              return  ([], [IfC l' e (mkComp c1') (mkComp c2') s])

    runLeft (ls@(WhileC _l e c s) : lss) rss =
        joinWhile `mplus` divergeWhile
      where
        joinWhile :: F l m ([Step l], [Step (l, l)])
        joinWhile = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
              (rss', c') <- runLeft (unComp c) rss
              guard (rss' == rss)
              let step      =  WhileC l' e (mkComp c') s
              (rss', steps) <- runLeft lss rss
              return (rss', step:steps)

        divergeWhile :: F l m ([Step l], [Step (l, l)])
        divergeWhile = do
            traceFusion $ text "Encountered diverging while in producer"
            fusionFailed
            mzero

    -- We attempt to fuse a for loop by running the body of the for with the
    -- consumer. If we end up back where we started in the consumer's
    -- computation, that means we can easily construct a new for loop whose body
    -- is the body of the producer's for loop merged with the consumer. This
    -- typically works when the consumer is a repeated computation.
    runLeft (ls@(ForC _ ann v tau e1 e2 c sloc) : lss) rss =
        joinFor `mplus` divergeFor
      where
        joinFor :: F l m ([Step l], [Step (l, l)])
        joinFor = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
              (rss', steps) <- runLeft (unComp c) rss
              guard (rss' == rss)
              let step      =  ForC l' ann v tau e1 e2 (mkComp steps) sloc
              (rss', steps) <- runRight lss rss
              return (rss', step:steps)

        divergeFor :: F l m ([Step l], [Step (l, l)])
        divergeFor = do
            traceFusion $ text "Encountered diverging for in producer"
            fusionFailed
            mzero

    runLeft (EmitC l_left e s1 : lss) (TakeC l_right _tau _s2 : rss) =
        whenNotBeenThere rss l' $ do
          let step      =  ReturnC l' e s1
          (rss', steps) <- runRight (dropBind lss) rss
          return (rss', step:steps)
      where
        l' :: (l, l)
        l' = (l_left, l_right)

    runLeft (lstep@EmitC{} : _) (rstep@TakesC{} : _) = do
        traceFusion $ ppr lstep <+> text "paired with" <+> ppr rstep
        fusionFailed
        mzero

    runLeft (EmitC {} : _) _ =
        faildoc $ text "emit paired with non-take."

    runLeft (EmitsC l_left e s1 : lss) (rs@(TakeC l_right _tau _s2) : rss) =
        whenNotBeenThere rss l' $ do
          -- We can only fuse an emits and a take when we statically know the
          -- size of the array being emitted.
          n <- inferExp e >>= knownArraySize
          if n == 1
            then emits1Take
            else emitsNTake n
      where
        -- If we are emitting an array with only one element, fusion is trivial.
        emits1Take :: F l m ([Step l], [Step (l, l)])
        emits1Take = do
            (rss', steps) <- runRight (dropBind lss) rss
            return (rss', step:steps)
          where
            step :: Step (l, l)
            step = ReturnC l' (idxE e 0) s1

        -- If we are emitting an array with more than one element, we rewrite
        -- the emits as a for loop that yields each element of the array one by
        -- one and try to fuse the rewritten computation.
        emitsNTake :: Int -> F l m ([Step l], [Step (l, l)])
        emitsNTake n = do
            body <- runK $ forC 0 n $ \i -> emitC (idxE e i)
            runLeft (unComp body ++ dropBind lss) (rs : rss)

        l' :: (l, l)
        l' = (l_left, l_right)

    runLeft (EmitsC l_left e s1 : lss)
            (rstep@(TakesC l_right n_right _tau _s2) : rss) =
        whenNotBeenThere rss l' $ do
          n_left <- inferExp e >>= knownArraySize
          when (n_left /= n_right) $ do
              (iota, _) <- inferExp e >>= checkArrT
              traceFusion $ text "emits" <+> ppr iota <+> text "paired with" <+>
                            ppr rstep
              fusionFailed
              mzero
          let step      =  ReturnC l' e s1
          (rss', steps) <- runRight (dropBind lss) rss
          return (rss', step:steps)
      where
        l' :: (l, l)
        l' = (l_left, l_right)

    runLeft (EmitsC {} : _) _ =
        faildoc $ text "emits paired with non-take."

    runLeft lss@(RepeatC _ ann c _s : _) rss = do
        l          <- jointLabel lss rss
        l_repeat   <- jointRepeatLabel lss rss
        (rss', ss) <- runLeft (unComp c ++ lss) rss
        recoverRepeat l ann l_repeat rss' ss

    runLeft (ParC {} : _lss) _rss = do
        traceFusion $ text "Saw nested par in producer during par fusion."
        fusionFailed
        mzero

    runLeft (ls:lss) rss = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $
          relabelStep l' ls $ \step -> do
          (rss', steps) <- runLeft lss rss
          return (rss', step:steps)

    jointLabel :: [Step l] -> [Step l] -> F l m (l, l)
    jointLabel lss rss =
        (,) <$> stepsLabel lss <*> stepsLabel rss
      where
        stepsLabel :: [Step l] -> F l m l
        stepsLabel []       = return klabel
        stepsLabel (step:_) = stepLabel step

    -- | Calculate a joint label for two computations where one or both are
    -- repeat loops. Since we unroll repeats during fusion, the "loop header"
    -- state we are looking for is found by "fast-forwarding" past the repeat
    -- state.
    jointRepeatLabel :: [Step l] -> [Step l] -> F l m (l, l)
    jointRepeatLabel lss rss =
        (,) <$> ffLabel lss <*> ffLabel rss
      where
        ffLabel :: [Step l] -> F l m l
        ffLabel []                    = return klabel
        ffLabel (RepeatC _ _ c _ : _) = ffLabel (unComp c)
        ffLabel (step : _)            = stepLabel step

dropBind :: [Step l] -> [Step l]
dropBind (BindC {} : ss) = ss
dropBind ss              = ss

knownArraySize :: MonadTc m => Type -> F l m Int
knownArraySize tau = do
    (iota, _) <- checkArrT tau
    case iota of
      ConstI n _ -> return n
      _          -> do traceFusion $ text "Unknown array size"
                       fusionFailed
                       mzero

relabelStep :: (IsLabel l1, MonadPlus m, MonadTc m)
            => l2
            -> Step l1
            -> (Step l2 -> m a)
            -> m a
relabelStep _ step@VarC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw variable bound to a computation during fusion"

relabelStep _ step@CallC{} _k =
    withSummaryContext step $
    faildoc $ text "Saw call to a computation function during fusion"

relabelStep l (LetC _ decl@(LetLD v tau _ _) s) k =
    extendVars [(bVar v, tau)] $
    k $ LetC l decl s

relabelStep l (LetC _ decl@(LetRefLD v tau _ _) s) k =
    extendVars [(bVar v, refT tau)] $
    k $ LetC l decl s

relabelStep l (LiftC _ e s) k =
    k $ LiftC l e s

relabelStep l (ReturnC _ e s) k =
    k $ ReturnC l e s

relabelStep l (BindC _ wv tau s) k =
    extendWildVars [(wv, tau)] $
    k $ BindC l wv tau s

relabelStep l (TakeC _ tau s) k =
    k $ TakeC l tau s

relabelStep l (TakesC _ i tau s) k =
    k $ TakesC l i tau s

relabelStep l (EmitC _ e s) k =
    k $ EmitC l e s

relabelStep l (EmitsC _ e s) k =
    k $ EmitsC l e s

relabelStep _ _ _k =
    fail "relabelStep: can't happen"
