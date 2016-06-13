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
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

data FEnv l = FEnv { kont :: l }

defaultFEnv :: FEnv l
defaultFEnv = FEnv { kont = error "no continuation label" }

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

newtype F l m a = F { unF :: ReaderT (FEnv l)
                               (WriterT (Seq (Step (l, l)))
                                 (StateT (FState l)
                                   (SEFKT (StateT FusionStats m)))) a }
    deriving (Functor, Applicative, Monad,
              Alternative, MonadPlus,
              MonadIO,
              MonadReader (FEnv l),
              MonadWriter (Seq (Step (l, l))),
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
runF m = fst <$> evalStateT
                   (runSEFKT
                     (evalStateT
                       (runWriterT
                         (runReaderT (unF m) defaultFEnv))
                       defaultFState))
                   mempty

withKont :: (IsLabel l, MonadTc m) => [Step l] -> F l m a -> F l m a
withKont [] m = do
    klabel <- gensym "end"
    local (\env -> env { kont = klabel }) m

withKont (step:_) m = do
    klabel <- stepLabel step
    local (\env -> env { kont = klabel }) m

currentKont :: MonadTc m => F l m l
currentKont = asks kont

stepsLabel :: MonadTc m => [Step l] -> F l m l
stepsLabel []         = currentKont
stepsLabel (step : _) = stepLabel step

jointStep :: (IsLabel l, MonadTc m) => Step (l, l) -> F l m ()
jointStep step = tell (Seq.singleton step)

jointSteps :: (IsLabel l, MonadTc m) => [Step (l, l)] -> F l m ()
jointSteps steps = tell (Seq.fromList steps)

collectSteps :: MonadTc m => F l m a -> F l m (a, [Step (l, l)])
collectSteps m =
    censor (const mempty) $ do
    (x, steps) <- listen m
    return (x, toList steps)

sawLabel :: (IsLabel l, MonadTc m)
         => (l, l) -> F l m Bool
sawLabel l = gets (Set.member l . seen)

recordLabel :: (IsLabel l, MonadTc m)
            => (l, l) -> F l m ()
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
      steps1    <- fusePar c1' c2' `mplus` return [ParC ann b c1' c2' sloc]
      steps'    <- stepsT steps
      return $ steps1 ++ steps'
    where
      fusePar :: Comp l -> Comp l -> F l m [Step l]
      fusePar left right0 = do
          l    <- compLabel right0
          comp <- withKont steps $
                  fuse left right >>=
                  setFirstLabel l
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
              => (l, l)         -- ^ The label to be used for the resulting
                                -- repeat
              -> VectAnn        -- ^ Annotation for the resulting repeat
              -> (l, l)         -- ^ Label of the loop header
              -> F l m [Step l] -- ^ Body of the repeat
              -> F l m [Step l] -- ^ Remaining steps or the other side of the
                                -- par.
recoverRepeat l ann l_repeat k =do
    (ss_other, ss) <- collectSteps k
    if isNonEmptyRepeatLoop ss
      then jointStep $ mkRepeat (init ss)
      else jointSteps ss
    return ss_other
  where
    mkRepeat :: [Step (l, l)] -> Step (l, l)
    mkRepeat steps = RepeatC l ann (mkComp steps) (srclocOf steps)

    isNonEmptyRepeatLoop :: [Step (l, l)] -> Bool
    isNonEmptyRepeatLoop steps =
        length steps > 1 && last steps == LoopC l_repeat

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
                 -> F l m [Step l]
                 -> F l m [Step l]
whenNotBeenThere ss l k = do
    beenThere <- sawLabel l
    if beenThere
      then do jointStep $ LoopC l
              return ss
      else recordLabel l >> k

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l         -- ^ Left computation
     -> Comp l         -- ^ Right computation
     -> F l m (Comp l)
fuse left right = do
    (_, rss') <- collectSteps $ runRight (unComp left) (unComp right)
    return $ uncurry pairLabel <$> mkComp rss'

runRight :: forall l m . (IsLabel l, MonadTc m)
         => [Step l]
         -> [Step l]
         -> F l m [Step l]
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
      relabelStep l' ls $
      runRight lss rss
  where
    -- | A "free" left step is one we can go ahead and run even if the
    -- right-hand side has not yet reached a take action.
    isFreeLeftStep :: Step l -> Bool
    isFreeLeftStep LetC{}    = True
    isFreeLeftStep LiftC{}   = True
    isFreeLeftStep ReturnC{} = True
    isFreeLeftStep BindC{}   = True
    isFreeLeftStep _         = False

runRight lss [] =
    return lss

runRight lss (rs@(IfC _l e c1 c2 s) : rss) =
    joinIf `mplus` divergeIf
  where
    joinIf :: F l m [Step l]
    joinIf = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
          (lss1, c1') <- collectSteps $
                         withKont rss $
                         runRight lss (unComp c1)
          (lss2, c2') <- collectSteps $
                         withKont rss $
                         runRight lss (unComp c2)
          guard (lss2 == lss1)
          jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
          runRight lss1 rss

    divergeIf :: F l m [Step l]
    divergeIf = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
          (_, c1') <- collectSteps $ runRight lss (unComp c1 ++ rss)
          (_, c2') <- collectSteps $ runRight lss (unComp c2 ++ rss)
          jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
          return []

runRight lss (rs@(WhileC _l e c s) : rss) =
    joinWhile `mplus` divergeWhile
  where
    joinWhile :: F l m [Step l]
    joinWhile = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
          (lss', c') <- collectSteps $
                        withKont rss $
                        runRight lss (unComp c)
          guard (lss' == lss)
          jointStep $ WhileC l' e (mkComp c') s
          runRight lss rss

    divergeWhile :: F l m [Step l]
    divergeWhile = do
        traceFusion $ text "Encountered diverging while in consumer"
        fusionFailed
        mzero

-- See the comment in the ForC case for runLeft.
runRight lss (rs@(ForC _ ann v tau e1 e2 c sloc) : rss) =
    joinFor `mplus` divergeFor
  where
    joinFor :: F l m [Step l]
    joinFor = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
          (lss', steps) <- collectSteps $
                           withKont rss $
                           runRight lss (unComp c)
          guard (lss' == lss)
          jointStep $ ForC l' ann v tau e1 e2 (mkComp steps) sloc
          runRight lss rss

    divergeFor :: F l m [Step l]
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
    recoverRepeat l ann l_repeat $
      runRight lss (unComp c ++ rss)

runRight _lss (ParC {} : _rss) =
    nestedPar

runRight lss (rs:rss) = do
    l' <- jointLabel lss (rs:rss)
    whenNotBeenThere lss l' $
      relabelStep l' rs $
      runRight lss rss

runLeft :: forall l m . (IsLabel l, MonadTc m)
        => [Step l]
        -> [Step l]
        -> F l m [Step l]
runLeft [] rss =
    return rss

runLeft (ls@(IfC _l e c1 c2 s) : lss) rss =
    joinIf `mplus` divergeIf
  where
    joinIf :: F l m [Step l]
    joinIf = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
          (rss1, c1') <- collectSteps $
                         withKont lss $
                         runLeft (unComp c1) rss
          (rss2, c2') <- collectSteps $
                         withKont lss $
                         runLeft (unComp c2) rss
          guard (rss2 == rss1)
          jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
          runLeft lss rss1

    divergeIf :: F l m [Step l]
    divergeIf = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
          (_, c1') <- collectSteps $ runLeft (unComp c1 ++ lss) rss
          (_, c2') <- collectSteps $ runLeft (unComp c2 ++ lss) rss
          jointStep $ IfC l' e (mkComp c1') (mkComp c2') s
          return []

runLeft (ls@(WhileC _l e c s) : lss) rss =
    joinWhile `mplus` divergeWhile
  where
    joinWhile :: F l m [Step l]
    joinWhile = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
          (rss', c') <- collectSteps $
                        withKont lss $
                        runLeft (unComp c) rss
          guard (rss' == rss)
          jointStep $ WhileC l' e (mkComp c') s
          runLeft lss rss

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
runLeft (ls@(ForC _ ann v tau e1 e2 c sloc) : lss) rss =
    joinFor `mplus` divergeFor
  where
    joinFor :: F l m [Step l]
    joinFor = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
          (rss', steps) <- collectSteps $
                           withKont lss $
                           runLeft (unComp c) rss
          guard (rss' == rss)
          jointStep $ ForC l' ann v tau e1 e2 (mkComp steps) sloc
          runRight lss rss

    divergeFor :: F l m [Step l]
    divergeFor = do
        traceFusion $ text "Encountered diverging for in producer"
        fusionFailed
        mzero

runLeft (EmitC _ e _ : lss) (TakeC{} : rss) =
    emitTake e lss rss

runLeft (lstep@EmitC{} : _) (rstep@TakesC{} : _) = do
    traceFusion $ ppr lstep <+> text "paired with" <+> ppr rstep
    fusionFailed
    mzero

runLeft (EmitC {} : _) _ =
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
        runLeft (unComp body ++ lss) (rs : rss)

runLeft (EmitsC _ e _ : lss) (rs@(TakesC _ n' _ _) : rss) = do
    n <- inferExp e >>= knownArraySize
    when (n' /= n) $ do
        (iota, _) <- inferExp e >>= checkArrT
        traceFusion $ text "emits" <+> ppr iota <+> text "paired with" <+>
                      ppr rs
        fusionFailed
        mzero
    emitTake e lss rss

runLeft (EmitsC {} : _) _ =
    faildoc $ text "emits paired with non-take."

runLeft lss@(RepeatC _ ann c _s : _) rss = do
    l        <- jointLabel lss rss
    l_repeat <- jointRepeatLabel lss rss
    recoverRepeat l ann l_repeat $
      runLeft (unComp c ++ lss) rss

runLeft (ParC {} : _lss) _rss =
    nestedPar

runLeft (ls:lss) rss = do
    l' <- jointLabel (ls:lss) rss
    whenNotBeenThere rss l' $
      relabelStep l' ls $
      runLeft lss rss

jointLabel :: (IsLabel l, MonadTc m)
           => [Step l]
           -> [Step l]
           -> F l m (l, l)
jointLabel lss rss =
    (,) <$> stepsLabel lss <*> stepsLabel rss

-- | Calculate a joint label for two computations where one or both are
-- repeat loops. Since we unroll repeats during fusion, the "loop header"
-- state we are looking for is found by "fast-forwarding" past the repeat
-- state.
jointRepeatLabel :: forall l m . (IsLabel l, MonadTc m)
                 => [Step l]
                 -> [Step l]
                 -> F l m (l, l)
jointRepeatLabel lss rss =
    (,) <$> ffLabel lss <*> ffLabel rss
  where
    ffLabel :: [Step l] -> F l m l
    ffLabel []                    = currentKont
    ffLabel (RepeatC _ _ c _ : _) = ffLabel (unComp c)
    ffLabel (step : _)            = stepLabel step

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

relabelStep :: (IsLabel l, MonadTc m)
            => (l, l)
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
