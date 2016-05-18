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
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Core.Comp
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

newtype FState l = FState { seen :: Set l }

newtype F l m a = F { unF :: SEFKT (StateT (FState l) m) a }
    deriving (Functor, Applicative, Monad,
              Alternative, MonadPlus,
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
runF m = evalStateT (runSEFKT (unF m)) fstate
  where
    fstate :: FState l
    fstate = FState mempty

sawLabel :: (IsLabel l, MonadTc m)
         => l -> F l m Bool
sawLabel l = gets (Set.member l . seen)

recordLabel :: (IsLabel l, MonadTc m)
            => l -> F l m ()
recordLabel l = modify $ \s -> s { seen = Set.insert l (seen s) }

jointLabel :: (IsLabel l, MonadTc m)
           => [Step l] -> [Step l] -> F l m l
jointLabel lss rss = pairLabel <$> stepLabel (head lss) <*> stepLabel (head rss)

fuseProgram :: forall l m . (IsLabel l, MonadPlus m, MonadTc m)
            => Program l -> m (Program l)
fuseProgram prog = runF (programT prog :: F l m (Program l))

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
          comp <- fuse left right >>= setFirstLabel l
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

-- | Calculate a joint label for two computations where one or both are repeat
-- loops. Since we unroll repeats during fusion, the "loop header" state we are
-- looking for is found by "fast-forwarding" past the repeat state.
jointRepeatLabel :: forall l m . (IsLabel l, Applicative m, Monad m)
                 => [Step l] -> [Step l] -> m l
jointRepeatLabel lss rss =
    pairLabel <$> ffLabel lss <*> ffLabel rss
  where
    ffLabel :: Monad m => [Step l] -> m l
    ffLabel []                    = fail "ffLabel: empty computation"
    ffLabel (RepeatC _ _ c _ : _) = ffLabel (unComp c)
    ffLabel (step : _)            = stepLabel step

runRepeat :: (IsLabel l, Monad m)
          => l
          -> [Step l]
          -> [Step l]
          -> m ([Step l], [Step l])
          -> m ([Step l], [Step l])
runRepeat l_repeat ss_other ss k
    | ss      == [LoopC l_repeat] = return (ss_other, ss)
    | last ss == LoopC l_repeat   = k
    | otherwise                   = return (ss_other, ss)

-- | Given a list of computation steps for the "other" side of the
-- producer/consumer loop and a label, @l@, for the current joint
-- producer/consumer state, see if we have been in the current state before. If
-- we have, return the remaining "other" side of the computation and the single
-- step @'LoopC' l@, which indicates that we have encountered a loop. Otherwise,
-- record the fact that we have seen the label @l@ and call our
-- continuation. The function 'whenNotBeenThere' is the only way a 'LoopC' step
-- can be introduced into a computation.
whenNotBeenThere :: (IsLabel l, MonadTc m)
                 => [Step l]
                 -> l
                 -> F l m ([Step l], [Step l])
                 -> F l m ([Step l], [Step l])
whenNotBeenThere ss l k = do
    beenThere <- sawLabel l
    if beenThere
      then return (ss, [LoopC l])
      else recordLabel l >> k

fuse :: forall l m . (IsLabel l, MonadTc m)
     => Comp l
     -> Comp l
     -> F l m (Comp l)
fuse left right = do
    (_, rss') <- runRight (unComp left) (unComp right)
    return $ Comp rss'
  where
    runRight :: [Step l] -> [Step l] -> F l m ([Step l], [Step l])
    runRight lss [] =
        return (lss, [])

    runRight lss (rs@(IfC _ e c1 c2 s) : rss) =
        joinIf `mplus` divergeIf
      where
        joinIf :: F l m ([Step l], [Step l])
        joinIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
            (lss1, c1') <- runRight lss (unComp c1)
            (lss2, c2') <- runRight lss (unComp c2)
            guard (lss2 == lss1)
            let step      =  IfC l' e (Comp c1') (Comp c2') s
            (lss', steps) <- runRight lss rss
            return (lss', step:steps)

        divergeIf :: F l m ([Step l], [Step l])
        divergeIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
            (_, c1') <- runRight lss (unComp c1 ++ rss)
            (_, c2') <- runRight lss (unComp c2 ++ rss)
            return ([], [IfC l' e (Comp c1') (Comp c2') s])

    runRight _lss (WhileC {} : _rss) = do
        traceFusion $ text "Encountered while in consumer"
        mzero

    -- See the comment in the ForC case for runLeft.
    runRight lss (rs@(ForC _ ann v tau e1 e2 c sloc) : rss) = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
        (lss', steps) <- runRight lss (unComp c)
        guard (lss' == lss)
        let step      =  ForC l' ann v tau e1 e2 (Comp steps) sloc
        (lss', steps) <- runRight lss rss
        return (lss', step:steps)

    runRight lss rss@(TakeC {} : _) =
        runLeft lss rss

    runRight lss rss@(TakesC {} : _) =
        runLeft lss rss

    runRight lss rss@(RepeatC _ ann c s : _) = do
        l          <- jointLabel lss rss
        l_repeat   <- jointRepeatLabel lss rss
        (lss', ss) <- traceNest $ runRight lss (unComp c ++ rss)
        runRepeat l_repeat lss' ss $
            return (lss', [RepeatC l ann (Comp (init ss)) s])

    runRight _lss (ParC {} : _rss) = do
        traceFusion $ text "Saw nested par in producer during par fusion."
        mzero

    runRight lss (rs:rss) = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $
          relabelStep l' rs $ \step -> do
          (lss', steps) <- runRight lss rss
          return (lss', step:steps)

    runLeft :: [Step l] -> [Step l] -> F l m ([Step l], [Step l])
    runLeft [] rss =
        return (rss, [])

    runLeft (ls@(IfC _ e c1 c2 s) : lss) rss =
        joinIf `mplus` divergeIf
      where
        joinIf :: F l m ([Step l], [Step l])
        joinIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
            (rss1, c1') <- runLeft (unComp c1) rss
            (rss2, c2') <- runLeft (unComp c2) rss
            guard (rss2 == rss1)
            let step      =  IfC l' e (Comp c1') (Comp c2') s
            (rss', steps) <- runLeft lss rss
            return (rss', step:steps)

        divergeIf :: F l m ([Step l], [Step l])
        divergeIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
            (_, c1') <- runLeft (unComp c1 ++ lss) rss
            (_, c2') <- runLeft (unComp c2 ++ lss) rss
            return  ([], [IfC l' e (Comp c1') (Comp c2') s])

    runLeft (WhileC {} : _lss) _rss = do
        traceFusion $ text "Encountered while in producer"
        mzero

    -- We attempt to fuse a for loop by running the body of the for with the
    -- consumer. If we end up back where we started in the consumer's
    -- computation, that means we can easily construct a new for loop whose body
    -- is the body of the producer's for loop merged with the consumer. This
    -- typically works when the consumer is a repeated computation.
    runLeft (ls@(ForC _ ann v tau e1 e2 c sloc) : lss) rss = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
        (rss', steps) <- runLeft (unComp c) rss
        guard (rss' == rss)
        let step      =  ForC l' ann v tau e1 e2 (Comp steps) sloc
        (rss', steps) <- runRight lss rss
        return (rss', step:steps)

    runLeft (EmitC l_left e s1 : lss) (TakeC l_right _tau _s2 : rss) =
        whenNotBeenThere rss l' $ do
        let step      =  ReturnC l' e s1
        (rss', steps) <- runRight (dropBind lss) rss
        return (rss', step:steps)
      where
        l' :: l
        l' = pairLabel l_left l_right

    runLeft (EmitC {} : _) (TakesC {} : _) = do
        traceFusion $ text "emit paired with takes"
        mzero

    runLeft (EmitC {} : _) _ =
        faildoc $ text "emit paired with non-take."

    runLeft (EmitsC l_left e s1 : lss) (rs@(TakeC l_right _tau _s2) : rss) =
        whenNotBeenThere rss l' $ do
        -- We can only fuse an emits and a take when we statically know the size
        -- of the array being emitted.
        n <- inferExp e >>= knownArraySize
        if n == 1
          then emits1Take
          else emitsNTake n
      where
        -- If we are emitting an array with only one element, fusion is trivial.
        emits1Take :: F l m ([Step l], [Step l])
        emits1Take = do
            (rss', steps) <- runRight (dropBind lss) rss
            return (rss', step:steps)
          where
            step :: Step l
            step = ReturnC l' (idxE e 0) s1

        -- If we are emitting an array with more than one element, we rewrite
        -- the emits as a for loop that yields each element of the array one by
        -- one and try to fuse the rewritten computation.
        emitsNTake :: Int -> F l m ([Step l], [Step l])
        emitsNTake n = do
            i    <- gensymAt "i" s1
            -- XXX We need the empty return so that the emit has a
            -- continuation...so that we can take its label to find a joint
            -- label.
            body <- emitC (idxE e (varE i)) .>>. returnC unitE
            fori <- forC AutoUnroll i intT 0 (fromIntegral n) body
            runLeft (unComp fori ++ dropBind lss) (rs : rss)

        l' :: l
        l' = pairLabel l_left l_right

    runLeft (EmitsC l_left e s1 : lss) (TakesC l_right n_right _tau _s2 : rss) =
        whenNotBeenThere rss l' $ do
        n_left <- inferExp e >>= knownArraySize
        when (n_left /= n_right) $ do
            traceFusion $ text "emits paired with takes with incompatible size"
            mzero
        let step      =  ReturnC l' e s1
        (rss', steps) <- runRight (dropBind lss) rss
        return (rss', step:steps)
      where
        l' :: l
        l' = pairLabel l_left l_right

    runLeft (EmitsC {} : _) _ =
        faildoc $ text "emits paired with non-take."

    runLeft lss@(RepeatC _ ann c s : _) rss = do
        l          <- jointLabel lss rss
        l_repeat   <- jointRepeatLabel lss rss
        (rss', ss) <- traceNest $ runLeft (unComp c ++ lss) rss
        runRepeat l_repeat rss' ss $
            return (rss', [RepeatC l ann (Comp (init ss)) s])

    runLeft (ParC {} : _lss) _rss = do
        traceFusion $ text "Saw nested par in producer during par fusion."
        mzero

    runLeft (ls:lss) rss = do
        l' <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $
          relabelStep l' ls $ \step -> do
          (rss', steps) <- runLeft lss rss
          return (rss', step:steps)

dropBind :: [Step l] -> [Step l]
dropBind (BindC {} : ss) = ss
dropBind ss              = ss

knownArraySize :: (MonadPlus m, MonadTc m) => Type -> m Int
knownArraySize tau = do
    (iota, _) <- checkArrT tau
    case iota of
      ConstI n _ -> return n
      _          -> do traceFusion $ text "Unknown array size"
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
