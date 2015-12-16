{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Fuse
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Fuse (
    F,
    runF,
    runF1,

    fuseProgram,
    fusePar
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

data FState = FState { seen :: Set (Label, Label) }

type F m a = SEFKT (StateT FState m) a

runF :: MonadErr m => F m a -> FState -> m a
runF m fstate = evalStateT (runSEFKT m) fstate

runF1 :: MonadErr m => F m a -> FState -> m (Maybe a)
runF1 m fstate = evalStateT (runSEFKT1 m) fstate

sawLabel :: (MonadPlus m, MonadTc m) => (Label, Label) -> F m Bool
sawLabel l = gets (Set.member l . seen)

recordLabel :: (MonadPlus m, MonadTc m) => (Label, Label) -> F m ()
recordLabel l = modify $ \s -> s { seen = Set.insert l (seen s) }

jointLabel :: (MonadPlus m, MonadTc m) => [LStep] -> [LStep] -> F m (Label, Label)
jointLabel lss rss = (,) <$> stepLabel (head lss) <*> stepLabel (head rss)

-- | Calculate a joint label for two computations where one or both are repeat
-- loops. Since we unroll repeats during fusion, the "loop header" state we are
-- looking for is found by "fast-forwarding" past the repeat state.
jointRepeatLabel :: forall m l . (Applicative m, Monad m)
                 => [Step l] -> [Step l] -> m (l, l)
jointRepeatLabel lss rss =
    (,) <$> ffLabel lss <*> ffLabel rss
  where
    ffLabel :: Monad m => [Step l] -> m l
    ffLabel []                    = fail "ffLabel: empty computation"
    ffLabel (RepeatC _ _ c _ : _) = ffLabel (unComp c)
    ffLabel (step : _)            = stepLabel step

runRepeat :: (IsLabel l, Monad m)
          => (l, l)
          -> [Step l]
          -> [Step (l, l)]
          -> m ([Step l], [Step (l, l)])
          -> m ([Step l], [Step (l, l)])
runRepeat l_repeat ss_other ss k
    | ss      == [LoopC l_repeat] = return (ss_other, ss)
    | last ss == LoopC l_repeat   = k
    | otherwise                   = return (ss_other, ss)

whenNotBeenThere :: (MonadPlus m, MonadTc m)
                 => [LStep]
                 -> (Label,Label)
                 -> F m ([LStep], [Step (Label, Label)])
                 -> F m ([LStep], [Step (Label, Label)])
whenNotBeenThere ss l k = do
    beenThere <- sawLabel l
    if beenThere
      then return (ss, [LoopC l])
      else recordLabel l >> k

fuseProgram :: forall m . (MonadPlus m, MonadTc m) => LProgram -> m LProgram
fuseProgram prog =
    fuse prog `mplus` return prog
  where
    fuse :: LProgram -> m LProgram
    fuse (Program decls comp tau) =
        fuseDecls decls $
        inSTScope tau $
        inLocalScope $ do
        comp' <- withLocContext comp (text "In definition of main") $
                 fuseComp comp
        return $ Program decls comp' tau

fuseDecls :: (MonadPlus m, MonadTc m) => [LDecl] -> m a -> m a
fuseDecls [] k =
    k

fuseDecls (decl:decls) k =
    fuseDecl decl $ fuseDecls decls k

fuseDecl :: (MonadPlus m, MonadTc m) => LDecl -> m a -> m a
fuseDecl (LetD decl _) k =
    fuseLocalDecl decl k

fuseDecl (LetFunD f iotas vbs tau_ret _ l) k =
    extendVars [(bVar f, tau)] k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

fuseDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(bVar f, tau)] k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

fuseDecl (LetStructD s flds l) k =
    extendStructs [StructDef s flds l] k

fuseDecl (LetCompD v tau _ _) k =
    extendVars [(bVar v, tau)] k

fuseDecl (LetFunCompD f ivs vbs tau_ret _ l) k =
    extendVars [(bVar f, tau)] k
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

fuseLocalDecl :: (MonadPlus m, MonadTc m) => LocalDecl -> m a -> m a
fuseLocalDecl (LetLD v tau _ _) k =
    extendVars [(bVar v, tau)] k

fuseLocalDecl (LetRefLD v tau _ _) k =
    extendVars [(bVar v, refT tau)] k

fuseComp :: (MonadPlus m, MonadTc m) => LComp -> m LComp
fuseComp (Comp steps) = Comp <$> fuseSteps steps

fuseSteps :: (MonadPlus m, MonadTc m) => [LStep] -> m [LStep]
fuseSteps [] =
    return []

fuseSteps (step@(LetC _ decl _) : steps) =
    fuseLocalDecl decl $
    (:) <$> pure step <*> fuseSteps steps

fuseSteps (step@(BindC _ wv tau _) : steps) =
    extendWildVars [(wv, tau)] $
    (:) <$> pure step <*> fuseSteps steps

fuseSteps (step : steps) =
    (++) <$> fuseStep step <*> fuseSteps steps

fuseStep :: (MonadPlus m, MonadTc m) => LStep -> m [LStep]
fuseStep step@(VarC {}) =
    return [step]

fuseStep step@(CallC {}) =
    return [step]

fuseStep (IfC l e c1 c2 s) = do
    step <- IfC l e <$> fuseComp c1 <*> fuseComp c2 <*> pure s
    return [step]

fuseStep (LetC {}) =
    faildoc $ text "Cannot fuse let step."

fuseStep (WhileC l e c s) = do
    step <- WhileC l e <$> fuseComp c <*> pure s
    return [step]

fuseStep (ForC l ann v tau e1 e2 c s) = do
    step <- ForC l ann v tau e1 e2 <$> fuseComp c <*> pure s
    return [step]

fuseStep step@(LiftC {}) =
    return [step]

fuseStep step@(ReturnC {}) =
    return [step]

fuseStep (BindC {}) =
    faildoc $ text "Cannot fuse bind step."

fuseStep step@(TakeC {}) =
    return [step]

fuseStep step@(TakesC {}) =
    return [step]

fuseStep step@(EmitC {}) =
    return [step]

fuseStep step@(EmitsC {}) =
    return [step]

fuseStep (RepeatC l ann c s) = do
    step <- RepeatC l ann <$> fuseComp c <*> pure s
    return [step]

fuseStep step@(ParC _ann b c1 c2 _s) = do
    (s, a, c) <- askSTIndTypes
    tau       <- inferStep step
    comp      <- fusePar s a b c c1 c2
    checkComp comp tau
    return $ unComp comp

fuseStep (LoopC {}) =
    faildoc $ text "fuseStep: saw LoopC"

fusePar :: forall m . (MonadPlus m, MonadTc m)
        => Type -> Type -> Type -> Type
        -> LComp
        -> LComp
        -> m LComp
fusePar s a b c left right = do
    left'  <- localSTIndTypes (Just (s, a, b)) $
              fuseComp left
    -- We need to make sure that the producer and consumer have unique sets of
    -- binders, so we freshen all binders in the consumer. Why the consumer?
    -- Because >>> is left-associative, so we hopefully avoid repeated re-naming
    -- of binders by renaming the consumer.
    let unquify :: Subst Exp Var a => a -> a
        unquify = subst (mempty :: Map Var Exp) (allVars left' <> allVars right :: Set Var)
    right' <- localSTIndTypes (Just (b, b, c)) $
              unquify <$> fuseComp right
    l      <- compLabel right'
    comp   <- fuse left' right' >>= mapCompLabels pair >>= setFirstLabel l
    traceFusion $ text "Fused" <+>
        (nest 2 $ text "producer:" </> ppr left') </>
        (nest 2 $ text "and consumer:" </> ppr right') </>
        (nest 2 $ text "into:" </> ppr comp)
    return comp
  where
    setFirstLabel :: Label -> Comp Label -> m (Comp Label)
    setFirstLabel l' comp = do
        l <- compLabel comp
        return $ subst1 (l /-> l') comp

    pair :: (Label, Label) -> m Label
    pair (Label l1 _, Label l2 _) = do
        u <- newUnique
        let l' = displayS (renderCompact (parens (text (unintern l1) <> comma <> text (unintern l2)))) ""
        return $ Label (intern l') (Just u)

fuse :: forall m . (MonadPlus m, MonadTc m)
     => LComp
     -> LComp
     -> m (Comp (Label, Label))
fuse left right = do
    maybe_res <- runF1 (runRight (unComp left) (unComp right)) fstate
    case maybe_res of
      Nothing        -> mzero
      Just (_, rss') -> return $ Comp rss'
  where
    fstate :: FState
    fstate = FState mempty

    runRight :: [LStep] -> [LStep] -> F m ([LStep], [Step (Label, Label)])
    runRight lss [] =
        return (lss, [])

    runRight lss (rs@(IfC _ e c1 c2 s) : rss) =
        joinIf `mplus` divergeIf
      where
        joinIf :: F m ([LStep], [Step (Label, Label)])
        joinIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
            (lss1, c1') <- runRight lss (unComp c1)
            (lss2, c2') <- runRight lss (unComp c2)
            guard (lss2 == lss1)
            let step      =  IfC l' e (Comp c1') (Comp c2') s
            (lss', steps) <- runRight lss rss
            return (lss', step:steps)

        divergeIf :: F m ([LStep], [Step (Label, Label)])
        divergeIf = do
            l' <- jointLabel lss (rs:rss)
            whenNotBeenThere lss l' $ do
            (_, c1') <- runRight lss (unComp c1 ++ rss)
            (_, c2') <- runRight lss (unComp c2 ++ rss)
            return ([], [IfC l' e (Comp c1') (Comp c2') s])

    runRight _lss (WhileC {} : _rss) =
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

    runRight _lss (ParC {} : _rss) =
        faildoc $ text "Saw nested par in consumer during par fusion."

    runRight lss (rs:rss) = do
        l' <- jointLabel lss (rs:rss)
        whenNotBeenThere lss l' $ do
        relabelStep l' rs $ \step -> do
        (lss', steps) <- runRight lss rss
        return (lss', step:steps)

    runLeft :: [LStep] -> [LStep] -> F m ([LStep], [Step (Label, Label)])
    runLeft [] rss =
        return (rss, [])

    runLeft (ls@(IfC _ e c1 c2 s) : lss) rss =
        joinIf `mplus` divergeIf
      where
        joinIf :: F m ([LStep], [Step (Label, Label)])
        joinIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
            (rss1, c1') <- runLeft (unComp c1) rss
            (rss2, c2') <- runLeft (unComp c2) rss
            guard (rss2 == rss1)
            let step      =  IfC l' e (Comp c1') (Comp c2') s
            (rss', steps) <- runLeft lss rss
            return (rss', step:steps)

        divergeIf :: F m ([LStep], [Step (Label, Label)])
        divergeIf = do
            l' <- jointLabel (ls:lss) rss
            whenNotBeenThere rss l' $ do
            (_, c1') <- runLeft (unComp c1 ++ lss) rss
            (_, c2') <- runLeft (unComp c2 ++ lss) rss
            return  ([], [IfC l' e (Comp c1') (Comp c2') s])

    runLeft (WhileC {} : _lss) _rss =
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
        (rss', steps) <- runRight lss rss
        return (rss', step:steps)
      where
        l' :: (Label, Label)
        l' = (l_left, l_right)

    runLeft (EmitC {} : _) (TakesC {} : _) =
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
        emits1Take :: F m ([LStep], [Step (Label, Label)])
        emits1Take = do
            (rss', steps) <- runRight lss rss
            return (rss', step:steps)
          where
            step :: Step (Label,Label)
            step = ReturnC l' (idxE e 0) s1

        -- If we are emitting an array with more than one element, we rewrite
        -- the emits as a for loop that yields each element of the array one by
        -- one and try to fuse the rewritten computation.
        emitsNTake :: Int -> F m ([LStep], [Step (Label, Label)])
        emitsNTake n = do
            i    <- gensymAt "i" s1
            -- XXX We need the empty return so that the emit has a
            -- continuation...so that we can take its label to find a joint
            -- label.
            body <- emitC (idxE e (varE i)) .>>. returnC unitE
            fori <- forC AutoUnroll i intT 0 (fromIntegral n) body
            runLeft (unComp fori ++ lss) (rs : rss)

        l' :: (Label, Label)
        l' = (l_left, l_right)

    runLeft (EmitsC l_left e s1 : lss) (TakesC l_right n_right _tau _s2 : rss) =
        whenNotBeenThere rss l' $ do
        n_left <- inferExp e >>= knownArraySize
        when (n_left /= n_right)
            mzero
        let step      =  ReturnC l' e s1
        (rss', steps) <- runRight lss rss
        return (rss', step:steps)
      where
        l' :: (Label, Label)
        l' = (l_left, l_right)

    runLeft (EmitsC {} : _) _ =
        faildoc $ text "emits paired with non-take."

    runLeft lss@(RepeatC _ ann c s : _) rss = do
        l          <- jointLabel lss rss
        l_repeat   <- jointRepeatLabel lss rss
        (rss', ss) <- traceNest $ runLeft (unComp c ++ lss) rss
        runRepeat l_repeat rss' ss $
            return (rss', [RepeatC l ann (Comp (init ss)) s])

    runLeft (ParC {} : _lss) _rss =
        faildoc $ text "Saw nested par in producer during par fusion."

    runLeft (ls:lss) rss = do
        l'  <- jointLabel (ls:lss) rss
        whenNotBeenThere rss l' $ do
        relabelStep l' ls $ \step -> do
        (rss', steps) <- runLeft lss rss
        return (rss', step:steps)

knownArraySize :: (MonadPlus m, MonadTc m) => Type -> m Int
knownArraySize tau = do
    (iota, _) <- checkArrT tau
    case iota of
      ConstI n _ -> return n
      _          -> mzero

relabelStep :: (IsLabel l1, MonadPlus m, MonadTc m)
            => l2
            -> Step l1
            -> (Step l2 -> m a)
            -> m a
relabelStep _ step@(VarC {}) _k =
    withSummaryContext step $
    faildoc $ text "Saw variable bound to a computation during fusion"

relabelStep _ step@(CallC {}) _k =
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
