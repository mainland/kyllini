{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Optimize.Eval
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Eval (
    evalProgram,
    toExp
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad ((>=>),
                      filterM,
                      zipWithM,
                      zipWithM_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Primitive (RealWorld)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Bits
import Data.Foldable (toList)
import Data.List (partition)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Ratio (numerator)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Analysis.Lut
import KZC.Core.Comp
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Interp (evalI)
import qualified KZC.Interp as I
import KZC.Label
import KZC.Name
import KZC.Optimize.Eval.Monad
import qualified KZC.Optimize.Eval.PArray as P
import KZC.Optimize.Eval.Val
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Util.SetLike
import KZC.Vars

-- | Return 'True' if we should partially-evaluate.
peval :: Flags -> Bool
peval = testDynFlag PartialEval

evalProgram :: (IsLabel l, MonadTcRef m)
            => Program l
            -> m (Program l)
evalProgram (Program decls comp tau) =
    evalEvalM $
    evalDecls decls $ \mkDecls ->
    inSTScope tau $
    inLocalScope $
    withLocContext comp (text "In definition of main") $ do
    val         <- evalComp comp
    (h', comp') <- case val of
                     CompReturnV {}  -> do h'    <- freezeHeap
                                           comp' <- toComp val
                                           return (h', comp')
                     CompV h' steps' -> return (h', mkComp  steps')
                     _               -> faildoc $ nest 2 $
                                        text "Computation did not return CompReturnV or CompV:" </>
                                        ppr val
    (sdecls1, decls1) <- partition isStructD <$> mkDecls h'
    (sdecls2, decls2) <- partition isStructD <$> getTopDecls
    return $ Program (sdecls1 ++ sdecls2 ++ decls1 ++ decls2) comp' tau

evalDecls :: (IsLabel l, MonadTcRef m)
          => [Decl l]
          -> ((FrozenHeap l m -> EvalM l m [Decl l]) -> EvalM l m a)
          -> EvalM l m a
evalDecls [] k =
    k $ \_h -> return []

evalDecls (decl:decls) k =
    evalDecl  decl  $ \mkDecl' ->
    evalDecls decls $ \mkDecls' ->
    k $ \h -> (:) <$> mkDecl' h <*> mkDecls' h

evalDecl :: forall l m a . (IsLabel l, MonadTcRef m)
         => Decl l
         -> ((FrozenHeap l m -> EvalM l m (Decl l)) -> EvalM l m a)
         -> EvalM l m a
evalDecl (LetD decl s) k =
    evalLocalDecl decl go
  where
    go :: LocalLetVal l m -> EvalM l m a
    go (DeclVal decl') =
        k $ \_h -> return $ LetD decl' s

    go (HeapDeclVal mkDecl) =
        k $ \h -> LetD <$> mkDecl h <*> pure s

evalDecl decl@(LetFunD f ivs vbs tau_ret e l) k =
    withSummaryContext decl $
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' ->
      withUniqVars vs $ \vs' -> do
      e' <- killHeap $
            extendLetFun f' ivs vbs tau_ret $
            extendUnknownVarBinds vbs $
            withSummaryContext e $
            toExp <$> evalExp e
      extendVarBinds [(bVar f', FunClosV theta ivs (vs' `zip` taus) tau_ret eval)] $
        k $ const . return $ LetFunD f' ivs (vs' `zip` taus) tau_ret e' l
  where
    (vs, taus) = unzip vbs
    tau       = FunT ivs taus tau_ret l

    eval :: EvalM l m (Val l m Exp)
    eval =
        extendIVars (ivs `zip` repeat IotaK) $
        extendVars vbs $
        withInstantiatedTyVars tau_ret $
        withSummaryContext e $
        evalExp e

evalDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendExtFuns [(bVar f, tau)] $
    extendVarBinds [(bVar f, UnknownV)] $
    k $ const . return $ LetExtFunD f iotas vbs tau_ret l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

evalDecl (LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k $ const . return $ LetStructD s flds l

evalDecl decl@(LetCompD v tau comp s) k =
    withSummaryContext decl $
    extendVars [(bVar v, tau)] $ do
    theta <- askSubst
    withUniqBoundVar v $ \v' -> do
    comp' <- extendLet v tau $
             killHeap $
             evalComp comp >>= toComp
    extendCVarBinds [(bVar v', CompClosV theta tau eval)] $
      k $ const . return $ LetCompD v' tau comp' s
  where
    eval :: EvalM l m (Val l m (Comp l))
    eval =
        withInstantiatedTyVars tau $
        withSummaryContext comp $
        traverse uniquify comp >>= evalComp

evalDecl decl@(LetFunCompD f ivs vbs tau_ret comp l) k =
    withSummaryContext decl $
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' ->
      withUniqVars vs $ \vs' -> do
      comp' <- killHeap $
               extendLetFun f ivs vbs tau_ret $
               extendUnknownVarBinds vbs $
               evalComp comp >>= toComp
      extendCVarBinds [(bVar f', FunCompClosV theta ivs (vs' `zip` taus) tau_ret eval)] $
        k $ const . return $ LetFunCompD f' ivs (vs' `zip` taus) tau_ret comp' l
  where
    (vs, taus) = unzip vbs
    tau        = FunT ivs taus tau_ret l

    eval :: EvalM l m (Val l m (Comp l))
    eval =
        withSummaryContext comp $
        extendIVars (ivs `zip` repeat IotaK) $
        extendVars vbs $
        withInstantiatedTyVars tau_ret $
        traverse uniquify comp >>= evalComp

data LocalLetVal l m  -- | Local declaration is pure and produces a declaration
                   = DeclVal LocalDecl
                   -- | Local declaration requires a heap so it can push the heap
                   -- through the declaration.
                   | HeapDeclVal (FrozenHeap l m -> EvalM l m LocalDecl)

evalLocalDecl :: forall l m a . (IsLabel l, MonadTcRef m)
              => LocalDecl
              -> (LocalLetVal l m -> EvalM l m a)
              -> EvalM l m a
evalLocalDecl (LetLD v tau e1 s1) k =
    extendVars [(bVar v, tau)] $ do
    -- Bind v to the value of e2
    tau' <- simplType tau
    val1 <- withSummaryContext e1 $ evalExp e1
    withUniqBoundVar v $ \v' ->
      extendVarBinds [(bVar v', val1)] $
      k $ DeclVal $ LetLD v' tau' (toExp val1) s1

evalLocalDecl decl@(LetRefLD v tau maybe_e1 s1) k =
    extendVars [(bVar v, refT tau)] $ do
    tau' <- simplType tau
    val1 <- evalRhs tau' maybe_e1
    -- Allocate heap storage for v and initialize it
    withNewVarPtr $ \ptr -> do
      writeVarPtr ptr val1
      withUniqBoundVar v $ \v' ->
        extendVarBinds [(bVar v', RefV (VarR (bVar v') ptr))] $
        k $ HeapDeclVal $ \h ->
            withSummaryContext decl $ do
            val1'     <- frozenHeapLookup h ptr
            maybe_e1' <- mkRhs val1' val1
            return $ LetRefLD v' tau' maybe_e1' s1
  where
    evalRhs :: Type -> Maybe Exp -> EvalM l m (Val l m Exp)
    evalRhs tau' Nothing =
      fromMaybe UnknownV <$> runMaybeT (defaultValue tau')

    evalRhs _ (Just e1) =
      withSummaryContext e1 $ evalExp e1

    mkRhs :: Val l m Exp -> Val l m Exp -> EvalM l m (Maybe Exp)
    mkRhs new old =
        case new' of
          UnknownV                -> return Nothing
          _ | isDefaultValue new' -> return Nothing
            | otherwise           -> return $ Just (toExp new')
      where
        new' :: Val l m Exp
        new' = if isKnown new then new else old

evalComp :: forall l m . (IsLabel l, MonadTcRef m)
         => Comp l
         -> EvalM l m (Val l m (Comp l))
evalComp comp = evalSteps (unComp comp)
  where
    evalSteps :: [Step l] -> EvalM l m (Val l m (Comp l))
    evalSteps [] =
        faildoc $ text "Cannot evaluate empty sequence of steps"

    evalSteps [step] =
        evalStep step

    evalSteps (LetC l decl s : steps) =
        evalLocalDecl decl go
      where
        go :: LocalLetVal l m -> EvalM l m (Val l m (Comp l))
        go (DeclVal decl') = do
            val <- evalSteps steps
            case val of
              CompV h steps' -> partial $ CompV h $ LetC l decl' s : steps'
              _              -> return val

        go (HeapDeclVal k) = do
            val <- evalSteps steps
            case val of
              CompV h steps' -> do decl' <- k h
                                   partial $ CompV h $ LetC l decl' s : steps'
              _              -> return val

    evalSteps (step:steps) = do
        val <- evalStep step
        case val of
          CompReturnV {} -> evalBind step val steps
          CompV h steps1 -> do steps2 <- evalFullBind steps
                               return $ CompV h (steps1 ++ steps2)
          _              -> withSummaryContext step $
                            faildoc $ nest 2 $
                            text "Step did not return CompReturnV or CompV:" </>
                            ppr val

    evalBind :: Step l -> Val l m (Comp l) -> [Step l] -> EvalM l m (Val l m (Comp l))
    evalBind _step (CompReturnV val1) (BindC l wv tau s : k) =
        extendWildVars [(wv, tau)] $
        withUniqWildVar wv $ \wv' ->
        extendWildVarBinds [(wv', val1)] $ do
        val <- evalSteps k
        case val of
          CompReturnV {}  -> return val
          CompV h steps2' -> do tau'    <- simplType tau
                                steps1' <- returnC (toExp val1)
                                partial $ CompV h $ unComp steps1' ++ BindC l wv' tau' s : steps2'
          _               -> withSummaryContext k $
                             faildoc $ nest 2 $
                             text "Steps did not return CompReturnV or CompV:" </>
                             ppr val

    evalBind _step (CompReturnV _val1) k =
        evalSteps k

    evalBind _step (CompV h1 steps1') (BindC l wv tau s : k) =
        extendWildVars [(wv, tau)] $
        withUniqWildVar wv $ \wv' -> do
        killVars steps1'
        tau'    <- simplType tau
        steps2' <- extendWildVarBinds [(wv', UnknownV)] $
                   evalFullSteps k
        partial $ CompV h1 $ steps1' ++ BindC l wv' tau' s : steps2'

    evalBind _step (CompV h1 steps1') k = do
        killVars steps1'
        steps2' <- evalFullSteps k
        partial $ CompV h1 $ steps1' ++ steps2'

    evalBind step val _ =
        withSummaryContext step $
        faildoc $ nest 2 $
        text "Command did not return CmdV or ReturnV:" </>
        (text . show) val

    evalFullBind :: [Step l] -> EvalM l m [Step l]
    evalFullBind (BindC l wv tau s : steps) =
        extendWildVars [(wv, tau)] $
        withUniqWildVar wv $ \wv' -> do
        tau'   <- simplType tau
        steps' <- extendWildVarBinds [(wv', UnknownV)] $
                  evalFullSteps steps
        return $ BindC l wv' tau' s : steps'

    evalFullBind steps =
        evalFullSteps steps

evalStep :: forall l m . (IsLabel l, MonadTcRef m)
         => Step l
         -> EvalM l m (Val l m (Comp l))
evalStep (VarC _ v _) =
    lookupCVarBind v >>= go
  where
    go :: Val l m a -> EvalM l m (Val l m (Comp l))
    go (CompClosV theta _tau k) =
        withSubst theta k

    go val@CompVarV{} =
        return val

    go _ =
        faildoc $
        text "Variable" <+> ppr v <+>
        text "is not a computation, but we are trying to call it!"

evalStep step@(CallC _ f iotas args _) =
    withSummaryContext step $ do
    maybe_f' <- lookupSubst f
    v_f      <- case maybe_f' of
                  Nothing -> lookupCVarBind f
                  Just f' -> lookupCVarBind f'
    iotas'  <- mapM simplIota iotas
    v_args  <- mapM evalArg args
    go v_f iotas' v_args
  where
    go :: Val l m a -> [Iota] -> [ArgVal l m] -> EvalM l m (Val l m (Comp l))
    go (FunCompClosV theta ivs vbs _tau_ret k) iotas' v_args =
        withSubst theta $
        withUniqVars vs $ \vs' ->
        extendIVarSubst (ivs `zip` iotas') $
        extendArgBinds  (vs' `zip` v_args) $ do
        taus' <- mapM simplType taus
        k >>= wrapLetArgs vs' taus'
      where
        (vs, taus) = unzip vbs

        -- If @val@ uses any of the function's parameter bindings, we need to
        -- keep them around. This is exactly what we need to do in the @CallE@
        -- case, but here we need to add bindings to a computation rather than
        -- to an expression.
        wrapLetArgs :: [Var] -> [Type] -> Val l m (Comp l) -> EvalM l m (Val l m (Comp l))
        wrapLetArgs vs' taus' val = do
            bs <- filterM isFree (zip3 vs' taus' v_args)
            if null bs
              then return val
              else transformCompVal (letBinds bs) val
          where
            letBinds :: [(Var, Type, ArgVal l m)] -> Comp l -> EvalM l m (Comp l)
            letBinds bs comp = do
              bindsSteps <- mapM letBind bs
              return $ mkComp  $ concat bindsSteps ++ unComp comp

            letBind :: (Var, Type, ArgVal l m) -> EvalM l m [Step l]
            letBind (_v, RefT {}, _e1)      = return []
            letBind (v,  tau,     ExpAV e1) = unComp <$> letC v tau (toExp e1)
            letBind (_v, _tau,    _e1)      = return []

            isFree :: (Var, Type, ArgVal l m) -> EvalM l m Bool
            isFree (v, _, _) = do
                comp <- toComp val
                return $ v `member` (fvs comp :: Set Var)

    go _val _iotas' _v_es =
      faildoc $ text "Cannot call computation function" <+> ppr f

    evalArg :: Arg l -> EvalM l m (ArgVal l m)
    evalArg (ExpA e)  = ExpAV <$> evalExp e
    evalArg (CompA c) = do tau   <- inferComp c
                           theta <- askSubst
                           return $ CompAV $ CompClosV theta tau (evalComp c)

    extendArgBinds :: [(Var, ArgVal l m)] -> EvalM l m a -> EvalM l m a
    extendArgBinds []                   m = m
    extendArgBinds ((v, ExpAV e):args)  m = extendVarBinds [(v, e)] $
                                            extendArgBinds args m
    extendArgBinds ((v, CompAV c):args) m = extendCVarBinds [(v, c)] $
                                            extendArgBinds args m

evalStep (IfC l e1 c2 c3 s) =
    evalExp e1 >>= evalIfBody
  where
    -- Note that @e1@ is pure, so we don't have to worry about it changing the
    -- heap.
    evalIfBody :: Val l m Exp -> EvalM l m (Val l m (Comp l))
    evalIfBody val
        | isTrue  val = evalComp c2
        | isFalse val = evalComp c3
        | otherwise   = do h   <- freezeHeap
                           c2' <- savingHeap $ evalFullSteps $ unComp c2
                           c3' <- savingHeap $ evalFullSteps $ unComp c3
                           killVars c2'
                           killVars c3'
                           partial $ CompV h [IfC l (toExp val) (mkComp  c2') (mkComp  c3') s]

evalStep LetC{} =
    panicdoc $ text "evalStep: saw LetC"

evalStep (WhileC _ e c _) =
    evalWhileC e c

evalStep (ForC _ ann v tau e1 e2 c _) =
    evalForC ann v tau e1 e2 c

evalStep (LiftC l e s) = do
    val <- withSummaryContext e $ evalExp e
    case val of
      ReturnV val' -> return $ CompReturnV val'
      CmdV h e'    -> partial $ CompV h [LiftC l e' s]
      _            -> withSummaryContext e $
                      faildoc $ nest 2 $
                      text "Command did not return CmdV or Return:" </>
                      (text . show) val

evalStep (ReturnC l e s) = do
    val <- evalExp e
    case val of
      ExpV e' -> partialComp $ mkComp  [ReturnC l e' s]
      _       -> return $ CompReturnV val

evalStep BindC{} =
    panicdoc $ text "evalStep: saw BindC"

evalStep (TakeC l tau s) = do
    tau' <- simplType tau
    partialComp $ mkComp  [TakeC l tau' s]

evalStep (TakesC l n tau s) = do
    tau' <- simplType tau
    partialComp $ mkComp  [TakesC l n tau' s]

evalStep (EmitC l e s) = do
    val <- evalExp e
    partialComp $ mkComp  [EmitC l (toExp val) s]

evalStep (EmitsC l e s) = do
    val <- evalExp e
    partialComp $ mkComp  [EmitsC l (toExp val) s]

evalStep (RepeatC l ann c s) = do
    h <- freezeHeap
    killVars c
    val    <- savingHeap $
              withSummaryContext c $
              evalComp c
    steps' <- toSteps val
    partial $ CompV h [RepeatC l ann (mkComp  steps') s]

evalStep (ParC ann tau c1 c2 s) = do
    h      <- freezeHeap
    val1   <- withSummaryContext c1 $ evalComp c1
    val2   <- withSummaryContext c2 $ evalComp c2
    steps1 <- toSteps val1
    steps2 <- toSteps val2
    partial $ CompV h [ParC ann tau (mkComp  steps1) (mkComp  steps2) s]

evalStep LoopC{} =
    panicdoc $ text "evalStep: saw LoopC"

-- | Fully evaluate a sequence of steps in the current heap, returning a
-- sequence of steps representing all changes to the heap.
evalFullSteps :: (IsLabel l, MonadTcRef m)
              => [Step l]
              -> EvalM l m [Step l]
evalFullSteps steps = do
    h            <- freezeHeap
    val          <- evalComp (mkComp steps)
    (h', steps') <- case val of
                      CompReturnV {}  -> do h'     <- freezeHeap
                                            steps' <- toSteps val
                                            return (h', steps')
                      CompV h' steps' -> return (h', steps')
                      _               -> withSummaryContext steps $
                                         faildoc $ nest 2 $
                                         text "Computation did not return CompReturnV or CompV:" </>
                                         ppr val
    unComp <$> diffHeapComp h h' (mkComp steps')

evalFullComp :: (IsLabel l, MonadTcRef m)
             => Comp l
             -> EvalM l m (Comp l)
evalFullComp comp = mkComp <$> evalFullSteps (unComp comp)

evalConst :: forall l m . (IsLabel l, MonadTcRef m)
          => Const
          -> EvalM l m (Val l m Exp)
evalConst c@(ArrayC cs) = do
    (_, tau)   <- inferConst noLoc c >>= checkArrT
    vals       <- mapM evalConst cs
    maybe_dflt <- runMaybeT $ defaultValue tau
    case maybe_dflt of
      Nothing   -> partialExp $ arrayE (map toExp vals)
      Just dflt -> return $ ArrayV $ P.fromList dflt vals

evalConst (StructC s flds) = do
    vals <- mapM evalConst cs
    return $ StructV s (Map.fromList (fs `zip` vals))
  where
    fs :: [Field]
    cs :: [Const]
    (fs, cs) = unzip  flds

evalConst c =
    return $ ConstV c

evalExp :: forall l m . (IsLabel l, MonadTcRef m)
        => Exp
        -> EvalM l m (Val l m Exp)
evalExp e =
    withSummaryContext e $ do
    flags <- askFlags
    eval flags e
  where
    eval :: Flags -> Exp -> EvalM l m (Val l m Exp)
    eval flags (ConstE c _) | peval flags =
        evalConst c

    eval _flags e@ConstE{} =
        partialExp e

    eval flags (VarE v _) | peval flags = do
        v' <- fromMaybe v <$> lookupSubst v
        -- If @v@ is a pureish computation, we need to look it up in the
        -- computation environment and convert it to an 'Exp Val'. This fixes
        -- #13.
        isVarNotComp <- isInScope v'
        if isVarNotComp
          then lookupVarBind v'
          else lookupCVarBind v' >>= compValToExpVal

    eval _flags (VarE v s) = do
        v' <- fromMaybe v <$> lookupSubst v
        -- If @v@ is a pureish computation, we need to return a 'CmdV' instead
        -- of a 'ExpV'. This is part of the fix to #13.
        tau <- lookupVar v
        if isCompT tau
          then partialCmd $ VarE v' s
          else partialExp $ VarE v' s

    eval flags (UnopE op e s) | peval flags = do
        val <- eval flags e
        unop op val
      where
        unop :: Unop -> Val l m Exp -> EvalM l m (Val l m Exp)
        unop Lnot val =
            maybePartialVal $ liftBool op not val

        unop Bnot val =
            maybePartialVal $ liftBits op complement val

        unop Neg val =
            maybePartialVal $ liftNum op negate val

        unop (Cast (StructT sn' _)) (StructV sn flds) | isComplexStruct sn && isComplexStruct sn' = do
            flds' <- castStruct cast sn' (Map.toList flds)
            return $ StructV sn' (Map.fromList flds')
          where
            cast :: Type -> Val l m Exp -> EvalM l m (Val l m Exp)
            cast tau = unop (Cast tau)

        unop (Cast tau) val =
            maybePartialVal $ liftCast tau val

        unop Len val = do
            (iota, _) <- inferExp e >>= checkArrOrRefArrT
            psi       <- askIVarSubst
            case subst psi mempty iota of
              ConstI n _ -> evalConst $ intC n
              _ -> partialExp $ UnopE op (toExp val) s

        unop op val =
            partialExp $ UnopE op (toExp val) s

    eval flags (UnopE op e s) = do
        val <- eval flags e
        partialExp $ UnopE op (toExp val) s

    eval flags (BinopE op e1 e2 s) | peval flags = do
        val1 <- eval flags e1
        val2 <- eval flags e2
        binop op val1 val2
      where
        binop :: Binop -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m Exp)
        binop Lt val1 val2 =
            maybePartialVal $ liftOrd op (<) val1 val2

        binop Le val1 val2 =
            maybePartialVal $ liftOrd op (<=) val1 val2

        binop Eq val1 val2 =
            maybePartialVal $ liftEq op (==) val1 val2

        binop Ge val1 val2 =
            maybePartialVal $ liftOrd op (>=) val1 val2

        binop Gt val1 val2 =
            maybePartialVal $ liftOrd op (>) val1 val2

        binop Ne val1 val2 =
            maybePartialVal $ liftEq op (/=) val1 val2

        binop Land val1 val2
            | isTrue  val1 = maybePartialVal val2
            | isFalse val1 = maybePartialVal val1
            | otherwise    = maybePartialVal $ liftBool2 op (&&) val1 val2

        binop Lor val1 val2
            | isTrue  val1 = maybePartialVal val1
            | isFalse val1 = maybePartialVal val2
            | otherwise    = maybePartialVal $ liftBool2 op (||) val1 val2

        binop Band val1 val2 =
            maybePartialVal $ liftBits2 op (.&.) val1 val2

        binop Bor val1 val2 =
            maybePartialVal $ liftBits2 op (.|.) val1 val2

        binop Bxor val1 val2 =
            maybePartialVal $ liftBits2 op xor val1 val2

        binop LshL val1 val2 =
            maybePartialVal $ liftShift op shiftL val1 val2

        binop AshR val1 val2 =
            maybePartialVal $ liftShift op shiftR val1 val2

        binop Add val1 val2 =
            maybePartialVal $ liftNum2 op (+) val1 val2

        binop Sub val1 val2 =
            maybePartialVal $ liftNum2 op (-) val1 val2

        binop Mul val1 val2 =
            maybePartialVal $ liftNum2 op (*) val1 val2

        binop Div val1 val2 =
            maybePartialVal $ liftIntegral2 op quot val1 val2

        binop Rem val1 val2 =
            maybePartialVal $ liftIntegral2 op rem val1 val2

        binop op val1 val2 =
            partialExp $ BinopE op (toExp val1) (toExp val2) s

    eval flags (BinopE op e1 e2 s) = do
        val1 <- eval flags e1
        val2 <- eval flags e2
        partialExp $ BinopE op (toExp val1) (toExp val2) s

    eval flags e@(IfE e1 e2 e3 s) = do
        tau  <- inferExp e
        val1 <- eval flags e1
        evalIfExp tau val1
      where
        -- Note that @e1@ is pure, so we don't have to worry about it changing the
        -- heap.
        evalIfExp :: Type -> Val l m Exp -> EvalM l m (Val l m Exp)
        evalIfExp tau val
            | isTrue  val = eval flags e2
            | isFalse val = eval flags e3
            | isPureT tau = do val2 <- eval flags e2
                               val3 <- eval flags e3
                               partial $ ExpV $ IfE (toExp val) (toExp val2) (toExp val3) s
            | otherwise   = do h   <- freezeHeap
                               e2' <- savingHeap $ evalFullCmd e2
                               e3' <- savingHeap $ evalFullCmd e3
                               killVars e2'
                               killVars e3'
                               partial $ CmdV h $ IfE (toExp val) e2' e3' s

    eval _flags (LetE decl e2 s2) =
        evalLocalDecl decl go
      where
        go :: LocalLetVal l m -> EvalM l m (Val l m Exp)
        go (DeclVal decl) = do
            val2 <- evalExp e2
            case val2 of
              ExpV e2'   -> partial $ ExpV   $ LetE decl e2' s2
              CmdV h e2' -> partial $ CmdV h $ LetE decl e2' s2
              _          -> wrapLet decl val2

        go (HeapDeclVal k) = do
            val2 <- evalExp e2
            case val2 of
              ExpV e2'   -> do decl <- freezeHeap >>= k
                               partial $ ExpV   $ LetE decl e2' s2
              CmdV h e2' -> do decl <- k h
                               partial $ CmdV h $ LetE decl e2' s2
              _          -> do decl <- freezeHeap >>= k
                               wrapLet decl val2

        wrapLet :: LocalDecl -> Val l m Exp -> EvalM l m (Val l m Exp)
        wrapLet decl val2
            | v `Set.member` fvs e2 = partialExp $ LetE decl e2 s2
            | otherwise             = return val2
          where
            e2 :: Exp
            e2 = toExp val2

            v :: Var
            [v] = Set.toList (binders decl)

    eval flags e@(CallE f iotas es s) | peval flags = do
        maybe_f' <- lookupSubst f
        v_f      <- case maybe_f' of
                      Nothing -> lookupVarBind f
                      Just f' -> lookupVarBind f'
        iotas'  <- mapM simplIota iotas
        v_es    <- mapM (eval flags) es
        tau     <- inferExp e
        go tau v_f iotas' v_es
      where
        go :: Type -> Val l m Exp -> [Iota] -> [Val l m Exp] -> EvalM l m (Val l m Exp)
        go _tau (FunClosV theta ivs vbs _tau_ret k) iotas' v_es =
            withSubst theta $
            withUniqVars vs $ \vs' ->
            extendIVarSubst (ivs `zip` iotas') $
            extendVarBinds  (vs' `zip` v_es) $ do
            taus' <- mapM simplType taus
            k >>= wrapLetArgs vs' taus'
          where
            vs :: [Var]
            taus :: [Type]
            (vs, taus) = unzip vbs

            -- If @val@ uses any of the function's parameter bindings, we need to
            -- keep them around. This can happen if we decide not to inline a
            -- variable, e.g., if the variable is bound to an array constant.
            wrapLetArgs :: [Var] -> [Type] -> Val l m Exp -> EvalM l m (Val l m Exp)
            wrapLetArgs vs' taus' val =
                -- We must be careful here not to apply transformExpVal if the list
                -- of free variables is null because @transformExpVal id@ is not the
                -- identify function!
                case filter isFree (zip3 vs' taus' v_es) of
                  [] -> return val
                  bs -> transformExpVal (letBinds bs) val
              where
                letBinds :: [(Var, Type, Val l m Exp)] -> Exp -> Exp
                letBinds bs e = foldr letBind e bs

                letBind :: (Var, Type, Val l m Exp) -> Exp -> Exp
                letBind (_v, RefT {}, _e1) e2 = e2
                letBind (v,  tau,      e1) e2 = letE v tau (toExp e1) e2

                isFree :: (Var, Type, Val l m Exp) -> Bool
                isFree (v, _, _) = v `member` (fvs (toExp val) :: Set Var)

        -- Note that the heap cannot change as the result of evaluating function
        -- arguments, so we can call 'partialCmd' here instead of saving the heap
        -- above and constructing a 'CmdV' from it manually.
        go tau (ExpV (VarE f' _)) iotas' v_es
           | isPureT tau = do killVars e
                              partialExp $ CallE f' iotas' (map toExp v_es) s
           | otherwise   = do killVars e
                              partialCmd $ CallE f' iotas' (map toExp v_es) s

        go _tau val _iotas' _v_es =
          faildoc $ text "Cannot call function" <+> ppr val

    eval flags e@(CallE f iotas es s) = do
        tau  <- inferExp e
        v_es <- mapM (eval flags) es
        if isPureT tau
          then partialExp $ CallE f iotas (map toExp v_es) s
          else partialCmd $ CallE f iotas (map toExp v_es) s

    eval flags (DerefE e s) =
        eval flags e >>= go
      where
        go :: Val l m Exp -> EvalM l m (Val l m Exp)
        go (RefV r) = do
            val <- readVarPtr (refVarPtr r)
            if isKnown val
              then ReturnV <$> refView r val
              else partialCmd $ DerefE (toExp r) s

        go val =
            partialCmd $ DerefE (toExp val) s

    eval flags e@(AssignE e1 e2 s) = do
        val1 <- eval flags e1
        val2 <- eval flags e2
        go val1 val2
      where
        go :: Val l m Exp -> Val l m Exp -> EvalM l m (Val l m Exp)
        go (RefV r) val2 = do
            h         <- freezeHeap
            old       <- readVarPtr ptr
            maybe_new <- runMaybeT $ refUpdate r old val2
            case maybe_new of
              Just new | isValue new ->
                  do writeVarPtr ptr new
                     return $ ReturnV unitV
              _ ->
                  do killVars e
                     partial $ CmdV h $ AssignE (toExp r) (toExp val2) s
          where
            ptr :: VarPtr
            ptr = refVarPtr r

        go val1 val2 =
            partialCmd $ AssignE (toExp val1) (toExp val2) s

    eval _flags (WhileE e1 e2 _) =
        evalWhileE e1 e2

    eval _flags (ForE ann v tau e1 e2 e3 _) =
        evalForE ann v tau e1 e2 e3

    eval flags e@(ArrayE es _) = do
        (_, tau)   <- inferExp e >>= checkArrT
        vals       <- mapM (eval flags) es
        maybe_dflt <- runMaybeT $ defaultValue tau
        case maybe_dflt of
          Nothing   -> partialExp $ arrayE (map toExp vals)
          Just dflt -> return $ ArrayV $ P.fromList dflt vals

    eval flags (IdxE arr start len s) = do
        v_arr   <- eval flags arr
        v_start <- eval flags start
        if peval flags
          then evalIdx v_arr v_start len
          else partialExp $ IdxE (toExp v_arr) (toExp v_start) len s

    eval flags (StructE s flds _) = do
        vals <- mapM (eval flags) es
        return $ StructV s (Map.fromList (fs `zip` vals))
      where
        fs :: [Field]
        es :: [Exp]
        (fs, es) = unzip  flds

    eval flags (ProjE e f s) = do
        val <- eval flags e
        if peval flags
          then evalProj val f
          else partialExp $ ProjE (toExp val) f s

    eval flags (PrintE nl es s) = do
        vals <- mapM (eval flags) es
        partialCmd $ PrintE nl (map toExp vals) s

    eval _flags e@ErrorE{} =
        partialCmd e

    eval flags (ReturnE _ e _) = do
        val <- eval flags e
        case val of
          ExpV e -> partialCmd $ returnE e
          _      -> return $ ReturnV val

    eval flags (BindE wv tau e1 e2 s) = do
        val1 <- withSummaryContext e1 $ eval flags e1
        extendWildVars [(wv, tau)] $
          withUniqWildVar wv $ \wv' -> do
          tau' <- simplType tau
          case val1 of
            CmdV h1 e1'   -> do killVars e1'
                                e2'  <- extendWildVarBinds [(wv', UnknownV)] $
                                        evalFullCmd e2
                                partial $ CmdV h1 $ BindE wv' tau' e1' e2' s
            ReturnV val1' -> extendWildVarBinds [(wv', val1')] $
                             withSummaryContext e2 $
                             eval flags e2 >>= wrapBind wv' tau' val1'
            _             -> withSummaryContext e1 $
                             faildoc $ nest 2 $
                             text "Command did not return CmdV or ReturnV:" </>
                             (text . show) val1
      where
        -- If @val2@ uses the binding, we need to keep it around. This can
        -- happen if we decide not to inline a variable, e.g., if the variable
        -- is bound to an array constant.
        wrapBind :: WildVar
                 -> Type
                 -> Val l m Exp
                 -> Val l m Exp
                 -> EvalM l m (Val l m Exp)
        wrapBind (TameV bv) tau val1 val2 | v `Set.member` fvs e2 =
            partialCmd $ letE v tau e1 e2
          where
            v :: Var
            v = bVar bv

            e1, e2 :: Exp
            e1 = toExp val1
            e2 = toExp val2

        wrapBind _ _ _ val2 =
            return val2

    eval flags (LutE e) | testDynFlag LUT flags = do
        h <- freezeHeap
        CmdV h <$> lutExp e

    eval flags (LutE e) =
        eval flags e

lutExp :: forall l s m . (s ~ RealWorld, IsLabel l, MonadTcRef m)
       => Exp
       -> EvalM l m Exp
lutExp e = do
    info     <- lutInfo e
    v_refs   <- varRefs $ toList $
                Set.map unLUTVar (lutInVars info) <>
                Set.map unLUTVar (lutOutVars info)
    in_refs  <- mapM (lutVarRef v_refs) $ toList $ lutInVars info
    out_refs <- mapM (lutVarRef v_refs) $ toList $ lutOutVars info
    ret_ref  <- traverse (lutVarRef v_refs . VarL) (lutReturnedVar info)
    tau_ret  <- inferExp e
    traceLUT $ nest 2 $ text "LUT:" <+> ppr tau_ret </> ppr e </> ppr info
    e'       <- go [(v, ref, tau) | (v, (ref, tau)) <- Map.assocs v_refs]
                   in_refs out_refs ret_ref tau_ret
    traceLUT $ nest 2 $ text "LUTted expression:" </> ppr e'
    -- Kill the variables we modified
    killVars e'
    return e'
  where
    unSTC :: Type -> Type
    unSTC (ST _ (C tau) _ _ _ _) = tau
    unSTC tau                    = tau

    varRefs :: [Var] -> EvalM l m (Map Var (I.Ref s, Type))
    varRefs vs =
        Map.fromList <$> mapM varRef vs
      where
        varRef :: Var -> EvalM l m (Var, (I.Ref s, Type))
        varRef v = do
            tau <- lookupVar v
            ref <- I.defaultRef tau
            return (v, (ref, tau))

    lutVarRef :: Map Var (I.Ref s, Type)
              -> LUTVar
              -> EvalM l m (LUTVar, I.Ref s, Type)
    lutVarRef v_refs lv@(VarL v) = do
        (ref, tau) <- maybe err return (Map.lookup v v_refs)
        return (lv, ref, tau)
      where
        err = faildoc $ text "Cannot find in/out variable:" <+> ppr v

    lutVarRef v_refs lv@(IdxL v i len) = do
        (ref, tau)    <- maybe err return (Map.lookup v v_refs)
        (_, tau_elem) <- checkArrOrRefArrT tau
        ref'          <- I.idxR ref i len
        return (lv, ref', arrKnownT n tau_elem)
      where
        n :: Int
        n = fromMaybe 1 len

        err = faildoc $ text "Cannot find in/out variable:" <+> ppr v

    go :: [(Var, I.Ref s, Type)]
       -> [(LUTVar, I.Ref s, Type)]
       -> [(LUTVar, I.Ref s, Type)]
       -> Maybe (LUTVar, I.Ref s, Type)
       -> Type
       -> EvalM l m Exp
    go v_refs in_refs out_refs ret_ref tau_ret = do
        fs    <- (++) <$> mapM (gensym . namedString) lvs_out
                      <*> if nonUnitResult
                          then (:[]) <$> gensym "ret"
                          else return []
        sname <- gensym "lut"
        appendTopDecl $ LetStructD sname (fs `zip` taus_result) noLoc
        (v_lut, tau_entry, e1) <- genLUT sname fs
        e2                     <- genLookup sname fs v_lut
        return $ letE v_lut tau_entry e1 e2
      where
        lvs_in :: [LUTVar]
        refs_in :: [I.Ref s]
        taus_in :: [Type]
        (lvs_in, refs_in, taus_in) = unzip3 in_refs

        lvs_out :: [LUTVar]
        refs_out :: [I.Ref s]
        taus_out :: [Type]
        (lvs_out, refs_out, taus_out) = unzip3 out_refs

        tau_ret' :: Type
        tau_ret' = unSTC tau_ret

        v_ret :: Maybe Var
        v_ret = case ret_ref of
                  Just (VarL v, _, _) -> Just v
                  _                   -> Nothing

        -- 'True' if the value returned by the LUTted expression is also
        -- among the output variables.
        resultInOutVars :: Bool
        resultInOutVars = case ret_ref of
                            Nothing         -> False
                            Just (lv, _, _) -> lv `elem` lvs_out

        -- 'True' if the LUTted expression has a non-unit value that /is not/
        -- one of the output variables.
        nonUnitResult :: Bool
        nonUnitResult = not resultInOutVars && not (isUnitT tau_ret')

        -- If @e@ returns one of the output variables, we don't need to add
        -- it to the LUT entry because it will already be included.
        taus_result :: [Type]
        taus_result = map unRefT taus_out ++ [tau_ret' | nonUnitResult]

        -- Generate the LUT
        genLUT :: Struct
               -> [Field]
               -> EvalM l m (Var, Type, Exp)
        genLUT sname fs = do
            v_lut         <- gensymAt "lut" e
            let tau_entry =  StructT sname noLoc
            traceLUT $ text "Returned variable:" <+> ppr v_ret
            traceLUT $ text "LUT entry type:" <+> ppr tau_entry
            mval <- evalI $ I.extendRefs [(v, ref) | (v, ref, _) <- v_refs] $
                            I.compileExp e
            if null taus_in
              then do entry <- genLUTEntry mval []
                      return (v_lut, tau_entry, constE entry)
              else do entries   <- I.enumValsList taus_in >>=
                                   mapM (genLUTEntry mval)
                      let n     =  length entries
                      let e_lut =  constE $ arrayC entries
                      return (v_lut, arrKnownT n tau_entry, e_lut)
          where
            -- Generate one LUT entry
            genLUTEntry :: IO I.Val -> [I.Val] -> EvalM l m Const
            genLUTEntry mval vals_in = do
                zipWithM_ I.assign refs_in vals_in
                c_ret  <- I.toConst <$> liftIO mval
                cs_vs  <- mapM (I.fromRef >=> return . I.toConst) refs_out
                let cs =  cs_vs ++ [c_ret | nonUnitResult]
                return $ StructC sname (fs `zip` cs)

        -- Generate the LUT lookup
        genLookup :: Struct
                  -> [Field]
                  -> Var
                  -> EvalM l m Exp
        genLookup _sname fs v_lut =
            lookupInVars in_refs $ \etaus -> do
            -- Construct a binder for the LUT index (if it is needed)
            w_in        <- sum <$> mapM typeSize taus_in
            v_idx       <- gensym "lutidx"
            let tau_idx =  FixT I U (W w_in) (BP 0) noLoc
            let args :: [(Val l m Exp, Type)]
                args = [(ExpV e, tau) | (e, tau) <- etaus]
            idx <- packValues args
            let letIdx :: Exp -> Exp
                letIdx | null lvs_in = id
                       | otherwise   = letE v_idx tau_idx
                                            (bitcastE tau_idx (toExp idx))
            -- Construct the values of the LUT entry
            let entry :: Exp
                entry | null lvs_in = varE v_lut
                      | otherwise   = idxE (varE v_lut) (varE v_idx)
            let results :: [Exp]
                results = [projE entry f | f <- fs]
            -- Return the LUT lookup expression
            letIdx <$> if isCompT tau_ret
                       then compLut results
                       else pureLut results
          where
            compLut :: [Exp] -> EvalM l m Exp
            compLut results = do
                es <- zipWithM mkAssign lvs_out results
                return $ foldr seqE (mkResult v_ret) es
              where
                mkResult :: Maybe Var -> Exp
                mkResult (Just v) | resultInOutVars =
                    derefE $ varE v

                mkResult _ | isUnitT tau_ret' =
                    returnE unitE

                mkResult _ =
                    returnE $ last results

                mkAssign :: LUTVar -> Exp -> EvalM l m Exp
                mkAssign v e = do
                    v' <- toExp <$> evalExp (toExp v)
                    return $ assignE v' e

            pureLut :: [Exp] -> EvalM l m Exp
            pureLut _results | isUnitT tau_ret' =
                return $ returnE unitE

            pureLut results =
                return $ last results

            -- Get the values of all the input variables, dereferencing them if
            -- needed.
            lookupInVars :: [(LUTVar, I.Ref s, Type)]
                         -> ([(Exp, Type)] -> EvalM l m Exp)
                         -> EvalM l m Exp
            lookupInVars [] k =
                k []

            lookupInVars ((lv,_,tau):lvtaus) k | isRefT tau = do
                v'       <- gensymAt (namedString lv) (locOf lv)
                let tau' =  unRefT tau
                lookupInVars lvtaus $ \lvtaus' -> do
                e1 <- toExp <$> evalExp (derefE (toExp lv))
                e2 <- k ((varE v', tau'):lvtaus')
                return $ bindE v' tau' e1 e2

            lookupInVars ((lv,_,tau):vtaus) k =
                lookupInVars vtaus $ \vtaus' -> do
                e <- toExp <$> evalExp (toExp lv)
                k ((e, tau):vtaus')

-- | Fully evaluate an expression, which must be an effectful command, in the
-- current heap, and return a single expression representing all changes to the
-- heap. We use this when we need to sequence two commands and the first command
-- produced a residual, meaning we can't push the prefix heap of the second
-- command past the first command.
evalFullCmd :: (IsLabel l, MonadTcRef m)
            => Exp
            -> EvalM l m Exp
evalFullCmd e =
    withSummaryContext e $ do
    h        <- freezeHeap
    val      <- evalExp e
    (h', e') <- case val of
                  ReturnV {} -> do h' <- freezeHeap
                                   return (h', toExp val)
                  CmdV h' e' -> return (h', e')
                  _          -> faildoc $ nest 2 $
                                text "Command did not return CmdV or ReturnV:" </>
                                (text . show) val
    diffHeapExp h h' e'

refVarPtr :: Ref l m -> VarPtr
refVarPtr (VarR _ ptr) = ptr
refVarPtr (IdxR r _ _) = refVarPtr r
refVarPtr (ProjR r _)  = refVarPtr r

refView :: (IsLabel l, MonadTc m)
        => Ref l m
        -> Val l m Exp
        -> EvalM l m (Val l m Exp)
refView VarR {}        val = return val
refView (IdxR r i len) val = do val' <- refView r val
                                evalIdx val' i len
refView (ProjR r f)    val = do val' <- refView r val
                                evalProj val' f

-- | Update a reference to an object given the old value of the entire object
-- and the new value of the pointed-to part.
refUpdate :: forall l m t . (IsLabel l, MonadTc m, MonadTrans t, MonadTc (t (EvalM l m)))
          => Ref l m
          -> Val l m Exp
          -> Val l m Exp
          -> t (EvalM l m) (Val l m Exp)
refUpdate VarR{} _ new =
    return new

refUpdate (IdxR r i len) old new = do
    old' <- lift $ refView r old
    go i len old' new
  where
    --go :: Val l m Exp -> Maybe Int -> Val l m Exp -> Val l m Exp -> t m (Val l m Exp)
    go (ConstV (FixC I _ _ (BP 0) n)) Nothing (ArrayV vs) new = do
        new' <- ArrayV <$> vs P.// [(start, new)]
        refUpdate r old new'
      where
        start :: Int
        start = fromIntegral (numerator n)

    go (ConstV (FixC I _ _ (BP 0) n)) (Just len) (ArrayV vs) (ArrayV vs') = do
        new' <- ArrayV <$> vs P.// ([start..start+len-1] `zip` P.toList vs')
        refUpdate r old new'
      where
        start :: Int
        start = fromIntegral (numerator n)

    go _ _ _ _ =
        fail "Cannot take slice of non-ArrayV"

refUpdate (ProjR r f) old new = do
    old' <- lift $ refView r old
    go f old' new
  where
    --go :: Field -> Val l m Exp -> Val l m Exp -> t m (Val l m Exp)
    go f (StructV s flds) new = do
        let new' = StructV s (Map.insert f new flds)
        refUpdate r old new'

    go _ _ _ =
        fail "Cannot project non-StructV"

-- | Attempt to execute a loop. If the loop cannot be fully evaluated, we
-- perform the following steps:
--
-- 1. Restore the initial heap.
--
-- 2. Kill all variables that the loop could have been modified by the loop,
-- i.e., the free variables of @body@.
--
-- 3. Return a command consisting of the initial heap and the
-- partially-evaluated loop.
evalLoop :: (IsLabel l, ModifiedVars e Var, MonadTcRef m)
         => e
         -> EvalM l m (Val l m a)
         -> EvalM l m (Val l m a)
evalLoop body m = do
    h   <- freezeHeap
    val <- m
    case val of
      ReturnV {}     -> return val
      CompReturnV {} -> return val
      CmdV _ e'      -> do thawHeap h
                           killVars body
                           partial $ CmdV h e'
      CompV _ c'     -> do thawHeap h
                           killVars body
                           partial $ CompV h c'
      _              -> faildoc $ text "Bad loop:" <+> ppr val

evalWhileE :: forall l m . (IsLabel l, MonadTcRef m)
           => Exp
           -> Exp
           -> EvalM l m (Val l m Exp)
evalWhileE e1 e2 =
    evalLoop e2 $
    evalExp e1 >>= loop
  where
    loop :: Val l m Exp -> EvalM l m (Val l m Exp)
    loop (ReturnV val) | isTrue val = do
        val2 <- evalExp e2
        case val2 of
          ReturnV {} -> evalExp e1 >>= loop
          CmdV {}    -> residualWhile
          _          -> faildoc $ text "Bad body evaluation in while:" <+> ppr val2

    loop (ReturnV val) | isFalse val =
        return $ ReturnV unitV

    loop CmdV{} =
        residualWhile

    loop val =
        faildoc $ text "Bad condition evaluation in while:" <+> ppr val

    residualWhile :: EvalM l m (Val l m Exp)
    residualWhile =
        savingHeap $ do
        killVars e1
        killVars e2
        e1' <- evalFullCmd e1
        e2' <- evalFullCmd e2
        partialCmd $ whileE e1' e2'

evalWhileC :: forall l m . (IsLabel l, MonadTcRef m)
           => Exp
           -> Comp l
           -> EvalM l m (Val l m (Comp l))
evalWhileC e1 c2 =
    evalLoop c2 $
    evalExp e1 >>= loop
  where
    loop :: Val l m Exp -> EvalM l m (Val l m (Comp l))
    loop (ReturnV val) | isTrue val = do
        val2 <- evalComp c2
        case val2 of
          CompReturnV {} -> evalExp e1 >>= loop
          CompV {}       -> residualWhile
          _              -> faildoc $ text "Bad body evaluation in while:" <+> ppr val2

    loop (ReturnV val) | isFalse val =
        return $ CompReturnV unitV

    loop CmdV{} =
        residualWhile

    loop val =
        faildoc $ text "Bad condition evaluation in while:" <+> ppr val

    residualWhile :: EvalM l m (Val l m (Comp l))
    residualWhile =
        savingHeap $ do
        killVars e1
        killVars c2
        e1' <- evalFullCmd e1
        c2' <- evalFullComp c2
        whileC e1' c2' >>= partialComp

-- | Convert an integral value to a 'Val Exp' of the given (fixpoint) type.
toFixVal :: Integral i => Type -> i -> Val l m Exp
toFixVal ~(FixT sc s w bp _) i =
    ConstV $ FixC sc s w bp (fromIntegral i)

evalForE :: forall l m . (IsLabel l, MonadTcRef m)
         => UnrollAnn
         -> Var
         -> Type
         -> Exp
         -> Exp
         -> Exp
         -> EvalM l m (Val l m Exp)
evalForE ann v tau e1 e2 e3 = do
    start <- evalExp e1
    len   <- evalExp e2
    withUniqVar v $ \v' ->
        evalLoop e3 $
        extendVars [(v, tau)] $
        go v' start len
  where
    go :: Var -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m Exp)
    go v' start len | Just r_start <- fromIntV start,
                      Just r_len   <- fromIntV len =
        loop r_start (r_start + r_len)
      where
        loop :: Integer -> Integer -> EvalM l m (Val l m Exp)
        loop !i !end | i < end = do
            val3 <- extendVarBinds [(v', toFixVal tau i)] $ evalExp e3
            case val3 of
              ReturnV {} -> loop (i+1) end
              CmdV {}    -> residualFor v' (toExp start) (toExp len)
              _          -> faildoc $ text "Bad body evaluation in for:" <+> ppr val3

        loop _ _ =
            return $ ReturnV unitV

    go v' start len =
        residualFor v' (toExp start) (toExp len)

    residualFor :: Var -> Exp -> Exp -> EvalM l m (Val l m Exp)
    residualFor v' e1' e2' =
        savingHeap $
        extendVarBinds [(v', UnknownV)] $ do
        killVars e3
        e3' <- evalFullCmd e3
        partialCmd $ forE ann v' tau e1' e2' e3'

evalForC :: forall l m . (IsLabel l, MonadTcRef m)
         => UnrollAnn
         -> Var
         -> Type
         -> Exp
         -> Exp
         -> Comp l
         -> EvalM l m (Val l m (Comp l))
evalForC ann v tau e1 e2 c3 = do
    start <- evalExp e1
    len   <- evalExp e2
    withUniqVar v $ \v' ->
        evalLoop c3 $
        extendVars [(v, tau)] $
        go v' start len
  where
    go :: Var -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m (Comp l))
    go v' start len | Just r_start <- fromIntV start,
                      Just r_len   <- fromIntV len =
        loop r_start (r_start + r_len)
      where
        loop :: Integer -> Integer -> EvalM l m (Val l m (Comp l))
        loop !i !end | i < end = do
            val3 <- extendVarBinds [(v', toFixVal tau i)] $ evalComp c3
            case val3 of
              CompReturnV {} -> loop (i+1) end
              CompV {}       -> residualFor v' (toExp start) (toExp len)
              _              -> faildoc $ text "Bad body evaluation in for:" <+> ppr val3

        loop _ _ =
            return $ CompReturnV unitV

    go v' start len =
        residualFor v' (toExp start) (toExp len)

    residualFor :: Var -> Exp -> Exp -> EvalM l m (Val l m (Comp l))
    residualFor v' e1' e2' =
        savingHeap $
        extendVarBinds [(v', UnknownV)] $ do
        killVars c3
        c3' <- evalFullComp c3
        forC ann v' tau e1' e2' c3' >>= partialComp

evalIdx :: (IsLabel l, MonadTc m)
        => Val l m Exp
        -> Val l m Exp
        -> Maybe Int
        -> EvalM l m (Val l m Exp)
evalIdx (RefV r) start len =
    return $ RefV $ IdxR r start len

evalIdx (ArrayV vs) start Nothing | Just r <- fromIntV start =
    let start :: Int
        start = fromIntegral r
    in
        vs P.!? start

evalIdx (ArrayV vs) start (Just len) | Just r <- fromIntV start =
    let start :: Int
        start = fromIntegral r
    in
        ArrayV <$> P.slice start len vs

evalIdx (SliceV arr start _len) i Nothing =
    return $ IdxV arr (start + i)

evalIdx (SliceV arr start0 _len0) start (Just len) =
    return $ SliceV arr (start0 + start) len

evalIdx v_arr v_start Nothing =
    return $ IdxV v_arr v_start

evalIdx v_arr v_start (Just len) =
    return $ SliceV v_arr v_start len

evalProj :: (IsLabel l, MonadTc m)
         => Val l m Exp
         -> Field
         -> EvalM l m (Val l m Exp)
evalProj (RefV r) f =
    return $ RefV $ ProjR r f

evalProj (StructV _ kvs) f =
    case Map.lookup f kvs of
      Nothing  -> faildoc $ text "Unknown struct field" <+> ppr f
      Just val -> return val

evalProj val f =
    partialExp $ ProjE (toExp val) f noLoc

-- | @'transformExpVal' f val'@ transforms a value of type @'Val' Exp@ by
-- applying f. Note that 'transformExpVal' will convert some sub-term of its
-- @Val l m Exp@ to an 'ExpV' if it isn't already, so even if @f@ is the identity
-- function, 'transformExpVal' /is not/ the identity function.
transformExpVal :: forall l m . (IsLabel l, MonadTc m)
                => (Exp -> Exp)
                -> Val l m Exp
                -> EvalM l m (Val l m Exp)
transformExpVal f = go
  where
    go :: Val l m Exp -> EvalM l m (Val l m Exp)
    go (ReturnV val) = ReturnV <$> go val
    go (ExpV e)      = partial $ ExpV   $ f e
    go (CmdV h e)    = partial $ CmdV h $ f e
    go v             = partial $ ExpV   $ f (toExp v)

-- | @'transformCompVal' f val'@ transforms a value of type @'Val' Comp@ by
-- applying f. Note that 'transformCompVal' will convert some sub-term of its
-- @Val Comp@ to a 'CompV' if it isn't already, so even if @f@ is the identity
-- function, 'transformCompVal' /is not/ the identity function.
transformCompVal :: (IsLabel l, MonadTcRef m)
                 => (Comp l -> EvalM l m (Comp l))
                 -> Val l m (Comp l)
                 -> EvalM l m (Val l m (Comp l))
transformCompVal f val =
    toComp val >>= f >>= partialComp

-- | Like 'compToExp', 'compValToExpVal' attempts to convert a 'Val Comp'
-- representing a pureish computation to a 'Val l m Exp' representing the same
-- computation.
compValToExpVal :: (IsLabel l, MonadTc m)
                => Val l m (Comp l)
                -> EvalM l m (Val l m Exp)
compValToExpVal (CompReturnV e) =
    return $ ReturnV e

compValToExpVal (CompV h steps) =
    CmdV h <$> compToExp (mkComp steps)

compValToExpVal (CompVarV v) =
    return $ ReturnV $ ExpV $ varE v

compValToExpVal (CompClosV theta _tau m) =
    withSubst theta m >>= compValToExpVal

compValToExpVal (FunCompClosV theta ivs vtaus tau m) =
    return $ FunClosV theta ivs vtaus tau $ m >>= compValToExpVal
