{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Optimize.Eval
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Eval (
    evalProgram,
    toExp
  ) where

import Control.Monad (filterM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Bits
import Data.List (partition)
import Data.Loc
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Comp
import KZC.Core.Enum
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Label
import KZC.Optimize.Eval.Monad
import qualified KZC.Optimize.Eval.PArray as P
import KZC.Optimize.Eval.Val
import KZC.Util.Error
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Uniq
import KZC.Vars

-- | Return 'True' if we should partially-evaluate.
peval :: Config -> Bool
peval = testDynFlag PartialEval

evalProgram :: (IsLabel l, MonadTcRef m)
            => Program l
            -> m (Program l)
evalProgram (Program imports decls maybe_main) =
    evalEvalM $
    evalDecls decls $ \mkDecls -> do
    (h', main') <- case maybe_main of
                     Just main -> do (h', main') <- evalMain main
                                     return (h', Just main')
                     Nothing   -> (,) <$> freezeHeap <*> pure Nothing
    (sdecls1, decls1) <- partition isStructD <$> mkDecls h'
    (sdecls2, decls2) <- partition isStructD <$> getTopDecls
    return $ Program imports (sdecls1 ++ sdecls2 ++ decls1 ++ decls2) main'

evalMain :: (IsLabel l, MonadTcRef m)
         => Main l
         -> EvalM l m (FrozenHeap l m, Main l)
evalMain (Main comp tau) =
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
    return (h', Main comp' tau)

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
evalDecl decl@(StructD s taus flds l) k =
    extendStructs [StructDef s taus flds l] $
    k $ const . return $ decl

evalDecl (LetD decl s) k =
    evalLocalDecl decl go
  where
    go :: LocalLetVal l m -> EvalM l m a
    go (DeclVal decl') =
        k $ \_h -> return $ LetD decl' s

    go (HeapDeclVal mkDecl) =
        k $ \h -> LetD <$> mkDecl h <*> pure s

evalDecl decl@(LetFunD f tvks vbs tau_ret e l) k =
    withSummaryContext decl $
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' ->
      withUniqVars vs $ \vs' -> do
      e' <- killHeap $
            extendLetFun f' tvks vbs tau_ret $
            extendUnknownVarBinds vbs $
            withSummaryContext e $
            toExp <$> evalExp e
      extendVarBinds [(bVar f', FunClosV theta tvks (vs' `zip` taus) tau_ret eval)] $
        k $ const . return $ LetFunD f' tvks (vs' `zip` taus) tau_ret e' l
  where
    (vs, taus) = unzip vbs
    tau        = funT tvks taus tau_ret l

    eval :: EvalM l m (Val l m Exp)
    eval =
        extendVars vbs $
        withInstantiatedTyVars tau_ret $
        withSummaryContext e $
        evalExp e

evalDecl (LetExtFunD f tvks vbs tau_ret l) k =
    extendExtFuns [(bVar f, tau)] $
    extendVarBinds [(bVar f, UnknownV)] $
    k $ const . return $ LetExtFunD f tvks vbs tau_ret l
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

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

evalDecl decl@(LetFunCompD f tvks vbs tau_ret comp l) k =
    withSummaryContext decl $
    extendVars [(bVar f, tau)] $ do
    theta <- askSubst
    withUniqBoundVar f $ \f' ->
      withUniqVars vs $ \vs' -> do
      comp' <- killHeap $
               extendLetFun f tvks vbs tau_ret $
               extendUnknownVarBinds vbs $
               evalComp comp >>= toComp
      extendCVarBinds [(bVar f', FunCompClosV theta tvks (vs' `zip` taus) tau_ret eval)] $
        k $ const . return $ LetFunCompD f' tvks (vs' `zip` taus) tau_ret comp' l
  where
    (vs, taus) = unzip vbs
    tau        = funT tvks taus tau_ret l

    eval :: EvalM l m (Val l m (Comp l))
    eval =
        withSummaryContext comp $
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
    mkRhs new old
      | isUnknown new' || isDefaultValue new' = return Nothing
      | otherwise                             = return $ Just (toExp new')
      where
        new' :: Val l m Exp
        new' = if isKnown new then new else old

evalLocalDecl LetViewLD{} _k =
    faildoc $ text "Views not supported"

evalComp :: forall l m . (IsLabel l, MonadTcRef m)
         => Comp l
         -> EvalM l m (Val l m (Comp l))
evalComp comp = evalSteps (unComp comp)
  where
    evalSteps :: [Step l] -> EvalM l m (Val l m (Comp l))
    evalSteps [] =
        return $ CompReturnV unitV

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

evalStep step@(CallC _ f taus args _) =
    withSummaryContext step $ do
    maybe_f' <- lookupSubst f
    v_f      <- case maybe_f' of
                  Nothing -> lookupCVarBind f
                  Just f' -> lookupCVarBind f'
    taus'   <- mapM simplType taus
    v_args  <- mapM evalArg args
    go v_f taus' v_args
  where
    go :: Val l m a -> [Type] -> [ArgVal l m] -> EvalM l m (Val l m (Comp l))
    go (FunCompClosV theta tvks vbs tau_ret k) taus' v_args =
        withSubst theta $
        withUniqVars vs $ \vs' ->
        extendTyVars tvks $
        extendTyVarTypes (map fst tvks `zip` taus') $
        extendSTTyVars tau_ret $
        withInstantiatedTyVars tau_ret $
        extendArgBinds (vs' `zip` v_args) $ do
        taus' <- mapM simplType taus
        k >>= wrapLetArgs vs' taus'
      where
        (vs, taus) = unzip vbs

        extendSTTyVars (ForallT tvks ST{} _) k = extendTyVars tvks k
        extendSTTyVars _                     k = k

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

    go _val _taus' _v_es =
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

evalStep (ForC _ ann v tau gint c _) =
    evalForC ann v tau gint c

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

evalStep (ParC ann b c1 c2 l) = do
    h         <- freezeHeap
    (s, a, c) <- askSTIndices
    val1      <- withSummaryContext c1 $
                 localSTIndices (Just (s, a, b)) $
                 evalComp c1
    val2      <- withSummaryContext c2 $
                 localSTIndices (Just (b, b, c)) $
                 evalComp c2
    steps1    <- toSteps val1
    steps2    <- toSteps val2
    partial $ CompV h [ParC ann b (mkComp  steps1) (mkComp  steps2) l]

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
    vals       <- V.mapM evalConst cs
    maybe_dflt <- runMaybeT $ defaultValue tau
    case maybe_dflt of
      Nothing   -> partialExp $ arrayE (map toExp (V.toList vals))
      Just dflt -> return $ ArrayV $ P.fromVector dflt vals

evalConst (ReplicateC n c) = do
    val <- evalConst c
    return $ ArrayV $ P.replicateDefault n val

evalConst (EnumC tau) =
    evalConst =<< ArrayC <$> enumType tau

evalConst (StructC s taus flds) = do
    vals <- mapM evalConst cs
    return $ StructV s taus (Map.fromList (fs `zip` vals))
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
    flags <- askConfig
    eval flags e
  where
    eval :: Config -> Exp -> EvalM l m (Val l m Exp)
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
          then do val <- lookupVarBind v'
                  case val of
                    ExpV VarE{} -> return val
                    ExpV{}      -> partialExp $ varE v'
                    _           -> return val
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
        op' <- evalUnop op
        val <- eval flags e
        unop op' val
      where
        unop :: Unop -> Val l m Exp -> EvalM l m (Val l m Exp)
        unop Lnot  val = maybePartialVal $ liftBool op not val
        unop Bnot  val = maybePartialVal $ liftBits op complement val
        unop Neg   val = maybePartialVal $ liftNum op negate val
        unop Abs   val = maybePartialVal $ liftNum op abs val
        unop Exp   val = maybePartialVal $ liftFloating op exp val
        unop Exp2  val = maybePartialVal $ liftFloating op (\x -> exp (log 2 * x)) val
        unop Expm1 val = maybePartialVal $ liftFloating op (\x -> exp x - 1) val
        unop Log   val = maybePartialVal $ liftFloating op log val
        unop Log2  val = maybePartialVal $ liftFloating op (\x -> log x / log 2) val
        unop Log1p val = maybePartialVal $ liftFloating op (\x -> log (x + 1)) val
        unop Sqrt  val = maybePartialVal $ liftFloating op sqrt val
        unop Sin   val = maybePartialVal $ liftFloating op sin val
        unop Cos   val = maybePartialVal $ liftFloating op cos val
        unop Tan   val = maybePartialVal $ liftFloating op tan val
        unop Asin  val = maybePartialVal $ liftFloating op asin val
        unop Acos  val = maybePartialVal $ liftFloating op acos val
        unop Atan  val = maybePartialVal $ liftFloating op atan val
        unop Sinh  val = maybePartialVal $ liftFloating op sinh val
        unop Cosh  val = maybePartialVal $ liftFloating op cosh val
        unop Tanh  val = maybePartialVal $ liftFloating op tanh val
        unop Asinh val = maybePartialVal $ liftFloating op asinh val
        unop Acosh val = maybePartialVal $ liftFloating op acosh val
        unop Atanh val = maybePartialVal $ liftFloating op atanh val

        unop (Cast (StructT s [_tau] _)) (StructV s' [tau'] flds) | isComplexStruct s && isComplexStruct s' = do
            flds' <- castStruct cast s' (Map.toList flds)
            return $ StructV s' [tau'] (Map.fromList flds')
          where
            cast :: Type -> Val l m Exp -> EvalM l m (Val l m Exp)
            cast tau = unop (Cast tau)

        unop (Cast tau) val =
            maybePartialVal $ liftCast tau val

        unop Len val = do
            (n, _) <- inferExp e >>= checkArrOrRefArrT
            phi    <- askTyVarTypeSubst
            case subst phi mempty n of
              NatT n _ -> evalConst $ idxC n
              _ -> partialExp $ UnopE op (toExp val) s

        unop op val =
            partialExp $ UnopE op (toExp val) s

        evalUnop :: Unop -> EvalM l m Unop
        evalUnop (Cast tau)    = do phi <- askTyVarTypeSubst
                                    return $ Cast (subst phi mempty tau)
        evalUnop (Bitcast tau) = do phi <- askTyVarTypeSubst
                                    return $ Bitcast (subst phi mempty tau)
        evalUnop op            = pure op

    eval flags (UnopE op e s) = do
        val <- eval flags e
        partialExp $ UnopE op (toExp val) s

    eval flags (BinopE op e1 e2 s) | peval flags = do
        val1 <- eval flags e1
        val2 <- eval flags e2
        binop op val1 val2
      where
        binop :: Binop -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m Exp)
        binop Eq val1 val2 =
            maybePartialVal $ liftEq op (==) val1 val2

        binop Ne val1 val2 =
            maybePartialVal $ liftEq op (/=) val1 val2

        binop Lt val1 val2 =
            maybePartialVal $ liftOrd op (<) val1 val2

        binop Le val1 val2 =
            maybePartialVal $ liftOrd op (<=) val1 val2

        binop Ge val1 val2 =
            maybePartialVal $ liftOrd op (>=) val1 val2

        binop Gt val1 val2 =
            maybePartialVal $ liftOrd op (>) val1 val2

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

        binop Pow (ConstV (IntC ip x)) (ConstV (IntC _ y)) =
            return $ ConstV (IntC ip (x ^ y))

        binop Pow (ConstV (FloatC fp x)) (ConstV (IntC _ y)) =
            return $ ConstV (FloatC fp (x ^ y))

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

    eval flags e@(CallE f taus es s) | peval flags = do
        maybe_f' <- lookupSubst f
        v_f      <- case maybe_f' of
                      Nothing -> lookupVarBind f
                      Just f' -> lookupVarBind f'
        taus'   <- mapM simplType taus
        v_es    <- mapM (eval flags) es
        tau     <- inferExp e
        go tau v_f taus' v_es
      where
        go :: Type -> Val l m Exp -> [Type] -> [Val l m Exp] -> EvalM l m (Val l m Exp)
        go _tau (FunClosV theta tvks vbs _tau_ret k) taus' v_es =
            withSubst theta $
            withUniqVars vs $ \vs' ->
            extendTyVars tvks $
            extendTyVarTypes (map fst tvks `zip` taus') $
            extendVarBinds   (vs' `zip` v_es) $ do
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
        go tau (ExpV (VarE f' _)) taus' v_es
           | isPureT tau = do killVars e
                              partialExp $ CallE f' taus' (map toExp v_es) s
           | otherwise   = do killVars e
                              partialCmd $ CallE f' taus' (map toExp v_es) s

        go _tau val _taus' _v_es =
          faildoc $ text "Cannot call function" <+> ppr val

    eval flags e@(CallE f taus es s) = do
        tau  <- inferExp e
        v_es <- mapM (eval flags) es
        if isPureT tau
          then partialExp $ CallE f taus (map toExp v_es) s
          else partialCmd $ CallE f taus (map toExp v_es) s

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

    eval _flags (ForE ann v tau gint e _) =
        evalForE ann v tau gint e

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

    eval flags (StructE s taus flds _) = do
        vals <- mapM (eval flags) es
        return $ StructV s taus (Map.fromList (fs `zip` vals))
      where
        fs :: [Field]
        es :: [Exp]
        (fs, es) = unzip flds

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

    eval flags (LutE sz e) = do
        val <- eval flags e
        partialCmd $ LutE sz (toExp val)

    eval _ GenE{} =
        faildoc $ text "Generator expressions not supported."

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
    go val Nothing (ArrayV vs) new | Just x <- fromIntV val = do
        let start :: Int
            start = fromIntegral x
        new' <- ArrayV <$> vs P.// [(start, new)]
        refUpdate r old new'

    go val (Just len) (ArrayV vs) (ArrayV vs') | Just x <- fromIntV val = do
        let start :: Int
            start = fromIntegral x
        new' <- ArrayV <$> vs P.// ([start..start+len-1] `zip` P.toList vs')
        refUpdate r old new'

    go _ _ _ _ =
        fail "Cannot take slice of non-ArrayV"

refUpdate (ProjR r f) old new = do
    old' <- lift $ refView r old
    go f old' new
  where
    --go :: Field -> Val l m Exp -> Val l m Exp -> t m (Val l m Exp)
    go f (StructV s tau flds) new = do
        let new' = StructV s tau (Map.insert f new flds)
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

-- | Convert an integral value to a 'Val Exp' of the given (integral) type.
toIntVal :: Integral i => Type -> i -> Val l m Exp
toIntVal ~(IntT ip _) i =
    ConstV $ IntC ip (fromIntegral i)

evalForE :: forall l m . (IsLabel l, MonadTcRef m)
         => UnrollAnn
         -> Var
         -> Type
         -> GenInterval Exp
         -> Exp
         -> EvalM l m (Val l m Exp)
evalForE ann v tau gint e3 = do
    start <- evalExp e1
    len   <- evalExp e2
    withUniqVar v $ \v' ->
        evalLoop e3 $
        extendVars [(v, tau)] $
        go v' start len
  where
    (e1, e2) = toStartLenGenInt gint

    go :: Var -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m Exp)
    go v' start len | Just i_start <- fromIntV start,
                      Just i_len   <- fromIntV len =
        loop i_start (i_start + i_len)
      where
        loop :: Int -> Int -> EvalM l m (Val l m Exp)
        loop !i !end | i < end = do
            val3 <- extendVarBinds [(v', toIntVal tau i)] $ evalExp e3
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
         -> GenInterval Exp
         -> Comp l
         -> EvalM l m (Val l m (Comp l))
evalForC ann v tau gint c3 = do
    start <- evalExp e1
    len   <- evalExp e2
    withUniqVar v $ \v' ->
        evalLoop c3 $
        extendVars [(v, tau)] $
        go v' start len
  where
    (e1, e2) = toStartLenGenInt gint

    go :: Var -> Val l m Exp -> Val l m Exp -> EvalM l m (Val l m (Comp l))
    go v' start len | Just i_start <- fromIntV start,
                      Just i_len   <- fromIntV len =
        loop i_start (i_start + i_len)
      where
        loop :: Int -> Int -> EvalM l m (Val l m (Comp l))
        loop !i !end | i < end = do
            val3 <- extendVarBinds [(v', toIntVal tau i)] $ evalComp c3
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

evalProj (StructV _ _ kvs) f =
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

toComp :: (IsLabel l, MonadTc m) => Val l m (Comp l) -> EvalM l m (Comp l)
toComp x = mkComp <$> toSteps x

toSteps :: (IsLabel l, MonadTc m) => Val l m (Comp l) -> EvalM l m [Step l]
toSteps (CompReturnV val) =
    unComp <$> returnC (toExp val)

toSteps (CompV _ steps) =
    return steps

toSteps (CompVarV v) =
    unComp <$> varC v

toSteps val =
    faildoc $ text "toSteps: Cannot convert value to steps:" <+> ppr val
