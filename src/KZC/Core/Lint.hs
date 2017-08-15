{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Lint
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Core.Lint (
    module KZC.Expr.Lint.Monad,

    Tc(..),
    runTc,
    liftTc,

    extendWildVars,

    inferKind,
    checkKind,

    checkProgram,

    checkConst,
    inferConst,

    inferExp,
    checkExp,

    checkGenerators,

    refPath,

    inferComp,
    checkComp,

    compToExp,

    inferStep,

    checkTypeEquality,

    joinOmega,

    checkComplexT,
    checkKnownNatT,
    checkArrT,
    checkKnownArrT,
    checkArrOrRefArrT,
    checkStructT,
    checkStructOrRefStructT,
    checkStructFieldT,
    checkRefT,
    checkFunT,

    withInstantiatedTyVars,
    genST,
    instST,
    checkST,
    checkSTC,
    checkSTCUnit,
    checkPure,
    checkPureish,
    checkPureishST,
    checkPureishSTC,
    checkPureishSTCUnit
  ) where

import Control.Monad (unless,
                      void,
                      when,
                      zipWithM,
                      zipWithM_)
import Data.Foldable (traverse_)
import Data.Loc
import qualified Data.Map as Map
import Text.PrettyPrint.Mainland

import KZC.Check.Path
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Expr.Lint (Tc(..),
                      runTc,
                      liftTc,

                      checkConst,
                      inferConst,

                      checkStructDecl,
                      checkStructUse,

                      inferKind,
                      checkKind,
                      checkTauOrRhoKind,
                      checkTyApp,

                      checkCast,
                      checkBitcast,

                      checkTypeEquality,

                      joinOmega,

                      checkComplexT,
                      checkKnownNatT,
                      checkArrT,
                      checkKnownArrT,
                      checkArrOrRefArrT,
                      checkStructT,
                      checkStructOrRefStructT,
                      checkStructFieldT,
                      checkRefT,
                      checkFunT,

                      withInstantiatedTyVars,
                      genST,
                      instST,
                      checkST,
                      checkSTC,
                      checkSTCUnit,
                      checkPure,
                      checkPureish,
                      checkPureishST,
                      checkPureishSTC,
                      checkPureishSTCUnit)
import KZC.Expr.Lint.Monad
import KZC.Label
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Vars

extendWildVars :: MonadTc m => [(WildVar, Type)] -> m a -> m a
extendWildVars wvs = extendVars [(bVar v, tau) | (TameV v, tau) <- wvs]

checkProgram :: (IsLabel l, MonadTc m)
             => Program l
             -> m ()
checkProgram (Program _ decls main) =
    checkDecls decls $
    traverse_ checkMain main

checkMain :: (IsLabel l, MonadTc m)
          => Main l
          -> m ()
checkMain (Main comp tau) =
    withLocContext comp (text "In definition of main") $
    inSTScope tau $
    inLocalScope $
    checkComp comp tau

checkDecls :: forall l m a . (IsLabel l, MonadTc m)
           => [Decl l] -> m a -> m a
checkDecls decls k = foldr checkDecl k decls

checkDecl :: forall l m a . (IsLabel l, MonadTc m)
          => Decl l
          -> m a
          -> m a
checkDecl decl@(StructD s tvks flds l) k = do
    alwaysWithSummaryContext decl $
        checkStructDecl s tvks flds
    extendStructs [StructDef s tvks flds l] k

checkDecl (LetD decl _) k =
    checkLocalDecl decl k

checkDecl decl@(LetFunD f ns vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    alwaysWithSummaryContext decl $ do
        checkKind tau PhiK
        tau_ret' <- extendLetFun f ns vbs tau_ret $
                    withFvContext e $
                    inferExp e >>= genST
        checkTypeEquality tau_ret' tau_ret
        unless (isPureishT tau_ret) $
          faildoc $ text "Function" <+> ppr f <+> text "is not pureish but is in a letfun!"
    k
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

checkDecl decl@(LetExtFunD f ns vbs tau_ret l) k = do
    alwaysWithSummaryContext decl $ checkKind tau PhiK
    extendExtFuns [(bVar f, tau)] k
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

checkDecl decl@(LetCompD v tau comp _) k = do
    alwaysWithSummaryContext decl $ do
        checkKind tau MuK
        tau' <- extendLet v tau $
                withSummaryContext comp $
                inferComp comp >>= genST
        checkTypeEquality tau' tau
    extendVars [(bVar v, tau)] k

checkDecl decl@(LetFunCompD f ns vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    alwaysWithSummaryContext decl $ do
        checkKind tau PhiK
        tau_ret' <- extendLetFun f ns vbs tau_ret $
                    withFvContext comp $
                    inferComp comp >>= genST
        checkTypeEquality tau_ret' tau_ret
        when (isPureishT tau_ret) $
          faildoc $ text "Function" <+> ppr f <+> text "is pureish but is in a letfuncomp!"
    k
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

inferView :: forall m . MonadTc m => View -> m Type
inferView (IdxVW v e len l) = do
    tau_v <- lookupVar v
    withFvContext e $ checkExp e idxT
    go tau_v
  where
    go :: Type -> m Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (sliceT tau len) l

    go (ArrT _ tau _) =
        return $ sliceT tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

checkView :: MonadTc m => View -> Type -> m ()
checkView vw tau = do
    tau' <- inferView vw
    checkTypeEquality tau' tau

checkLocalDecl :: MonadTc m => LocalDecl -> m a -> m a
checkLocalDecl decl@(LetLD v tau e _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau tauK
        withSummaryContext e $ checkExp e tau
    extendVars [(bVar v, tau)] k

checkLocalDecl decl@(LetRefLD v tau maybe_e _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau tauK
        case maybe_e of
          Nothing -> return ()
          Just e  -> withSummaryContext e $ checkExp e tau
    extendVars [(bVar v, refT tau)] k

checkLocalDecl decl@(LetTypeLD alpha kappa tau _) k = do
    alwaysWithSummaryContext decl $ checkKind tau kappa
    extendTyVars [(alpha, kappa)] $
      extendTyVarTypes [(alpha, tau)] k

checkLocalDecl decl@(LetViewLD v tau vw _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkTauOrRhoKind tau
        checkView vw tau
    extendVars [(bVar v, tau)] k

inferExp :: forall m . MonadTc m => Exp -> m Type
inferExp (ConstE c l) =
    inferConst l c

inferExp (VarE v _) =
    lookupVar v

inferExp (UnopE op e1 l) = do
    tau1 <- inferExp e1
    unop op tau1
  where
    unop :: Unop -> Type -> m Type
    unop Lnot tau = inferOp [(a, boolK)] aT aT tau
    unop Bnot tau = inferOp [(a, bitsK)] aT aT tau

    unop Neg tau =
        mkSigned <$> inferOp [(a, numK)] aT aT tau
      where
        mkSigned :: Type -> Type
        mkSigned (IntT (U w) l) = IntT (I w) l
        mkSigned tau            = tau

    unop Abs   tau = inferOp [(a, numK)] aT aT tau
    unop Exp   tau = inferOp [(a, fracK)] aT aT tau
    unop Exp2  tau = inferOp [(a, fracK)] aT aT tau
    unop Expm1 tau = inferOp [(a, fracK)] aT aT tau
    unop Log   tau = inferOp [(a, fracK)] aT aT tau
    unop Log2  tau = inferOp [(a, fracK)] aT aT tau
    unop Log1p tau = inferOp [(a, fracK)] aT aT tau
    unop Sqrt  tau = inferOp [(a, fracK)] aT aT tau
    unop Sin   tau = inferOp [(a, fracK)] aT aT tau
    unop Cos   tau = inferOp [(a, fracK)] aT aT tau
    unop Tan   tau = inferOp [(a, fracK)] aT aT tau
    unop Asin  tau = inferOp [(a, fracK)] aT aT tau
    unop Acos  tau = inferOp [(a, fracK)] aT aT tau
    unop Atan  tau = inferOp [(a, fracK)] aT aT tau
    unop Sinh  tau = inferOp [(a, fracK)] aT aT tau
    unop Cosh  tau = inferOp [(a, fracK)] aT aT tau
    unop Tanh  tau = inferOp [(a, fracK)] aT aT tau
    unop Asinh tau = inferOp [(a, fracK)] aT aT tau
    unop Acosh tau = inferOp [(a, fracK)] aT aT tau
    unop Atanh tau = inferOp [(a, fracK)] aT aT tau

    unop Len tau = do
        _ <- checkArrOrRefArrT tau
        return idxT

    a :: TyVar
    a = "a"

    aT :: Type
    aT = tyVarT a

    inferOp :: [Tvk]
            -> Type
            -> Type
            -> Type
            -> m Type
    inferOp tvks a b tau1 =
        inferPureCall tau_op [tau1] [e1]
      where
        tau_op :: Type
        tau_op = ForallT tvks (FunT [a] b l) l

inferExp (BinopE op e1 e2 l) = do
    tau1 <- inferExp e1
    tau2 <- inferExp e2
    binop op tau1 tau2
  where
    binop :: Binop -> Type -> Type -> m Type
    binop Eq   tau1 _tau2 = inferOp [(a, eqK)] aT aT boolT tau1
    binop Ne   tau1 _tau2 = inferOp [(a, eqK)] aT aT boolT tau1
    binop Lt   tau1 _tau2 = inferOp [(a, ordK)] aT aT boolT tau1
    binop Le   tau1 _tau2 = inferOp [(a, ordK)] aT aT boolT tau1
    binop Ge   tau1 _tau2 = inferOp [(a, ordK)] aT aT boolT tau1
    binop Gt   tau1 _tau2 = inferOp [(a, ordK)] aT aT boolT tau1
    binop Land tau1 _tau2 = inferOp [(a, boolK)] aT aT aT tau1
    binop Lor  tau1 _tau2 = inferOp [(a, boolK)] aT aT aT tau1
    binop Band tau1 _tau2 = inferOp [(a, bitsK)] aT aT aT tau1
    binop Bor  tau1 _tau2 = inferOp [(a, bitsK)] aT aT aT tau1
    binop Bxor tau1 _tau2 = inferOp [(a, bitsK)] aT aT aT tau1
    binop LshL tau1 _tau2 = inferOp [(a, bitsK)] aT uintT aT tau1
    binop LshR tau1 _tau2 = inferOp [(a, bitsK)] aT uintT aT tau1
    binop AshR tau1 _tau2 = inferOp [(a, bitsK)] aT uintT aT tau1
    binop Add  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1
    binop Sub  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1
    binop Mul  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1
    binop Div  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1
    binop Rem  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1
    binop Pow  tau1 _tau2 = inferOp [(a, numK)] aT aT aT tau1

    binop Cat tau1 tau2 = do
        (nat1, tau1_elem) <- checkArrT tau1
        (nat2, tau2_elem) <- checkArrT tau2
        checkTypeEquality tau2_elem tau1_elem
        return $ ArrT (nat1 + nat2) tau1_elem (tau1 `srcspan` tau2)

    a :: TyVar
    a = "a"

    aT :: Type
    aT = tyVarT a

    inferOp :: [Tvk]
            -> Type
            -> Type
            -> Type
            -> Type
            -> m Type
    inferOp tvks a b c tau1 =
        inferPureCall tau_op [tau1] [e1, e2]
      where
        tau_op :: Type
        tau_op = ForallT tvks (FunT [a, b] c l) l

inferExp (IfE e1 e2 e3 _) = do
    checkExp e1 boolT
    tau <- withFvContext e2 $ inferExp e2
    withFvContext e3 $ checkExp e3 tau
    return tau

inferExp (LetE decl body _) =
    withSummaryContext decl $
    checkLocalDecl decl $ do
    tau <- inferExp body
    inferKind tau >>= checkLetKind
    return tau
  where
    checkLetKind :: Kind -> m ()
    checkLetKind TauK{} = return ()
    checkLetKind MuK    = return ()

    checkLetKind kappa =
      faildoc $ text "Body of let has kind" <+> ppr kappa

inferExp (CallE f ies es _) = do
    tau_f           <- lookupVar f
    (taus, tau_ret) <- inferCall tau_f ies es
    zipWithM_ checkArg es taus
    unless (isPureishT tau_ret) $
        checkNoAliasing (es `zip` taus)
    return tau_ret
  where
    checkArg :: Exp -> Type -> m ()
    checkArg e tau =
        withFvContext e $ do
        tau' <- inferExp e
        checkTypeEquality tau tau'
        checkPure tau

inferExp (DerefE e l) = do
    tau     <- withFvContext e $ inferExp e >>= checkRefT
    [s,a,b] <- freshenVars ["s", "a", "b"] (fvs tau)
    return $ forallST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l

inferExp e@(AssignE e1 e2 l) = do
    tau  <- withFvContext e1 $ inferExp e1 >>= checkRefT
    tau' <- withFvContext e2 $ inferExp e2
    withFvContext e $ checkTypeEquality tau' tau
    [s,a,b] <- freshenVars ["s", "a", "b"] mempty
    return $ forallST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l

inferExp e@(LowerE tau _) = do
    withSummaryContext e $ checkKind tau NatK
    return intT

inferExp (WhileE e1 e2 _) = do
    withFvContext e1 $ do
        (_, tau, _, _, _) <- inferExp e1 >>= checkPureishSTC
        checkTypeEquality tau boolT
    withFvContext e2 $ do
        tau <- inferExp e2
        void $ checkPureishSTCUnit tau
        return tau

inferExp (ForE _ v tau gint e _) = do
    checkKind tau intK
    traverse_ (\e -> withFvContext e $ checkExp e tau) gint
    extendVars [(v, tau)] $
        withFvContext e $ do
        tau_body <- inferExp e
        void $ checkPureishSTCUnit tau_body
        return tau_body

inferExp (ArrayE es l) = do
    taus <- mapM inferExp es
    case taus of
      [] -> faildoc $ text "Empty array expression"
      tau:taus -> do mapM_ (checkTypeEquality tau) taus
                     return $ ArrT (fromIntegral (length es)) tau l

inferExp (IdxE e1 e2 len l) = do
    tau <- withFvContext e1 $ inferExp e1
    withFvContext e2 $ checkExp e2 idxT
    checkLen len
    go tau
  where
    checkLen :: Maybe Type -> m ()
    checkLen Nothing =
        return ()

    checkLen (Just len) = do
        n <- checkKnownNatT len
        unless (n >= 0) $
          faildoc $ text "Negative slice length:" <+> ppr n

    go :: Type -> m Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (sliceT tau len) l

    go (ArrT _ tau _) =
        return $ sliceT tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

inferExp (ProjE e f l) = do
    tau <- withFvContext e $ inferExp e
    go tau
  where
    go :: Type -> m Type
    go (RefT tau _) = do
        (s, taus) <- checkStructT tau
        sdef      <- lookupStruct s
        tau_f     <- checkStructFieldT sdef taus f
        return $ RefT tau_f l

    go tau = do
        (s, taus) <- checkStructT tau
        sdef      <- lookupStruct s
        checkStructFieldT sdef taus f

inferExp (CastE tau2 e _) = do
    tau1 <- inferExp e
    checkCast tau1 tau2
    return tau2

inferExp (BitcastE tau2 e _) = do
    tau1 <- inferExp e
    checkBitcast tau1 tau2
    return tau2

inferExp e0@(StructE s taus flds l) =
    withFvContext e0 $ do
    fdefs <- checkStructUse s taus (map fst flds)
    mapM_ (checkField fdefs) flds
    return $ StructT s taus l
  where
    checkField :: [(Field, Type)] -> (Field, Exp) -> m ()
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc "checkField: missing field!"
               Just tau -> return tau
      checkExp e tau

inferExp (PrintE _ es l) = do
    mapM_ inferExp es
    [s,a,b] <- freshenVars ["s", "a", "b"] mempty
    return $ forallST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l

inferExp (ErrorE nu _ l) = do
    [s,a,b] <- freshenVars ["s", "a", "b"] mempty
    return $ forallST [s,a,b] (C nu) (tyVarT s) (tyVarT a) (tyVarT b) l

inferExp (ReturnE _ e l) = do
    tau     <- inferExp e
    [s,a,b] <- freshenVars ["s", "a", "b"] (fvs tau)
    return $ forallST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l

inferExp (BindE wv tau e1 e2 _) = do
    (alphas, tau', s,  a,  b) <- withFvContext e1 $
                                 inferExp e1 >>= checkPureishSTC
    checkTypeEquality tau' tau
    withFvContext e2 $
        extendWildVars [(wv, tau)] $ do
        tau_e2              <- inferExp e2
        (_, omega, _, _, _) <- checkPureishST tau_e2
        checkTypeEquality tau_e2 (forallST alphas omega s a b noLoc)
        return tau_e2

inferExp (LutE _ e) =
    inferExp e

inferExp (GenE e gs _) =
    checkGenerators gs $ \n -> do
    tau <- inferExp e
    case tau of
      ForallT _ (ST (C tau') _ _ _ _) _ ->
          do checkPureish tau
             return $ arrKnownT n tau'
      _ ->
          return $ arrKnownT n tau

checkGenerators :: forall a m . MonadTc m => [Gen] -> (Int -> m a) -> m a
checkGenerators gs k =
    -- Generators may not have any free variables.
    withNoVars $ go 1 gs
  where
    withNoVars :: m a -> m a
    withNoVars = localTc $ \env -> env { varTypes = mempty }

    go :: Int -> [Gen] -> m a
    go !n [] = k n

    go !n (GenG v tau c l:gs) = do
        (m, tau') <- inferConst l c >>= checkKnownArrT
        checkTypeEquality tau tau'
        extendVars [(v, tau)] $
          go (n*m) gs

    go !n (GenRefG v tau c l:gs) = do
        (m, tau') <- inferConst l c >>= checkKnownArrT
        checkTypeEquality tau tau'
        extendVars [(v, refT tau)] $
          go (n*m) gs

inferCall :: forall m e . MonadTc m
          => Type -> [Type] -> [e] -> m ([Type], Type)
inferCall tau_f taus args = do
    (tvks, taus_args, tau_ret) <- checkFunT tau_f
    checkTyApp tvks taus
    checkNumArgs (length args) (length taus_args)
    extendTyVars tvks $ do
      let theta = Map.fromList (map fst tvks `zip` taus)
      let phi   = fvs taus_args <> fvs tau_ret
      return (subst theta phi taus_args, subst theta phi tau_ret)
  where
    checkNumArgs :: Int -> Int -> m ()
    checkNumArgs n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "arguments but got" <+> ppr n

inferPureCall :: forall m . MonadTc m
              => Type -> [Type] -> [Exp] -> m Type
inferPureCall tau_f taus es = do
    (taus, tau_ret) <- inferCall tau_f taus es
    zipWithM_ checkArg es taus
    unless (isPureishT tau_ret) $
        checkNoAliasing (es `zip` taus)
    return tau_ret
  where
    checkArg :: Exp -> Type -> m ()
    checkArg e tau =
        withFvContext e $ do
        tau' <- inferExp e
        checkTypeEquality tau tau'
        checkPure tau

checkExp :: MonadTc m => Exp -> Type -> m ()
checkExp e tau = do
    tau' <- inferExp e
    checkTypeEquality tau' tau

checkNoAliasing :: forall m . MonadTc m => [(Exp, Type)] -> m ()
checkNoAliasing etaus = do
    rpaths <- concat <$> mapM root etaus
    checkNoPathAliasing rpaths
  where
    root :: (Exp, Type) -> m [RefPath Var Field]
    root (e, tau) | isRefT tau = do
        path <- refPath e
        return [path]

    root _ =
        return []

refPath :: forall m . Monad m => Exp -> m (RefPath Var Field)
refPath e =
    go e []
  where
    go :: Exp -> [Path Field] -> m (RefPath Var Field)
    go (VarE v _) path =
        return $ RefP v (reverse path)

    go (IdxE e (ConstE (IntC _ i) _) Nothing _) path =
        go e (IdxP i 1 : path)

    go (IdxE e (ConstE (IntC _ i) _) (Just (NatT len _)) _) path =
        go e (IdxP i len : path)

    go (IdxE e _ _ _) _ =
        go e []

    go (ProjE e f _) path =
        go e (ProjP f : path)

    go e _ =
        faildoc $ text "refPath: Not a reference:" <+> ppr e

inferComp :: forall l m . (IsLabel l, MonadTc m) => Comp l -> m Type
inferComp comp =
    withSummaryContext comp $
    inferSteps (unComp comp)
  where
    inferSteps :: [Step l] -> m Type
    inferSteps [] =
        faildoc $ text "No computational steps to type check!"

    inferSteps [LetC{}] =
        faildoc $ text "Computation may not end in let"

    inferSteps (LetC _ decl _ : k) =
        checkLocalDecl decl $
        inferSteps k

    inferSteps (step:k) =
        inferStep step >>= inferBind step k

    inferBind :: Step l -> [Step l] -> Type -> m Type
    inferBind step [] tau = do
        withFvContext step $
            void $ checkST tau
        return tau

    inferBind step [BindC{}] _ = do
        [s,a,b] <- freshenVars ["s", "a", "b"] mempty
        instST $ forallST [s,a,b] (C unitT) (tyVarT s) (tyVarT a) (tyVarT b) (srclocOf step)

    inferBind step (BindC _ wv tau _ : k) tau0 = do
        (tau', s,  a,  b) <- withFvContext step $
                             instST tau0 >>= checkSTC
        withFvContext step $
            checkTypeEquality tau' tau
        withFvContext (mkComp k) $
            extendWildVars [(wv, tau)] $ do
            tau2             <- inferSteps k >>= instST
            (omega, _, _, _) <- checkST tau2
            checkTypeEquality tau2 (stT omega s a b)
            return tau2

    inferBind step k tau = do
        withFvContext step $
            void $ checkSTC tau
        inferSteps k

inferStep :: forall l m . (IsLabel l, MonadTc m) => Step l -> m Type
inferStep (VarC _ v _) =
    lookupVar v >>= instST

inferStep (CallC _ f ies args _) = do
    tau_f           <- lookupVar f
    (taus, tau_ret) <- inferCall tau_f ies args
    zipWithM_ checkArg args taus
    unless (isPureishT tau_ret) $ do
        args' <- concat <$> zipWithM argRefs args taus
        checkNoAliasing args'
    instST tau_ret
  where
    checkArg :: Arg l -> Type -> m ()
    checkArg (ExpA e) tau =
        withFvContext e $ do
        tau' <- inferExp e
        checkPure tau'
        checkTypeEquality tau tau'

    checkArg (CompA c) tau =
        withFvContext c $ do
        tau' <- inferComp c
        void $ checkST tau
        tau'' <- instST tau'
        checkTypeEquality tau tau''

    -- We treat all free variables of ref type in a computation argument as if
    -- we were passing the whole ref. This is an approximation, but we don't
    -- have a clean way to extract all the free "ref paths" from a computation.
    argRefs :: Arg l -> Type -> m [(Exp, Type)]
    argRefs (ExpA e) tau =
        return [(e, tau)]

    argRefs (CompA c) _ = do
        taus <- mapM lookupVar vs
        return [(varE v, tau) | (v, tau) <- vs `zip` taus, isRefT tau]
      where
        vs :: [Var]
        vs = fvs c

inferStep (IfC _ e1 e2 e3 _) = do
    tau1 <- inferExp e1
    if isCompT tau1
      then do (tau1', _, _, _) <- checkSTC tau1
              checkTypeEquality tau1' boolT
      else checkTypeEquality tau1 boolT
    tau <- withFvContext e2 $ inferComp e2
    withFvContext e3 $ checkComp e3 tau
    return tau

inferStep LetC{} =
    faildoc $ text "Let computation step does not have a type."

inferStep (WhileC _ e c _) = do
    withFvContext e $ do
        (_, tau, _, _, _) <- inferExp e >>= checkPureishSTC
        checkTypeEquality tau boolT
    withFvContext c $ do
        tau <- inferComp c
        void $ checkSTCUnit tau
        return tau

inferStep (ForC _ _ v tau gint c _) = do
    checkKind tau intK
    traverse_ (\e -> withFvContext e $ checkExp e tau) gint
    extendVars [(v, tau)] $
        withFvContext c $ do
        tau_body <- inferComp c
        void $ checkSTCUnit tau_body
        return tau_body

-- A lifted expression /must/ be pureish.
inferStep (LiftC _ e _) =
    withFvContext e $ do
    tau <- inferExp e
    unless (isPureishT tau) $
        faildoc $ text "Lifted expression must be pureish but has type" <+> ppr tau
    instST tau

inferStep (ReturnC _ e _) =
    withFvContext e $ do
    tau <- inferExp e
    unless (isPureT tau) $
        faildoc $ text "Returned expression must be pure but has type" <+> ppr tau
    [s,a,b] <- freshenVars ["s", "a", "b"] (fvs tau)
    instST $ forallST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) (srclocOf e)

inferStep BindC{} =
    faildoc $ text "Bind computation step does not have a type."

inferStep (TakeC _ tau l) = do
    checkKind tau tauK
    [b] <- freshenVars ["b"] (fvs tau)
    instST $ forallST [b] (C tau) tau tau (tyVarT b) l

inferStep (TakesC _ n tau l) = do
    checkKind n NatK
    checkKind tau tauK
    [b] <- freshenVars ["b"] (fvs tau)
    instST $ forallST [b] (C (arrT n tau)) tau tau (tyVarT b) l

inferStep (EmitC _ e l) = do
    tau   <- withFvContext e $ inferExp e
    [s,a] <- freshenVars ["s", "a"] (fvs tau)
    instST $ forallST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l

inferStep (EmitsC _ e l) = do
    (_, tau) <- withFvContext e $ inferExp e >>= checkArrT
    [s,a]    <- freshenVars ["s", "a"] (fvs tau)
    instST $ forallST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l

inferStep (RepeatC _ _ c l) = do
    (s, a, b) <- withFvContext c $ inferComp c >>= checkSTCUnit
    return $ forallST [] T s a b l

inferStep step@(ParC _ b e1 e2 l) = do
    (s, a, c) <- askSTIndices
    (omega1, s', a',    b') <- withFvContext e1 $
                               localSTIndices (Just (s, a, b)) $
                               inferComp e1 >>= checkST
    (omega2, b'', b''', c') <- withFvContext e2 $
                               localSTIndices (Just (b, b, c)) $
                               inferComp e2 >>= checkST
    withFvContext e1 $
        checkTypeEquality (stT omega1 s'  a'   b') (stT omega1 s a b)
    withFvContext e2 $
        checkTypeEquality (stT omega2 b'' b''' c') (stT omega2 b b c)
    omega <- withFvContext step $
             joinOmega omega1 omega2
    return $ ST omega s a c l

checkComp :: (IsLabel l, MonadTc m)
          => Comp l
          -> Type
          -> m ()
checkComp comp tau = do
    tau' <- inferComp comp
    checkTypeEquality tau' tau

-- | 'compToExp' will convert a pureish computation back to an expression.
compToExp :: forall l m . (IsLabel l, MonadTc m)
          => Comp l
          -> m Exp
compToExp comp =
    withSummaryContext comp $
    stepsToExp (unComp comp)
  where
    stepsToExp :: [Step l] -> m Exp
    stepsToExp [] =
        panicdoc $
        text "compToExp: No computational steps to convert to an expression!"

    stepsToExp [step] =
        stepToExp step

    stepsToExp (LetC _ decl _ : steps) = do
        e <- stepsToExp steps
        return $ LetE decl e (decl `srcspan` e)

    stepsToExp (step : BindC _ wv tau _ : steps) = do
        e1 <- stepToExp  step
        e2 <- stepsToExp steps
        return $ BindE wv tau e1 e2 (e1 `srcspan` e2)

    stepsToExp (step : steps) = do
        e1  <- stepToExp  step
        tau <- inferExp e1
        e2  <- stepsToExp steps
        return $ BindE WildV tau e1 e2 (e1 `srcspan` e2)

    stepToExp :: Step l -> m Exp
    stepToExp (VarC _ v l) =
        pure $ VarE v l

    stepToExp (CallC _ f taus args l) =
        CallE f taus <$> mapM argToExp args <*> pure l

    stepToExp (IfC _ e1 c2 c3 l) =
        IfE e1 <$> compToExp c2 <*> compToExp c3 <*> pure l

    stepToExp LetC{} =
        faildoc $ text "compToExp: saw let."

    stepToExp (WhileC _ e1 c2 l) =
        WhileE e1 <$> compToExp c2 <*> pure l

    stepToExp (ForC _ ann v tau gint c3 l) =
        ForE ann v tau gint <$> compToExp c3 <*> pure l

    stepToExp (LiftC _ e _) =
        pure e

    stepToExp (ReturnC _ e l) =
        pure $ ReturnE AutoInline e l

    stepToExp BindC{} =
        faildoc $ text "compToExp: saw bind."

    stepToExp TakeC{} =
        faildoc $ text "compToExp: saw take."

    stepToExp TakesC{} =
        faildoc $ text "compToExp: saw takes."

    stepToExp EmitC{} =
        faildoc $ text "compToExp: saw emit."

    stepToExp EmitsC{} =
        faildoc $ text "compToExp: saw emits."

    stepToExp RepeatC{} =
        faildoc $ text "compToExp: saw repeat."

    stepToExp ParC{} =
        faildoc $ text "compToExp: saw >>>."

    argToExp :: Arg l -> m Exp
    argToExp (ExpA e)  = return e
    argToExp (CompA c) = compToExp c
