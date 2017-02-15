{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Lint
-- Copyright   :  (c) 2015-2016 Drexel University
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

    checkEqT,
    checkOrdT,
    checkBoolT,
    checkBitT,
    checkIntT,
    checkNumT,
    checkArrT,
    checkKnownArrT,
    checkArrOrRefArrT,
    checkStructT,
    checkStructOrRefStructT,
    checkStructFieldT,
    checkRefT,
    checkFunT,

    absSTScope,
    appSTScope,
    checkST,
    checkSTC,
    checkSTCUnit,
    checkPure,
    checkPureish,
    checkPureishST,
    checkPureishSTC,
    checkPureishSTCUnit
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (unless,
                      void,
                      when,
                      zipWithM,
                      zipWithM_)
import Data.Foldable (traverse_)
import Data.Loc
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Check.Path
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Expr.Lint (Tc(..),
                      runTc,
                      liftTc,

                      checkConst,
                      inferConst,

                      inferKind,
                      checkKind,
                      checkTauOrRhoKind,

                      checkCast,
                      checkBitcast,

                      checkTypeEquality,

                      joinOmega,

                      checkEqT,
                      checkOrdT,
                      checkBoolT,
                      checkBitT,
                      checkIntT,
                      checkNumT,
                      checkArrT,
                      checkKnownArrT,
                      checkArrOrRefArrT,
                      checkStructT,
                      checkStructOrRefStructT,
                      checkStructFieldT,
                      checkRefT,
                      checkFunT,

                      absSTScope,
                      appSTScope,
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
checkDecl (LetD decl _) k =
    checkLocalDecl decl k

checkDecl decl@(LetFunD f ns vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    alwaysWithSummaryContext decl $ do
        checkKind tau PhiK
        tau_ret' <- extendLetFun f ns vbs tau_ret $
                    withFvContext e $
                    inferExp e >>= absSTScope
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

checkDecl decl@(LetStructD s flds l) k = do
    alwaysWithSummaryContext decl $ do
        checkStructNotRedefined s
        checkDuplicates "field names" fnames
        mapM_ (`checkKind` TauK) taus
    extendStructs [StructDef s flds l] k
  where
    (fnames, taus) = unzip flds

    checkStructNotRedefined :: Struct -> m ()
    checkStructNotRedefined s = do
      maybe_sdef <- maybeLookupStruct s
      case maybe_sdef of
        Nothing   -> return ()
        Just sdef -> faildoc $ text "Struct" <+> ppr s <+> text "redefined" <+>
                     parens (text "original definition at" <+> ppr (locOf sdef))

checkDecl decl@(LetCompD v tau comp _) k = do
    alwaysWithSummaryContext decl $ do
        checkKind tau MuK
        tau' <- extendLet v tau $
                withSummaryContext comp $
                inferComp comp >>= absSTScope
        checkTypeEquality tau' tau
    extendVars [(bVar v, tau)] k

checkDecl decl@(LetFunCompD f ns vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $ do
    alwaysWithSummaryContext decl $ do
        checkKind tau PhiK
        tau_ret' <- extendLetFun f ns vbs tau_ret $
                    withFvContext comp $
                    inferComp comp >>= absSTScope
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
    withFvContext e $ checkExp e uintT
    go tau_v
  where
    go :: Type -> m Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (mkArrSlice tau len) l

    go (ArrT _ tau _) =
        return $ mkArrSlice tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (NatT i l) tau l

checkView :: MonadTc m => View -> Type -> m ()
checkView vw tau = do
    tau' <- inferView vw
    checkTypeEquality tau' tau

checkLocalDecl :: MonadTc m => LocalDecl -> m a -> m a
checkLocalDecl decl@(LetLD v tau e _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau TauK
        withSummaryContext e $ checkExp e tau
    extendVars [(bVar v, tau)] k

checkLocalDecl decl@(LetRefLD v tau maybe_e _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau TauK
        case maybe_e of
          Nothing -> return ()
          Just e  -> withSummaryContext e $ checkExp e tau
    extendVars [(bVar v, refT tau)] k

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

inferExp (UnopE op e1 _) = do
    tau1 <- inferExp e1
    unop op tau1
  where
    unop :: Unop -> Type -> m Type
    unop Lnot tau = do
        checkBoolT tau
        return tau

    unop Bnot tau = do
        checkBitT tau
        return tau

    unop Neg tau = do
        checkNumT tau
        return $ mkSigned tau
      where
        mkSigned :: Type -> Type
        mkSigned (FixT (U w) l) = FixT (I w) l
        mkSigned tau            = tau

    unop (Cast tau2) tau1 = do
        checkCast tau1 tau2
        return tau2

    unop (Bitcast tau2) tau1 = do
        checkBitcast tau1 tau2
        return tau2

    unop Len tau = do
        _ <- checkArrOrRefArrT tau
        return intT

inferExp (BinopE op e1 e2 _) = do
    tau1 <- inferExp e1
    tau2 <- inferExp e2
    binop op tau1 tau2
  where
    binop :: Binop -> Type -> Type -> m Type
    binop Lt tau1 tau2 =
        checkOrdBinop tau1 tau2

    binop Le tau1 tau2 =
        checkOrdBinop tau1 tau2

    binop Eq tau1 tau2 =
        checkEqBinop tau1 tau2

    binop Ge tau1 tau2 =
        checkOrdBinop tau1 tau2

    binop Gt tau1 tau2 =
        checkOrdBinop tau1 tau2

    binop Ne tau1 tau2 =
        checkEqBinop tau1 tau2

    binop Land tau1 tau2 =
        checkBoolBinop tau1 tau2

    binop Lor tau1 tau2 =
        checkBoolBinop tau1 tau2

    binop Band tau1 tau2 =
        checkBitBinop tau1 tau2

    binop Bor tau1 tau2 =
        checkBitBinop tau1 tau2

    binop Bxor tau1 tau2 =
        checkBitBinop tau1 tau2

    binop LshL tau1 tau2 =
        checkBitShiftBinop tau1 tau2

    binop LshR tau1 tau2 =
        checkBitShiftBinop tau1 tau2

    binop AshR tau1 tau2 =
        checkBitShiftBinop tau1 tau2

    binop Add tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Sub tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Mul tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Div tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Rem tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Pow tau1 tau2 =
        checkNumBinop tau1 tau2

    binop Cat tau1 tau2 = do
        (iota1, tau1_elem) <- checkArrT tau1
        (iota2, tau2_elem) <- checkArrT tau2
        checkTypeEquality tau2_elem tau1_elem
        case (iota1, iota2) of
          (NatT n _, NatT m _) -> return $ ArrT (NatT (n+m) s) tau1_elem s
          _ -> faildoc $ text "Cannot determine type of concatenation of arrays of unknown length"
      where
        s :: SrcLoc
        s = tau1 `srcspan` tau2

    checkEqBinop :: Type -> Type -> m Type
    checkEqBinop tau1 tau2 = do
        checkEqT tau1
        checkTypeEquality tau2 tau1
        return boolT

    checkOrdBinop :: Type -> Type -> m Type
    checkOrdBinop tau1 tau2 = do
        checkOrdT tau1
        checkTypeEquality tau2 tau1
        return boolT

    checkBoolBinop :: Type -> Type -> m Type
    checkBoolBinop tau1 tau2 = do
        checkBoolT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkNumBinop :: Type -> Type -> m Type
    checkNumBinop tau1 tau2 = do
        checkNumT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkBitBinop :: Type -> Type -> m Type
    checkBitBinop tau1 tau2 = do
        checkBitT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkBitShiftBinop :: Type -> Type -> m Type
    checkBitShiftBinop tau1 tau2 = do
        checkBitT tau1
        checkTypeEquality tau2 uintT
        return tau1

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
    checkLetKind TauK = return ()
    checkLetKind MuK  = return ()

    checkLetKind kappa =
      faildoc $ text "Body of let has kind" <+> ppr kappa

inferExp (CallE f ies es _) = do
    (taus, tau_ret) <- inferCall f ies es
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
    tau <- withFvContext e $ inferExp e >>= checkRefT
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp e@(AssignE e1 e2 l) = do
    tau  <- withFvContext e1 $ inferExp e1 >>= checkRefT
    tau' <- withFvContext e2 $ inferExp e2
    withFvContext e $ checkTypeEquality tau' tau
    return $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (WhileE e1 e2 _) = do
    withFvContext e1 $ do
        (_, tau, _, _, _) <- inferExp e1 >>= checkPureishSTC
        checkTypeEquality tau boolT
    withFvContext e2 $ do
        tau <- inferExp e2
        void $ checkPureishSTCUnit tau
        return tau

inferExp (ForE _ v tau e1 e2 e3 _) = do
    checkIntT tau
    withFvContext e1 $
        checkExp e1 tau
    withFvContext e2 $
        checkExp e2 tau
    extendVars [(v, tau)] $
        withFvContext e3 $ do
        tau_body <- inferExp e3
        void $ checkPureishSTCUnit tau_body
        return tau_body

inferExp (ArrayE es l) = do
    taus <- mapM inferExp es
    case taus of
      [] -> faildoc $ text "Empty array expression"
      tau:taus -> do mapM_ (checkTypeEquality tau) taus
                     return $ ArrT (NatT (length es) l) tau l

inferExp (IdxE e1 e2 len l) = do
    tau <- withFvContext e1 $ inferExp e1
    withFvContext e2 $ checkExp e2 uintT
    checkLen len
    go tau
  where
    checkLen :: Maybe Int -> m ()
    checkLen Nothing =
        return ()

    checkLen (Just len) =
        unless (len >= 0) $
        faildoc $ text "Slice length must be non-negative."

    go :: Type -> m Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (mkArrSlice tau len) l

    go (ArrT _ tau _) =
        return $ mkArrSlice tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (NatT i l) tau l

inferExp (ProjE e f l) = do
    tau <- withFvContext e $ inferExp e
    go tau
  where
    go :: Type -> m Type
    go (RefT tau _) = do
        sdef  <- checkStructT tau >>= lookupStruct
        tau_f <- checkStructFieldT sdef f
        return $ RefT tau_f l

    go tau = do
        sdef  <- checkStructT tau >>= lookupStruct
        checkStructFieldT sdef f

inferExp e0@(StructE s flds l) =
    withFvContext e0 $ do
    StructDef _ fldDefs _ <- lookupStruct s
    checkMissingFields flds fldDefs
    checkExtraFields flds fldDefs
    mapM_ (checkField fldDefs) flds
    return $ StructT s l
  where
    checkField :: [(Field, Type)] -> (Field, Exp) -> m ()
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc "checkField: missing field!"
               Just tau -> return tau
      checkExp e tau

    checkMissingFields :: [(Field, Exp)] -> [(Field, Type)] -> m ()
    checkMissingFields flds fldDefs =
        unless (Set.null missing) $
          faildoc $
            text "Struct definition has missing fields:" <+>
            (commasep . map ppr . Set.toList) missing
      where
        fs, fs', missing :: Set Field
        fs  = Set.fromList [f | (f,_) <- flds]
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        missing = fs Set.\\ fs'

    checkExtraFields :: [(Field, Exp)] -> [(Field, Type)] -> m ()
    checkExtraFields flds fldDefs =
        unless (Set.null extra) $
          faildoc $
            text "Struct definition has extra fields:" <+>
            (commasep . map ppr . Set.toList) extra
      where
        fs, fs', extra :: Set Field
        fs  = Set.fromList [f | (f,_) <- flds]
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        extra = fs' Set.\\ fs

inferExp (PrintE _ es l) = do
    mapM_ inferExp es
    return $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (ErrorE nu _ l) =
    return $ ST [s,a,b] (C nu) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (ReturnE _ e l) = do
    tau <- inferExp e
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (BindE wv tau e1 e2 _) = do
    (alphas, tau', s,  a,  b) <- withFvContext e1 $
                                 inferExp e1 >>= checkPureishSTC
    checkTypeEquality tau' tau
    withFvContext e2 $
        extendWildVars [(wv, tau)] $ do
        tau_e2              <- inferExp e2
        (_, omega, _, _, _) <- checkPureishST tau_e2
        checkTypeEquality tau_e2 (ST alphas omega s a b noLoc)
        return tau_e2

inferExp (LutE _ e) =
    inferExp e

inferExp (GenE e gs _) =
    checkGenerators gs $ \n -> do
    tau <- inferExp e
    case tau of
      ST _ (C tau') _ _ _ _ -> do checkPureish tau
                                  return $ arrKnownT n tau'
      _                     -> return $ arrKnownT n tau

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
          => Var -> [Type] -> [e] -> m ([Type], Type)
inferCall f taus args = do
    (tvks, taus_args, tau_ret) <- lookupVar f >>= checkFunT
    checkNumTypeArgs (length taus) (length tvks)
    checkNumArgs     (length args) (length taus_args)
    extendTyVars tvks $ do
      let theta = Map.fromList (map fst tvks `zip` taus)
      let phi   = fvs taus_args <> fvs tau_ret
      return (subst theta phi taus_args, subst theta phi tau_ret)
  where
    checkNumTypeArgs :: Int -> Int -> m ()
    checkNumTypeArgs n ntaus =
        when (n /= ntaus) $
             faildoc $
             text "Expected" <+> ppr ntaus <+>
             text "type arguments but got" <+> ppr n

    checkNumArgs :: Int -> Int -> m ()
    checkNumArgs n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "arguments but got" <+> ppr n

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

    go (IdxE e (ConstE (FixC _ i) _) Nothing _) path =
        go e (IdxP i 1 : path)

    go (IdxE e (ConstE (FixC _ i) _) (Just len) _) path =
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

    inferBind step [BindC{}] _ =
        appSTScope $ ST [s,a,b] (C unitT) (tyVarT s) (tyVarT a) (tyVarT b) (srclocOf step)
      where
        s = "s"
        a = "a"
        b = "b"

    inferBind step (BindC _ wv tau _ : k) tau0 = do
        (tau', s,  a,  b) <- withFvContext step $
                             appSTScope tau0 >>= checkSTC
        withFvContext step $
            checkTypeEquality tau' tau
        withFvContext (mkComp k) $
            extendWildVars [(wv, tau)] $ do
            tau2             <- inferSteps k >>= appSTScope
            (omega, _, _, _) <- checkST tau2
            checkTypeEquality tau2 (stT omega s a b)
            return tau2

    inferBind step k tau = do
        withFvContext step $
            void $ checkSTC tau
        inferSteps k

inferStep :: forall l m . (IsLabel l, MonadTc m) => Step l -> m Type
inferStep (VarC _ v _) =
    lookupVar v >>= appSTScope

inferStep (CallC _ f ies args _) = do
    (taus, tau_ret) <- inferCall f ies args
    zipWithM_ checkArg args taus
    unless (isPureishT tau_ret) $ do
        args' <- concat <$> zipWithM argRefs args taus
        checkNoAliasing args'
    appSTScope tau_ret
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
        tau'' <- appSTScope tau'
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

inferStep (ForC _ _ v tau e1 e2 c _) = do
    checkIntT tau
    withFvContext e1 $
        checkExp e1 tau
    withFvContext e2 $
        checkExp e2 tau
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
    appSTScope tau

inferStep (ReturnC _ e _) =
    withFvContext e $ do
    tau <- inferExp e
    unless (isPureT tau) $
        faildoc $ text "Returned expression must be pure but has type" <+> ppr tau
    appSTScope $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) (srclocOf e)
  where
    s = "s"
    a = "a"
    b = "b"

inferStep BindC{} =
    faildoc $ text "Bind computation step does not have a type."

inferStep (TakeC _ tau l) = do
    checkKind tau TauK
    appSTScope $ ST [b] (C tau) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferStep (TakesC _ i tau l) = do
    checkKind tau TauK
    appSTScope $ ST [b] (C (arrKnownT i tau)) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferStep (EmitC _ e l) = do
    tau <- withFvContext e $ inferExp e
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s = "s"
    a = "a"

inferStep (EmitsC _ e l) = do
    (_, tau) <- withFvContext e $ inferExp e >>= checkArrT
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s = "s"
    a = "a"

inferStep (RepeatC _ _ c l) = do
    (s, a, b) <- withFvContext c $ inferComp c >>= checkSTCUnit
    return $ ST [] T s a b l

inferStep step@(ParC _ b e1 e2 l) = do
    (s, a, c) <- askSTIndTypes
    (omega1, s', a',    b') <- withFvContext e1 $
                               localSTIndTypes (Just (s, a, b)) $
                               inferComp e1 >>= checkST
    (omega2, b'', b''', c') <- withFvContext e2 $
                               localSTIndTypes (Just (b, b, c)) $
                               inferComp e2 >>= checkST
    withFvContext e1 $
        checkTypeEquality (stT omega1 s'  a'   b') (stT omega1 s a b)
    withFvContext e2 $
        checkTypeEquality (stT omega2 b'' b''' c') (stT omega2 b b c)
    omega <- withFvContext step $
             joinOmega omega1 omega2
    return $ ST [] omega s a c l

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

    stepToExp (CallC _ f iotas args l) =
        CallE f iotas <$> mapM argToExp args <*> pure l

    stepToExp (IfC _ e1 c2 c3 l) =
        IfE e1 <$> compToExp c2 <*> compToExp c3 <*> pure l

    stepToExp LetC{} =
        faildoc $ text "compToExp: saw let."

    stepToExp (WhileC _ e1 c2 l) =
        WhileE e1 <$> compToExp c2 <*> pure l

    stepToExp (ForC _ ann v tau e1 e2 c3 l) =
        ForE ann v tau e1 e2 <$> compToExp c3 <*> pure l

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
