{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Auto.Lint
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Auto.Lint (
    withTc,

    checkProgram,

    inferComp,
    inferStep,

    inferExp,
    checkExp,

    inferKind,
    checkKind,

    checkArrT,
    checkST,
    checkFunT
  ) where

import Control.Monad (when,
                      zipWithM_,
                      void)
import Data.Loc
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Lint (checkCast,
                 checkTypeEquality,
                 inferKind,
                 checkKind,

                 absSTScope,
                 appSTScope,

                 checkEqT,
                 checkOrdT,
                 checkBoolT,
                 checkBitT,
                 checkIntT,
                 checkNumT,
                 checkArrT,
                 checkStructT,
                 checkStructFieldT,
                 checkST,
                 checkSTC,
                 checkSTCUnit,
                 checkRefT,
                 checkFunT)
import KZC.Lint.Monad
import KZC.Summary
import KZC.Vars

checkProgram :: IsLabel l
             => Program l
             -> Tc r s ()
checkProgram (Program decls comp tau) =
    checkDecls decls $
    localLocContext comp (text "In definition of main") $
    inSTScope tau $
    inLocalScope $
    checkComp comp tau

checkDecls :: forall l r s a . IsLabel l
           => [Decl l] -> Tc r s a -> Tc r s a
checkDecls decls k =
    go decls
  where
    go :: [Decl l] -> Tc r s a
    go [] =
        k

    go (decl:decls) =
        checkDecl decl $
        go decls

checkDecl :: IsLabel l
          => Decl l
          -> Tc r s a
          -> Tc r s a
checkDecl decl@(LetD v tau e _) k = do
    withSummaryContext decl $ do
        void $ inferKind tau
        tau' <- withFvContext e $
                inSTScope tau $
                inLocalScope $
                inferExp e >>= absSTScope
        checkTypeEquality tau' tau
        when (not (isPureishT tau)) $
          faildoc $ text "Value" <+> ppr v <+> text "is not pureish but is in a let!"
    extendVars [(v, tau)] k

checkDecl decl@(LetFunD f iotas vbs tau_ret e l) k = do
    withSummaryContext decl $
        checkKind tau PhiK
    extendVars [(f, tau)] $ do
    withSummaryContext decl $ do
        tau_ret' <- withFvContext e $
                    extendIVars (iotas `zip` repeat IotaK) $
                    extendVars vbs $
                    inSTScope tau_ret $
                    inLocalScope $
                    inferExp e >>= absSTScope
        checkTypeEquality tau_ret' tau_ret
        when (not (isPureishT tau)) $
          faildoc $ text "Function" <+> ppr f <+> text "is not pureish but is in a letfun!"
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

checkDecl decl@(LetExtFunD f iotas vbs tau_ret l) k = do
    withSummaryContext decl $ checkKind tau PhiK
    extendVars [(f, tau)] k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

checkDecl decl@(LetRefD v tau Nothing _) k = do
    withSummaryContext decl $ checkKind tau TauK
    extendVars [(v, refT tau)] k

checkDecl decl@(LetRefD v tau (Just e) _) k = do
    withSummaryContext decl $
        inLocalScope $ do
        checkKind tau TauK
        checkExp e tau
    extendVars [(v, refT tau)] k

checkDecl decl@(LetStructD s flds l) k = do
    withSummaryContext decl $ do
        checkStructNotRedefined s
        checkDuplicates "field names" fnames
        mapM_ (\tau -> checkKind tau TauK) taus
    extendStructs [StructDef s flds l] k
  where
    (fnames, taus) = unzip flds

    checkStructNotRedefined :: Struct -> Tc r s ()
    checkStructNotRedefined s = do
      maybe_sdef <- maybeLookupStruct s
      case maybe_sdef of
        Nothing   -> return ()
        Just sdef -> faildoc $ text "Struct" <+> ppr s <+> text "redefined" <+>
                     parens (text "original definition at" <+> ppr (locOf sdef))

checkDecl decl@(LetCompD v tau comp _) k = do
    withSummaryContext decl $ do
        void $ inferKind tau
        tau' <- withSummaryContext comp $
                inSTScope tau $
                inLocalScope $
                inferComp comp >>= absSTScope
        checkTypeEquality tau' tau
        when (isPureishT tau) $
          faildoc $ text "Value" <+> ppr v <+> text "is pureish but is in a letcomp!"
    extendVars [(v, tau)] k

checkDecl decl@(LetFunCompD f iotas vbs tau_ret comp l) k = do
    withSummaryContext decl $
        checkKind tau PhiK
    extendVars [(f, tau)] $ do
    withSummaryContext decl $ do
        tau_ret' <- withFvContext comp $
                    extendIVars (iotas `zip` repeat IotaK) $
                    extendVars vbs $
                    inSTScope tau_ret $
                    inLocalScope $
                    inferComp comp >>= absSTScope
        checkTypeEquality tau_ret' tau_ret
        when (isPureishT tau_ret) $
          faildoc $ text "Function" <+> ppr f <+> text "is pureish but is in a letfuncomp!"
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

checkLocalDecl :: LocalDecl -> Tc r s a -> Tc r s a
checkLocalDecl decl@(LetLD v tau e _) k = do
    withSummaryContext decl $ do
        void $ inferKind tau
        tau' <- withFvContext e $
                inSTScope tau $
                inLocalScope $
                inferExp e >>= absSTScope
        checkTypeEquality tau' tau
    extendVars [(v, tau)] k

checkLocalDecl decl@(LetRefLD v tau Nothing _) k = do
    withSummaryContext decl $ checkKind tau TauK
    extendVars [(v, refT tau)] k

checkLocalDecl decl@(LetRefLD v tau (Just e) _) k = do
    withSummaryContext decl $
        inLocalScope $ do
        checkKind tau TauK
        checkExp e tau
    extendVars [(v, refT tau)] k

inferExp :: Exp -> Tc r s Type
inferExp (ConstE c l) =
    checkConst c
  where
    checkConst :: Const -> Tc r s Type
    checkConst UnitC       = return (UnitT l)
    checkConst(BoolC {})   = return (BoolT l)
    checkConst(BitC {})    = return (BitT l)
    checkConst(IntC w s _) = return (IntT w s l)
    checkConst(FloatC w _) = return (FloatT w l)
    checkConst(StringC _)  = return (StringT l)

    checkConst(ArrayC cs) = do
        taus <- mapM checkConst cs
        case taus of
          [] -> faildoc $ text "Empty array"
          tau:taus | all (== tau) taus -> return tau
                   | otherwise -> faildoc $ text "Constant array elements do not all have the same type"

inferExp (VarE v _) =
    lookupVar v

inferExp (UnopE op e1 _) = do
    tau1 <- inferExp e1
    unop op tau1
  where
    unop :: Unop -> Type -> Tc r s Type
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
        mkSigned (IntT w _ l) = IntT w Signed l
        mkSigned tau          = tau

    unop (Cast tau2) tau1 = do
        checkCast tau1 tau2
        return tau2

    unop Len tau = do
        _ <- checkArrT tau
        return intT

inferExp (BinopE op e1 e2 _) = do
    tau1 <- inferExp e1
    tau2 <- inferExp e2
    binop op tau1 tau2
  where
    binop :: Binop -> Type -> Type -> Tc r s Type
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

    checkEqBinop :: Type -> Type -> Tc r s Type
    checkEqBinop tau1 tau2 = do
        checkEqT tau1
        checkTypeEquality tau2 tau1
        return boolT

    checkOrdBinop :: Type -> Type -> Tc r s Type
    checkOrdBinop tau1 tau2 = do
        checkOrdT tau1
        checkTypeEquality tau2 tau1
        return boolT

    checkBoolBinop :: Type -> Type -> Tc r s Type
    checkBoolBinop tau1 tau2 = do
        checkBoolT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkNumBinop :: Type -> Type -> Tc r s Type
    checkNumBinop tau1 tau2 = do
        checkNumT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkBitBinop :: Type -> Type -> Tc r s Type
    checkBitBinop tau1 tau2 = do
        checkBitT tau1
        checkTypeEquality tau2 tau1
        return tau1

    checkBitShiftBinop :: Type -> Type -> Tc r s Type
    checkBitShiftBinop tau1 tau2 = do
        checkBitT tau1
        checkIntT tau2
        return tau1

inferExp (IfE e1 e2 e3 _) = do
    checkExp e1 boolT
    tau <- withFvContext e2 $ inferExp e2
    withFvContext e3 $ checkExp e3 tau
    return tau

inferExp (LetE decl body _) =
    checkLocalDecl decl $ inferExp body

inferExp (CallE f ies es _) =
    inferCall f ies es

inferExp (DerefE e l) = do
    tau <- inferExp e >>= checkRefT
    appSTScope $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (AssignE e1 e2 l) = do
    tau  <- inferExp e1 >>= checkRefT
    tau' <- inferExp e2
    withFvContext e2 $ checkTypeEquality tau' tau
    appSTScope $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (WhileE e1 e2 _) = do
    withFvContext e1 $ do
        (tau, _, _, _) <- inferExp e1 >>= checkSTC
        checkTypeEquality tau boolT
    withFvContext e2 $ do
        tau <- inferExp e2
        void $ checkSTCUnit tau
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
        void $ checkSTCUnit tau_body
        return tau_body

inferExp (ArrayE es l) = do
    taus <- mapM inferExp es
    case taus of
      [] -> faildoc $ text "Empty array expression"
      tau:taus -> do mapM_ (checkTypeEquality tau) taus
                     return $ ArrT (ConstI (length es) l) tau l

inferExp (IdxE e1 e2 len l) = do
    tau <- withFvContext e1 $ inferExp e1
    withFvContext e2 $ inferExp e2 >>= checkIntT
    go tau
  where
    go :: Type -> Tc r s Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (mkArrSlice tau len) l

    go (ArrT _ tau _) = do
        return $ mkArrSlice tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (ConstI i l) tau l

inferExp (ProjE e f l) = do
    tau <- withFvContext e $ inferExp e
    go tau
  where
    go :: Type -> Tc r s Type
    go (RefT tau _) = do
        sdef  <- checkStructT tau >>= lookupStruct
        tau_f <- checkStructFieldT sdef f
        return $ RefT tau_f l

    go tau = do
        sdef  <- checkStructT tau >>= lookupStruct
        tau_f <- checkStructFieldT sdef f
        return tau_f

inferExp e0@(StructE s flds l) =
    withFvContext e0 $ do
    StructDef _ fldDefs _ <- lookupStruct s
    checkMissingFields flds fldDefs
    checkExtraFields flds fldDefs
    mapM_ (checkField fldDefs) flds
    return $ StructT s l
  where
    checkField :: [(Field, Type)] -> (Field, Exp) -> Tc r s ()
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc $ "checkField: missing field!"
               Just tau -> return tau
      checkExp e tau

    checkMissingFields :: [(Field, Exp)] -> [(Field, Type)] -> Tc r s ()
    checkMissingFields flds fldDefs =
        when (not (Set.null missing)) $
          faildoc $
            text "Struct definition has missing fields:" <+>
            (commasep . map ppr . Set.toList) missing
      where
        fs, fs', missing :: Set Field
        fs  = Set.fromList [f | (f,_) <- flds]
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        missing = fs Set.\\ fs'

    checkExtraFields :: [(Field, Exp)] -> [(Field, Type)] -> Tc r s ()
    checkExtraFields flds fldDefs =
        when (not (Set.null extra)) $
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
    appSTScope $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (ErrorE nu _ l) =
    appSTScope $ ST [s,a,b] (C nu) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (ReturnE _ e l) = do
    tau <- inferExp e
    appSTScope $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (BindE bv e1 e2 _) = do
    (tau', s,  a,  b)  <- withFvContext e1 $ do
                          inferExp e1 >>= appSTScope >>= checkSTC
    case bv of
      WildV       -> return ()
      BindV _ tau -> checkTypeEquality tau' tau
    (omega,  s', a', b') <- withFvContext e2 $
                            extendBindVars [bv] $
                            inferExp e2 >>= appSTScope >>= checkST
    withFvContext e2 $ do
    checkTypeEquality s' s
    checkTypeEquality a' a
    checkTypeEquality b' b
    return $ stT omega s a b

inferCall :: Var -> [Iota] -> [Exp] -> Tc r s Type
inferCall f ies es = do
    (ivs, taus, tau_ret) <- lookupVar f >>= checkFunT
    checkNumIotas (length ies) (length ivs)
    checkNumArgs  (length es)  (length taus)
    extendIVars (ivs `zip` repeat IotaK) $ do
    mapM_ checkIotaArg ies
    let theta = Map.fromList (ivs `zip` ies)
    let phi   = fvs taus
    zipWithM_ checkArg es (subst theta phi taus)
    appSTScope $ subst theta phi tau_ret
  where
    checkIotaArg :: Iota -> Tc r s ()
    checkIotaArg (ConstI {}) =
        return ()

    checkIotaArg (VarI iv _) =
        void $ lookupIVar iv

    checkArg :: Exp -> Type -> Tc r s ()
    checkArg e tau =
        withFvContext e $
        checkExp e tau

    checkNumIotas :: Int -> Int -> Tc r s ()
    checkNumIotas n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "index expression arguments but got" <+> ppr n

    checkNumArgs :: Int -> Int -> Tc r s ()
    checkNumArgs n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "arguments but got" <+> ppr n

checkExp :: Exp -> Type -> Tc r s ()
checkExp e tau = do
    tau' <- inferExp e
    checkTypeEquality tau' tau

inferComp :: forall l r s . IsLabel l => Comp l -> Tc r s Type
inferComp comp =
    inferSteps (unComp comp)
  where
    inferSteps :: [Step l] -> Tc r s Type
    inferSteps [] =
        faildoc $ text "No computational steps to type check!"

    inferSteps (LetC _ decl _ : k) =
        checkLocalDecl decl $
        inferSteps k

    inferSteps (step:k) =
        inferStep step >>= inferBind step k

    inferBind :: Step l -> [Step l] -> Type -> Tc r s Type
    inferBind step [] tau = do
        withFvContext step $
            void $ checkST tau
        return tau

    inferBind step (BindC _ bv _ : k) tau0 = do
        (tau', s,  a,  b) <- withFvContext step $
                             appSTScope tau0 >>= checkSTC
        case bv of
          WildV       -> return ()
          BindV _ tau -> checkTypeEquality tau' tau
        (omega,  s', a', b') <- extendBindVars [bv] $
                                inferSteps k >>= appSTScope >>= checkST
        checkTypeEquality s' s
        checkTypeEquality a' a
        checkTypeEquality b' b
        return $ stT omega s a b

    inferBind step k tau = do
        withFvContext step $
            void $ checkSTC tau
        inferSteps k

inferStep :: IsLabel l => Step l -> Tc r s Type
inferStep (VarC _ v _) =
    lookupVar v

inferStep (CallC _ f ies es _) =
    inferCall f ies es

inferStep (IfC _ e1 e2 e3 _) = do
    tau1 <- inferExp e1
    if isCompT tau1
      then do (tau1', _, _, _) <- checkSTC tau1
              checkTypeEquality tau1' boolT
      else checkTypeEquality tau1 boolT
    tau <- withFvContext e2 $ inferComp e2
    withFvContext e3 $ checkComp e3 tau
    return tau

inferStep step@(LetC {}) =
    withSummaryContext step $
    faildoc $ text "Let computation step does not have a type."

inferStep (LiftC _ e _) =
    inferExp e

inferStep (ReturnC _ e _) = do
    tau <- inferExp e
    tau' <- appSTScope $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) (srclocOf e)
    return tau'
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferStep step@(BindC {}) =
    withSummaryContext step $
    faildoc $ text "Bind computation step does not have a type."

inferStep (GotoC _ l) =
    appSTScope $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferStep (RepeatC _ l) =
    appSTScope $ ST [s,a,b] T (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferStep (TakeC _ tau l) = do
    checkKind tau TauK
    tau <- appSTScope $ ST [b] (C tau) tau tau (tyVarT b) l
    return tau
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
    s, a :: TyVar
    s = "s"
    a = "a"

inferStep (EmitsC _ e l) = do
    (_, tau) <- withFvContext e $ inferExp e >>= checkArrT
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

inferStep step@(ParC _ b e1 e2 l) = do
    (s, a, c) <- askSTIndTypes
    (omega1, s', a',    b') <- withFvContext e1 $
                               localSTIndTypes (Just (s, a, b)) $
                               inferComp e1 >>= checkST
    (omega2, b'', b''', c') <- withFvContext e2 $
                               localSTIndTypes (Just (b, b, c)) $
                               inferComp e2 >>= checkST
    withFvContext e1 $
        checkTypeEquality (ST [] omega1 s'  a'   b' l) (ST [] omega1 s a b l)
    withFvContext e2 $
        checkTypeEquality (ST [] omega2 b'' b''' c' l) (ST [] omega2 b b c l)
    omega <- withFvContext step $
             joinOmega omega1 omega2
    return $ ST [] omega s a c l
  where
    joinOmega :: Omega -> Omega -> Tc r s Omega
    joinOmega omega1@(C {}) (T {})        = return omega1
    joinOmega (T {})        omega2@(C {}) = return omega2
    joinOmega omega1@(T {}) (T {})        = return omega1

    joinOmega omega1 omega2 =
        faildoc $ text "Cannot join" <+> ppr omega1 <+> text "and" <+> ppr omega2

checkComp :: IsLabel l
          => Comp l
          -> Type
          -> Tc r s ()
checkComp comp tau = do
    tau' <- inferComp comp
    checkTypeEquality tau' tau
