{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  KZC.Lint
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Lint (
    withTc,

    inferExp,
    checkExp,

    inferKind,
    checkKind
  ) where

import Control.Monad (when,
                      zipWithM_,
                      void)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Text.PrettyPrint.Mainland

import Language.Core.Smart
import Language.Core.Syntax

import KZC.Lint.Monad
import KZC.Vars

inferExp :: Exp -> Tc b Type
inferExp (ConstE c l) =
    checkConst c
  where
    checkConst :: Const -> Tc b Type
    checkConst UnitC       = return (UnitT l)
    checkConst(BoolC {})   = return (BoolT l)
    checkConst(BitC {})    = return (BitT l)
    checkConst(IntC w _)   = return (IntT w l)
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
    unop :: Unop -> Type -> Tc b Type
    unop Len tau = do
        _ <- checkArrT tau
        return intT

    unop op _ = faildoc $ text "tcExp: cannot type check unary operator" <+> ppr op

inferExp (BinopE op e1 e2 _) = do
    tau1 <- inferExp e1
    tau2 <- inferExp e2
    binop op tau1 tau2
  where
    binop :: Binop -> Type -> Type -> Tc b Type
    binop Add tau1 tau2 = do
        checkNumT tau1
        checkTypeEquality tau2 tau1
        return tau1

    binop op _ _ =
        faildoc $ text "tcExp: cannot type check binary operator" <+> ppr op

inferExp (IfE e1 e2 e3 _) = do
    checkExp e1 boolT
    tau <- inferExp e2
    checkExp e3 tau
    return tau

inferExp (LetE v tau e1 e2 _) = do
    void $ inferKind tau
    tau' <- withExpContext e1 $
            absSTScope tau $
            inferExp e1
    checkTypeEquality tau' tau
    extendVars [(v, tau)] $ do
    inferExp e2

inferExp (LetFunE f iotas vbs tau_ret e1 e2 l) = do
    let tau = FunT iotas (map snd vbs) tau_ret l
    checkKind tau PhiK
    extendVars [(f, tau)] $ do
    extendIVars (iotas `zip` repeat IotaK) $ do
    extendVars vbs $ do
    tau_ret' <- withExpContext e1 $
                absSTScope tau_ret $
                inferExp e1
    checkTypeEquality tau_ret' tau_ret
    inferExp e2

inferExp (CallE f ies es _) = do
    (ivs, taus, tau_ret) <- inferExp f >>= checkFunT
    checkNumIotas (length ies) (length ivs)
    checkNumArgs  (length es)  (length taus)
    extendIVars (ivs `zip` repeat IotaK) $ do
    mapM_ checkIotaArg ies
    let theta = Map.fromList (ivs `zip` ies)
    let phi   = fvs taus
    zipWithM_ checkArg es (subst theta phi taus)
    appSTScope tau_ret
  where
    checkIotaArg :: Iota -> Tc b ()
    checkIotaArg (ConstI {}) =
        return ()

    checkIotaArg (VarI iv _) =
        void $ lookupIVar iv

    checkArg :: Exp -> Type -> Tc b ()
    checkArg e tau =
        withExpContext e $
        checkExp e tau

    checkNumIotas :: Int -> Int -> Tc b ()
    checkNumIotas n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "index expression arguments but got" <+> ppr n

    checkNumArgs :: Int -> Int -> Tc b ()
    checkNumArgs n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "arguments but got" <+> ppr n

inferExp (LetRefE v tau Nothing e2 _) = do
    checkKind tau TauK
    extendVars [(v, refT tau)] $ inferExp e2

inferExp (LetRefE v tau (Just e1) e2 _) = do
    checkKind tau TauK
    checkExp e1 tau
    extendVars [(v, refT tau)] $ inferExp e2

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
    withExpContext e2 $ checkTypeEquality tau' tau
    appSTScope $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (WhileE e1 e2 _) = do
    withExpContext e1 $
        checkExp e1 boolT
    tau <- withExpContext e2 $ inferExp e2
    void $ checkSTCUnit tau
    return tau

inferExp (UntilE e1 e2 _) = do
    withExpContext e1 $
        checkExp e1 boolT
    tau <- withExpContext e2 $ inferExp e2
    void $ checkSTCUnit tau
    return tau

inferExp (ForE v e1 e2 e3 _) = do
    withExpContext e1 $
        checkExp e1 intT
    withExpContext e2 $
        checkExp e2 intT
    tau <- extendVars [(v, intT)] $
           withExpContext e3 $
           inferExp e3
    void $ checkSTCUnit tau
    return tau

inferExp (ArrayE es l) = do
    taus <- mapM inferExp es
    case taus of
      [] -> faildoc $ text "Empty array expression"
      tau:taus -> do mapM_ (checkTypeEquality tau) taus
                     return $ ArrT (ConstI (length es) l) tau l

inferExp (IdxE e1 e2 len l) = do
    tau <- withExpContext e1 $ inferExp e1
    withExpContext e2 $ inferExp e2 >>= checkIntT
    go tau
  where
    go :: Type -> Tc b Type
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

inferExp (PrintE _ es l) = do
    mapM_ inferExp es
    appSTScope $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (ReturnE e l) = do
    tau <- inferExp e
    appSTScope $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (BindE bv e1 e2 _) = do
    (tau_bv, s,  a,  b)  <- withExpContext e1 $ do
                            inferExp e1 >>= checkSTC
    (omega,  s', a', b') <- withExpContext e2 $
                            extendBindVars [(bv, tau_bv)] $
                            inferExp e2 >>= checkST
    withExpContext e2 $ do
    checkTypeEquality s' s
    checkTypeEquality a' a
    checkTypeEquality b' b
    return $ stT omega s a b
  where
    extendBindVars :: [(BindVar, Type)] -> Tc b a -> Tc b a
    extendBindVars bvtaus m =
        extendVars [(v, tau) | (BindV v, tau) <- bvtaus] m

inferExp (TakeE tau l) = do
    checkKind tau TauK
    appSTScope $ ST [a,b] (C tau) (tyVarT a) (tyVarT a) (tyVarT b) l
  where
    a, b :: TyVar
    a = "a"
    b = "b"

inferExp (TakesE i tau l) = do
    checkKind tau TauK
    appSTScope $ ST [a,b] (C (arrKnownT i tau)) (tyVarT a) (tyVarT a) (tyVarT b) l
  where
    a, b :: TyVar
    a = "a"
    b = "b"

inferExp (EmitE e l) = do
    tau <- withExpContext e $ inferExp e
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

inferExp (EmitsE e l) = do
    (_, tau) <- withExpContext e $ inferExp e >>= checkArrKnownT
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

inferExp (RepeatE e l) = do
    (s, a, b) <- withExpContext e $ inferExp e >>= checkSTCUnit
    return $ ST [] T s a b l

inferExp (ArrE e1 e2 l) = do
    (omega1, s,  a,  b)  <- withExpContext e1 $ inferExp e1 >>= checkST
    (omega2, s', a', b') <- withExpContext e2 $ inferExp e2 >>= checkST
    checkTypeEquality s' s
    checkTypeEquality a' a
    checkTypeEquality b' b
    omega <- joinOmega omega1 omega2
    return $ ST [] omega s a b l
  where
    joinOmega :: Omega -> Omega -> Tc b Omega
    joinOmega omega1@(C {}) (T {})        = return omega1
    joinOmega (T {})        omega2@(C {}) = return omega2
    joinOmega omega1@(T {}) (T {})        = return omega1

    joinOmega omega1 omega2 =
        faildoc $ text "Cannot join" <+> ppr omega1 <+> text "and" <+> ppr omega2

inferExp e = faildoc $ nest 2 $ text "inferExp: cannot type check:" </> ppr e

checkExp :: Exp -> Type -> Tc b ()
checkExp e tau = do
    tau' <- inferExp e
    checkTypeEquality tau' tau

checkTypeEquality :: Type -> Type -> Tc b ()
checkTypeEquality tau1 tau2 =
    checkT Map.empty Map.empty tau1 tau2
  where
    checkT :: Map TyVar TyVar
           -> Map IVar IVar
           -> Type
           -> Type
           -> Tc b ()
    checkT _ _ (UnitT {}) (UnitT {}) = return ()
    checkT _ _ (BoolT {}) (BoolT {}) = return ()
    checkT _ _ (BitT {})  (BitT {})  = return ()

    checkT _ _ (IntT w1 _)   (IntT w2 _)     | w1 == w2 = return ()
    checkT _ _ (FloatT w1 _) (FloatT w2 _)   | w1 == w2 = return ()

    checkT _ _ (StringT {}) (StringT {})  = return ()

    checkT theta phi (ArrT iota1 tau1 _) (ArrT iota2 tau2 _) = do
        checkI phi iota1 iota2
        checkT theta phi tau1 tau2

    checkT _ _ (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    checkT theta phi (ST alphas_a omega_a tau1_a tau2_a tau3_a _)
                     (ST alphas_b omega_b tau1_b tau2_b tau3_b _)
        | length alphas_a == length alphas_b = do
          checkO theta phi omega_a omega_b
          checkT theta phi tau1_a tau1_b
          checkT theta' phi tau2_a tau2_b
          checkT theta' phi tau3_a tau3_b
      where
        theta' :: Map TyVar TyVar
        theta' = Map.fromList (alphas_a `zip` alphas_b) `Map.union` theta

    checkT theta phi (FunT iotas_a taus_a tau_a _)
                     (FunT iotas_b taus_b tau_b _)
        | length iotas_a == length iotas_b && length taus_a == length taus_b = do
          zipWithM_ (checkT theta phi') taus_a taus_b
          checkT theta phi' tau_a tau_b
      where
        phi' :: Map IVar IVar
        phi' = Map.fromList (iotas_a `zip` iotas_b) `Map.union` phi

    checkT theta phi (RefT tau1 _) (RefT tau2 _) =
        checkT theta phi tau1 tau2

    checkT theta _ (TyVarT alpha _) (TyVarT beta _)
        | fromMaybe alpha (Map.lookup alpha theta) == beta =
        return ()

    checkT _ _ _ _ =
        err

    checkO :: Map TyVar TyVar
           -> Map IVar IVar
           -> Omega
           -> Omega
           -> Tc b ()
    checkO theta phi (C tau1) (C tau2) =
        checkT theta phi tau1 tau2

    checkO _ _ (T {}) (T {}) =
        return ()

    checkO _ _ _ _ =
        err

    checkI :: Map IVar IVar
           -> Iota
           -> Iota
           -> Tc b ()
    checkI _ (ConstI i1 _) (ConstI i2 _) | i1 == i2 =
        return ()

    checkI phi (VarI iv1 _) (VarI iv2 _)
        | fromMaybe iv1 (Map.lookup iv1 phi) == iv2 =
        return ()

    checkI _ _ _ =
        err

    err :: Tc b ()
    err =
      faildoc $ align $
          text "Expected type:" <+> ppr tau2 </>
          text "but got:      " <+> ppr tau1

inferKind :: Type -> Tc b Kind
inferKind tau =
    inferType tau
  where
    inferType :: Type -> Tc b Kind
    inferType (UnitT {})   = return TauK
    inferType (BoolT {})   = return TauK
    inferType (BitT {})    = return TauK
    inferType (IntT {})    = return TauK
    inferType (FloatT {})  = return TauK
    inferType (StringT {}) = return TauK
    inferType (StructT {}) = return TauK

    inferType (ArrT iota tau _) = do
        inferIota iota
        kappa <- inferType tau
        checkKindEquality kappa TauK
        return TauK

    inferType (ST alphas omega tau1 tau2 tau3 _) =
        extendTyVars (alphas `zip` repeat TauK) $ do
        inferOmega omega
        checkKind tau1 TauK
        checkKind tau2 TauK
        checkKind tau3 TauK
        return MuK

    inferType (RefT tau _) = do
        checkKind tau TauK
        return RhoK

    inferType (FunT ivs taus tau _) =
        extendIVars (ivs `zip` repeat IotaK) $ do
        mapM_ inferArgType taus
        kappa <- inferType tau
        case kappa of
          TauK -> return ()
          MuK  -> return ()
          _    -> checkKindEquality kappa MuK
        return PhiK
      where
        inferArgType :: Type -> Tc b ()
        inferArgType tau = do
            kappa <- inferType tau
            case kappa of
              TauK -> return ()
              RhoK -> return ()
              _    -> checkKindEquality kappa TauK

    inferType (TyVarT alpha _) =
        lookupTyVar alpha

    inferIota :: Iota -> Tc b Kind
    inferIota (ConstI {}) = return IotaK
    inferIota (VarI iv _) = lookupIVar iv

    inferOmega :: Omega -> Tc b Kind
    inferOmega (C tau) = do
        checkKind tau TauK
        return OmegaK

    inferOmega T =
        return OmegaK

checkKind :: Type -> Kind -> Tc b ()
checkKind tau kappa = do
    kappa' <- inferKind tau
    checkKindEquality kappa' kappa

checkKindEquality :: Kind -> Kind -> Tc b ()
checkKindEquality kappa1 kappa2 | kappa1 == kappa2 =
    return ()

checkKindEquality kappa1 kappa2 =
    faildoc $ align $
    text "Expected kind:" <+> ppr kappa2 </>
    text "but got:      " <+> ppr kappa1

absSTScope :: Type -> Tc b Type -> Tc b Type
absSTScope tau m =
    scopeOver tau $
    m >>= absScope
  where
    scopeOver :: Type -> Tc b a -> Tc b a
    scopeOver (ST _ _ s a b _) m =
        localSTIndTypes (Just (s, a, b)) m

    scopeOver _ m =
        localSTIndTypes Nothing m

    absScope :: Type -> Tc b Type
    absScope (ST [] omega s a b l) = do
        (s',a',b') <- askSTIndTypes
        let alphas =  [alpha | TyVarT alpha _ <- [s',a',b']]
        return $ ST alphas omega s a b l

    absScope tau =
        return tau

appSTScope :: Type -> Tc b Type
appSTScope tau@(ST alphas omega s a b l) = do
    (s',a',b') <- askSTIndTypes
    let theta = Map.fromList [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']
                                           , alpha `elem` alphas]
    let phi   = fvs tau
    return $ ST [] omega
                (subst theta phi s)
                (subst theta phi a)
                (subst theta phi b)
                l

appSTScope tau =
    return tau

-- | Check that a type is an @arr \iota \alpha@ type, returning @\iota@ and
-- @\alpha@.
checkArrT :: Type -> Tc b (Iota, Type)
checkArrT (ArrT iota alpha _) =
    return (iota, alpha)

checkArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

checkArrKnownT :: Type -> Tc b (Int, Type)
checkArrKnownT (ArrT (ConstI i _) alpha _) =
    return (i, alpha)

checkArrKnownT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type of known length but got:" <+/> ppr tau

checkST :: Type -> Tc b (Omega, Type, Type, Type)
checkST (ST [] omega s a b _) =
    return (omega, s, a, b)

checkST tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST omega s a b' but got:" <+/> ppr tau

checkSTC :: Type -> Tc b (Type, Type, Type, Type)
checkSTC (ST [] (C tau) s a b _) =
    return (tau, s, a, b)

checkSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C tau) s a b' but got:" </> ppr tau

checkSTCUnit :: Type -> Tc b (Type, Type, Type)
checkSTCUnit (ST _ (C (UnitT _)) s a b _) =
    return (s, a, b)

checkSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C ()) s a b' but got:" <+/> ppr tau

checkRefT :: Type -> Tc b Type
checkRefT (RefT tau _) =
    return tau

checkRefT tau =
    faildoc $ nest 2 $ group $
    text "Expected ref type but got:" <+/> ppr tau

checkFunT :: Type -> Tc b ([IVar], [Type], Type)
checkFunT (FunT iotas taus tau_ret _) =
    return (iotas, taus, tau_ret)

checkFunT tau =
    faildoc $ nest 2 $ group $
    text "Expected function type but got:" <+/> ppr tau

-- | Check that a type is an integer type.
checkIntT :: Type -> Tc b ()
checkIntT (IntT _ _)     = return ()
checkIntT tau =
    faildoc $ nest 2 $ group $
    text "Expected integer type but got:" <+/> ppr tau

-- | Check that a type is a numerical type.
checkNumT :: Type -> Tc b ()
checkNumT (IntT _ _)   = return ()
checkNumT (FloatT _ _) = return ()
checkNumT tau =
    faildoc $ nest 2 $ group $
    text "Expected numerical type but got:" <+/> ppr tau
