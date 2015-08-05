{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  KZC.Lint
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Lint (
    withTc,

    checkExp
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

checkExp :: Exp -> Tc b Type
checkExp (ConstE c l) =
    checkConst c
  where
    checkConst :: Const -> Tc b Type
    checkConst UnitC           = return (UnitT l)
    checkConst(BoolC {})       = return (BoolT l)
    checkConst(BitC {})        = return (BitT l)
    checkConst(IntC w _)       = return (IntT w l)
    checkConst(FloatC w _)     = return (FloatT w l)
    checkConst(ComplexC w _ _) = return (ComplexT w l)
    checkConst(StringC _)      = return (StringT l)

    checkConst(ArrayC cs) = do
        taus <- mapM checkConst cs
        case taus of
          [] -> faildoc $ text "Empty array"
          tau:taus | all (== tau) taus -> return tau
                   | otherwise -> faildoc $ text "Constant array elements do not all have the same type"

checkExp (VarE v _) =
    lookupVar v

checkExp (UnopE op e1 _) = do
    tau1 <- checkExp e1
    unop op tau1
  where
    unop :: Unop -> Type -> Tc b Type
    unop Len tau = do
        _ <- checkArrT tau
        return intT

    unop op _ = faildoc $ text "tcExp: cannot type check unary operator" <+> ppr op

checkExp (BinopE op e1 e2 _) = do
    tau1 <- checkExp e1
    tau2 <- checkExp e2
    binop op tau1 tau2
  where
    binop :: Binop -> Type -> Type -> Tc b Type
    binop Add tau1 tau2 = do
        checkNumT tau1
        checkTypesEqual tau2 tau1
        return tau1

    binop op _ _ =
        faildoc $ text "tcExp: cannot type check binary operator" <+> ppr op

checkExp (IfE e1 e2 e3 _) = do
    tau1 <- checkExp e1
    checkTypesEqual tau1 boolT
    tau2 <- checkExp e2
    tau3 <- checkExp e3
    checkTypesEqual tau3 tau2
    return tau2

checkExp (LetE v tau e1 e2 _) = do
    tau' <- checkExp e1
    checkTypesEqual tau' tau
    extendVars [(v, tau)] $ do
    checkExp e2

checkExp (LetFunE f iotas vbs tau_ret e1 e2 l) = do
    let tau = FunT iotas (map snd vbs) tau_ret l
    extendVars [(f, tau)] $ do
    extendIVars (iotas `zip` repeat IotaK) $ do
    extendVars vbs $ do
    tau_ret' <- withExpContext e1 $ checkExp e1
    checkTypesEqual tau_ret' tau_ret
    checkExp e2

checkExp (CallE f ies es _) = do
    (ivs, taus, tau_ret) <- checkExp f >>= checkFunT
    checkNumIotas (length ies) (length ivs)
    checkNumArgs  (length es)  (length taus)
    extendIVars (ivs `zip` repeat IotaK) $ do
    mapM_ checkIotaArg ies
    let theta = Map.fromList (ivs `zip` ies)
    let phi   = fvs taus
    zipWithM_ checkArg es (subst theta phi taus)
    return tau_ret
  where
    checkIotaArg :: Iota -> Tc b ()
    checkIotaArg (ConstI {}) =
        return ()

    checkIotaArg (VarI iv _) =
        void $ lookupIVar iv

    checkArg :: Exp -> Type -> Tc b ()
    checkArg e tau =
        withExpContext e $ do
        tau' <- checkExp e
        checkTypesEqual tau' tau

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

checkExp (TyAbsE alphas e l) =
    extendTyVars (alphas `zip` repeat TauK) $ do
    (omega, s, a, b) <- checkExp e >>= checkST
    return $ ST alphas omega s a b l

checkExp (TyAppE e taus l) =
    checkExp e >>= go
  where
    go :: Type -> Tc b Type
    go tau@(ST alphas omega tau1 tau2 tau3 _) = do
        when (length alphas /= length taus) $
             faildoc $
               text "Expected" <+> ppr (length alphas) <+>
               text "type arguments but got" <+> ppr (length taus)
        let theta = Map.fromList (alphas `zip` taus)
        let phi   = fvs tau
        return $ ST []
                    omega
                    (subst theta phi tau1)
                    (subst theta phi tau2)
                    (subst theta phi tau3)
                    l

    go tau =
        faildoc $
        text "Expected type of the form 'forall s a b . ST omega s a b' but got:" <+/> ppr tau

checkExp (LetRefE v tau Nothing e2 _) =
    extendVars [(v, tau)] $
    checkExp e2

checkExp (LetRefE v tau (Just e1) e2 _) = do
    tau' <- checkExp e1
    checkTypesEqual (refT tau') tau
    extendVars [(v, tau)] $ do
    checkExp e2

checkExp (DerefE e l) = do
    tau <- checkExp e >>= checkRefT
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

checkExp (AssignE e1 e2 l) = do
    tau  <- checkExp e1 >>= checkRefT
    tau' <- checkExp e2
    withExpContext e2 $ checkTypesEqual tau' tau
    return $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

checkExp (WhileE e1 e2 _) = do
    tau_e1 <- withExpContext e1 $ checkExp e1
    checkTypesEqual tau_e1 boolT
    tau_e2 <- withExpContext e2 $ checkExp e2
    void $ checkSTCUnit tau_e2
    return tau_e2

checkExp (UntilE e1 e2 _) = do
    tau_e1 <- withExpContext e1 $ checkExp e1
    checkTypesEqual tau_e1 boolT
    tau_e2 <- withExpContext e2 $ checkExp e2
    void $ checkSTCUnit tau_e2
    return tau_e2

checkExp (ForE v e1 e2 e3 _) = do
    tau_e1 <- withExpContext e1 $ checkExp e1
    checkTypesEqual tau_e1 intT
    tau_e2 <- withExpContext e2 $ checkExp e2
    checkTypesEqual tau_e2 intT
    tau_e3 <- extendVars [(v, intT)] $
              withExpContext e3 $
              checkExp e3
    void $ checkSTCUnit tau_e3
    return tau_e3

checkExp (ArrayE es l) = do
    taus <- mapM checkExp es
    case taus of
      [] -> faildoc $ text "Empty array expression"
      tau:taus -> do mapM_ (checkTypesEqual tau) taus
                     return $ ArrT (ConstI (length es) l) tau l

checkExp (IdxE e1 e2 len l) = do
    tau <- withExpContext e1 $ checkExp e1
    withExpContext e2 $ checkExp e2 >>= checkIntT
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

checkExp (PrintE _ es l) = do
    mapM_ checkExp es
    return $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

checkExp (ReturnE e l) = do
    tau <- checkExp e
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

checkExp (BindE bv e1 e2 _) = do
    (tau_bv, s,  a,  b)  <- withExpContext e1 $
                            checkExp e1 >>= checkSTC
    (omega,  s', a', b') <- withExpContext e2 $
                            extendBindVars [(bv, tau_bv)] $
                            checkExp e2 >>= checkST
    withExpContext e2 $ do
    checkTypesEqual s' s
    checkTypesEqual a' a
    checkTypesEqual b' b
    return $ stT omega s a b
  where
    extendBindVars :: [(BindVar, Type)] -> Tc b a -> Tc b a
    extendBindVars bvtaus m =
        extendVars [(v, tau) | (BindV v, tau) <- bvtaus] m

checkExp (TakeE tau l) =
    return $ ST [a,b] (C tau) (tyVarT a) (tyVarT a) (tyVarT b) l
  where
    a, b :: TyVar
    a = "a"
    b = "b"

checkExp (TakesE i tau l) =
    return $ ST [a,b] (C (arrKnownT i tau)) (tyVarT a) (tyVarT a) (tyVarT b) l
  where
    a, b :: TyVar
    a = "a"
    b = "b"

checkExp (EmitE e l) = do
    tau <- withExpContext e $ checkExp e
    return $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

checkExp (EmitsE e l) = do
    (_, tau) <- withExpContext e $ checkExp e >>= checkArrKnownT
    return $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

checkExp (RepeatE e l) = do
    (s, a, b) <- withExpContext e $ checkExp e >>= checkSTCUnit
    return $ ST [] T s a b l

checkExp (ArrE e1 e2 l) = do
    (omega1, s,  a,  b)  <- withExpContext e1 $ checkExp e1 >>= checkST
    (omega2, s', a', b') <- withExpContext e2 $ checkExp e2 >>= checkST
    checkTypesEqual s' s
    checkTypesEqual a' a
    checkTypesEqual b' b
    omega <- joinOmega omega1 omega2
    return $ ST [] omega s a b l
  where
    joinOmega :: Omega -> Omega -> Tc b Omega
    joinOmega omega1@(C {}) (T {})        = return omega1
    joinOmega (T {})        omega2@(C {}) = return omega2
    joinOmega omega1@(T {}) (T {})        = return omega1

    joinOmega omega1 omega2 =
        faildoc $ text "Cannot join" <+> ppr omega1 <+> text "and" <+> ppr omega2

checkExp e = faildoc $ nest 2 $ text "checkExp: cannot type check:" </> ppr e

checkTypesEqual :: Type -> Type -> Tc b ()
checkTypesEqual tau1 tau2 =
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

    checkT _ _ (IntT w1 _)     (IntT w2 _)     | w1 == w2 = return ()
    checkT _ _ (FloatT w1 _)   (FloatT w2 _)   | w1 == w2 = return ()
    checkT _ _ (ComplexT w1 _) (ComplexT w2 _) | w1 == w2 = return ()

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
    text "Expected type of the form 'ST (C ()) s a b' but got:" </> ppr tau

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
checkNumT (IntT _ _)     = return ()
checkNumT (FloatT _ _)   = return ()
checkNumT (ComplexT _ _) = return ()
checkNumT tau =
    faildoc $ nest 2 $ group $
    text "Expected numerical type but got:" <+/> ppr tau
