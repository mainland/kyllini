{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Check (
    Expected,
    readExpected,

    checkProgram,

    tcExp,
    checkExp,
    inferExp
  ) where

import Control.Applicative hiding ((<|>))
import Control.Monad (filterM,
                      when,
                      replicateM,
                      zipWithM,
                      zipWithM_)
import Control.Monad.Ref
import Data.IORef
import Data.List (sort)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import qualified Language.Core.Smart as C
import qualified Language.Core.Syntax as C
import qualified Language.Ziria.Syntax as Z

import KZC.Check.Monad
import KZC.Check.Smart
import KZC.Check.Types
import KZC.Error
import KZC.Summary
import KZC.Util.SetLike
import KZC.Vars

data Expected a = Infer (IORef a)
                | Check a
  deriving (Show)

readExpected :: MonadRef IORef m => Expected a -> m a
readExpected (Infer r)   = readRef r
readExpected (Check tau) = return tau

checkProgram :: [Z.CompLet] -> Tc C.Exp C.Exp
checkProgram cls = do
    mce <- go cls
    mce
  where
    go :: [Z.CompLet] -> Tc C.Exp (Tc b C.Exp)
    go []       = return $ return $ C.varE (C.mkVar "main")
    go (cl:cls) = checkCompLet cl $ go cls

checkLet :: Z.Var -> Maybe Z.Type -> Kind -> Z.Exp
         -> Tc b (Type, Tc c C.Exp)
checkLet v ztau kappa e = do
    tau <- fromZ (ztau, kappa)
    extendVars [(v, tau)] $ do
    mce1 <- checkExp e tau
    return (tau, mce1)

checkLetRef :: Z.Var -> Z.Type -> Maybe Z.Exp
            -> Tc b (Type, Tc c (Maybe C.Exp))
checkLetRef v ztau e_init = do
    tau <- fromZ ztau
    extendVars [(v, refT tau)] $ do
    mce1 <- case e_init of
              Nothing -> return $ return Nothing
              Just e  -> do mce <- checkExp e tau
                            return $ Just <$> mce
    return (refT tau, mce1)

checkLetFun :: Z.Var -> Maybe Z.Type -> [Z.VarBind] -> Z.Exp -> SrcLoc
            -> Tc b (Type, [(Z.Var, Type)], Tc c C.Exp -> Tc c C.Exp)
checkLetFun f ztau ps e l = do
    tau   <- fromZ (ztau, PhiK)
    ptaus <- mapM fromZ ps
    mce1  <- extendVars ((f,tau) : ptaus) $ do
             (tau_ret, mce1) <- inferExp e
             unifyTypes (funT (map snd ptaus) tau_ret) tau
             return mce1
    tau_gen@(FunT iotas _ _ _) <- generalize tau
    traceVar f tau_gen
    let mkLetFun mce2 = do
        extendIVars (iotas `zip` repeat IotaK) $ do
        cf      <- trans f
        ciotas  <- mapM trans iotas
        cptaus  <- mapM trans ptaus
        ctau    <- trans tau_gen
        ce1     <- mce1
        ce2     <- mce2
        return $ C.LetFunE cf ciotas cptaus ctau ce1 ce2 l
    return (tau_gen, ptaus, mkLetFun)

derefRvalueE :: C.Exp -> Tc b C.Exp
derefRvalueE ce1 = do
    cx <- C.mkUniqVar "x" l
    modifyRvalCtx $ \ce2 -> C.bindE cx (C.derefE ce1) ce2
    return $ C.VarE cx l
  where
    l :: SrcLoc
    l = srclocOf ce1

checkCompLet :: Z.CompLet
             -> Tc b (Tc c C.Exp)
             -> Tc b (Tc c C.Exp)
checkCompLet cl@(Z.LetCL v ztau e l) k = do
    (tau, mce1) <- withSummaryContext cl $ do
                   checkLet v ztau TauK e
    mce2        <- extendVars [(v, tau)] $
                   k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

checkCompLet cl@(Z.LetRefCL v ztau e_init l) k = do
    (tau, mce1) <- withSummaryContext cl $
                   checkLetRef v ztau e_init
    mce2        <- extendVars [(v, tau)] $
                   k
    return $ do cv   <- trans v
                ctau <- trans (refT tau)
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

checkCompLet cl@(Z.LetFunCL f ztau ps e l) k = do
    (tau, ptaus, mkLetFun) <- withSummaryContext cl $
                              checkLetFun f ztau ps e l
    mce2                   <- extendVars ((f,tau) : ptaus) $
                              k
    return $ mkLetFun mce2

checkCompLet cl@(Z.LetCompCL v ztau _ e l) k = do
    (tau, mce1) <- withSummaryContext cl $
                   checkLet v ztau MuK e
    mce2        <- extendVars [(v, tau)] $ k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

checkCompLet cl@(Z.LetFunCompCL f ztau _ ps e l) k = do
    (tau, ptaus, mkLetFun) <- withSummaryContext cl $
                              checkLetFun f ztau ps e l
    mce2                   <- extendVars ((f,tau) : ptaus) $
                              k
    return $ mkLetFun mce2

checkCompLet e _ = faildoc $ text "checkCompLet: can't type check:" <+> ppr e

tcExp :: Z.Exp -> Expected Type -> Tc b (Tc c C.Exp)
tcExp (Z.ConstE zc l) exp_ty = do
    cc <- tcConst zc
    return $ return $ C.ConstE cc l
  where
    tcConst :: Z.Const -> Tc b C.Const
    tcConst Z.UnitC = do
        instType (UnitT l) exp_ty
        return $ C.UnitC

    tcConst(Z.BoolC b) = do
        instType (BoolT l) exp_ty
        return $ C.BoolC b

    tcConst(Z.BitC b)  = do
        instType (BitT l) exp_ty
        return $ C.BitC b

    tcConst(Z.IntC zw i) = do
        w  <- fromZ zw
        cw <- trans w
        instType (IntT w l) exp_ty
        return $ C.IntC cw i

    tcConst(Z.FloatC zw f) = do
        w  <- fromZ zw
        cw <- trans w
        instType (FloatT w l) exp_ty
        return $ C.FloatC cw (toRational f)

    tcConst(Z.ComplexC zw i r) = do
        w  <- fromZ zw
        cw <- trans w
        instType (ComplexT w l) exp_ty
        return $ C.ComplexC cw i r

    tcConst(Z.StringC s)  = do
        instType (StringT l) exp_ty
        return $ C.StringC s

tcExp (Z.VarE v l) exp_ty = do
    isRval <- isRvalCtx
    tau    <- lookupVar v >>= instantiate
    go isRval tau
  where
    go :: Bool -> Type -> Tc b (Tc c C.Exp)
    -- If we are in an r-value context, we need to generate code that
    -- dereferences the variable and returns the dereferenced value.
    go True (RefT tau _) = do
        instType tau exp_ty
        return $ do cv <- trans v
                    derefRvalueE $ C.VarE cv l

    go _ tau = do
        instType tau exp_ty
        return $ do cv <- trans v
                    return $ C.VarE cv l

tcExp (Z.UnopE op e1 l) exp_ty = do
    (tau1, mce1) <- inferExp e1
    (tau, cop)   <- unop op tau1
    instType tau exp_ty
    return $ do ce1 <- mce1
                return $ C.UnopE cop ce1 l
  where
    unop :: Z.Unop -> Type -> Tc b (Type, C.Unop)
    unop Z.Len tau = do
        _ <- checkArrType tau
        return (intT, C.Len)

    unop op _ = faildoc $ text "tcExp: cannot type check unary operator" <+> ppr op

tcExp (Z.BinopE op e1 e2 l) exp_ty = do
    (tau1, mce1) <- inferExp e1
    (tau2, mce2) <- inferExp e2
    (tau, cop)   <- binop op tau1 tau2
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.BinopE cop ce1 ce2 l
  where
    binop :: Z.Binop -> Type -> Type -> Tc b (Type, C.Binop)
    binop Z.Add tau1 tau2 = do
        checkNumType tau1
        unifyTypes tau2 tau1
        return (tau1, C.Add)

    binop op _ _ =
        faildoc $ text "tcExp: cannot type check binary operator" <+> ppr op

tcExp (Z.IfE e1 e2 e3 l) exp_ty = do
    mce1 <- checkExp e1 (BoolT l)
    (tau, mce2) <- inferExp e2
    mce3        <- checkExp e3 tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                ce3 <- mce3
                return $ C.IfE ce1 ce2 ce3 l

tcExp (Z.LetE v ztau e1 e2 l) exp_ty = do
    (tau, mce1) <- checkLet v ztau TauK e1
    mce2        <- extendVars [(v, tau)] $
                   tcExp e2 exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

tcExp (Z.CallE f es l) exp_ty = do
    (taus, tau_ret) <- lookupVar f >>= checkFunType f nargs
    when (length taus /= nargs) $
        faildoc $
          text "Expected" <+> ppr nargs <+>
          text "arguments but got" <+> ppr (length taus)
    mces     <- zipWithM checkArg es taus
    tau_ret' <- instantiate tau_ret
    instType tau_ret' exp_ty
    return $ collectRvalCtx $ do
             cf  <- trans f
             ces <- sequence mces
             return $ C.CallE cf [] ces l
  where
    nargs :: Int
    nargs = length es

    -- If an argument is a ref type, then we do not want to implicitly
    -- dereference it, since it should be passed by reference. Otherwise, we
    -- assume we are in an r-value context.
    checkArg :: Z.Exp -> Type -> Tc b (Tc c C.Exp)
    checkArg e tau =
        compress tau >>= go
      where
        go :: Type -> Tc b (Tc c C.Exp)
        go (RefT {}) = checkExp e tau
        go _         = inRvalCtx $ checkExp e tau

tcExp (Z.LetRefE v ztau e1 e2 l) exp_ty = do
    (tau, mce1) <- checkLetRef v ztau e1
    mce2        <- extendVars [(v, tau)] $
                   tcExp e2 exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

tcExp (Z.AssignE e1 e2 l) exp_ty = do
    (gamma, mce1) <- withSummaryContext e1 $ do
                     (tau, mce1) <- inferExp e1
                     gamma       <- checkRefType tau
                     return (gamma, mce1)
    mce2  <- withSummaryContext e2 $
             inRvalCtx $
             checkExp e2 gamma
    tau   <- mkStCT (UnitT l)
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- collectRvalCtx mce2
                return $ C.AssignE ce1 ce2 l

tcExp (Z.WhileE e1 e2 l) exp_ty = do
    mce1        <- checkExp e1 (BoolT l)
    (tau, mce2) <- inferExp e2
    _           <- checkSTCUnitType tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.WhileE ce1 ce2 l

tcExp (Z.UntilE e1 e2 l) exp_ty = do
    mce1        <- checkExp e1 (BoolT l)
    (tau, mce2) <- inferExp e2
    _           <- checkSTCUnitType tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.UntilE ce1 ce2 l

tcExp (Z.TimesE _ e1 e2 l) exp_ty = do
    (tau1, mce1) <- inferExp e1
    checkIntType tau1
    (tau, mce2) <- inferExp e2
    _           <- checkSTCUnitType tau
    instType tau exp_ty
    return $ do cx  <- C.mkUniqVar "x" l
                ce1 <- mce1
                ce2 <- mce2
                return $ C.ForE cx (C.intE 1) ce1 ce2 l

tcExp (Z.ForE _ i ztau_i e1 e2 e3 l) exp_ty = do
    tau_i <- fromZ (ztau_i, TauK)
    checkIntType tau_i
    mce1 <- checkExp e1 tau_i
    mce2 <- checkExp e2 tau_i
    (tau, mce3) <- inferExp e3
    _           <- checkSTCUnitType tau
    instType tau exp_ty
    return $ do ci  <- trans i
                ce1 <- mce1
                ce2 <- mce2
                ce3 <- mce3
                return $ C.ForE ci ce1 ce2 ce3 l

tcExp (Z.ArrayE es l) exp_ty = do
    tau  <- newMetaTvT TauK l
    mces <- mapM (\e -> checkExp e tau) es
    instType (ArrT (ConstI (length es) l) tau l) exp_ty
    return $ do ces <- sequence mces
                return $ C.ArrayE ces l

tcExp (Z.IdxE e1 e2 len l) exp_ty = do
    isRval      <- isRvalCtx
    (tau, mce1) <- withSummaryContext e1 $
                   notInRvalCtx $
                   inferExp e1
    mce2        <- withSummaryContext e2 $ do
                   (tau2, mce2) <- inferExp e2
                   checkIntType tau2
                   return mce2
    checkIdxE isRval tau mce1 mce2
  where
    checkIdxE :: forall b c . Bool
              -> Type
              -> Tc c C.Exp
              -> Tc c C.Exp
              -> Tc b (Tc c C.Exp)
    checkIdxE isRval tau mce1 mce2 = do
        compress tau >>= go isRval
      where
        go :: Bool -> Type -> Tc b (Tc c C.Exp)
        -- If we are in an r-value context and e1 is a reference to an array, we
        -- need to generate code that will index into the array
        go True (RefT (ArrT _ tau _) _) = do
            instType (mkArrSlice tau len) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        derefRvalueE $ C.IdxE ce1 ce2 len l

        -- If we are not in an r-value context, then indexing into a reference
        -- to an array returns a reference to an element of the array.
        go False (RefT (ArrT _ tau _) _) = do
            instType (RefT (mkArrSlice tau len) l) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ C.IdxE ce1 ce2 len l

        -- A plain old array gets indexed as one would expect.
        go _ (ArrT _ tau _) = do
            instType (mkArrSlice tau len) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ C.IdxE ce1 ce2 len l

        -- Otherwise we assert that the type of @e1@ should be an array type.
        go isRval tau = do
            i     <- newMetaTvT IotaK l
            alpha <- newMetaTvT TauK l
            unifyTypes tau (ArrT i alpha l)
            compress tau >>= go isRval

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) =  ArrT (ConstI i l) tau l

tcExp (Z.PrintE newline es l) exp_ty = do
    mces  <- mapM checkArg es
    tau   <- mkStCT (UnitT l)
    instType tau exp_ty
    return $ do ces <- sequence mces
                return $ C.PrintE newline ces l
  where
    checkArg :: Z.Exp -> Tc b (Tc c C.Exp)
    checkArg e = do
        (_, mce) <- inferExp e
        return mce

tcExp (Z.ReturnE _ e l) exp_ty = do
    (tau, mce) <- inRvalCtx $ inferExp e
    kappa      <- inferKind tau
    go tau kappa mce
  where
    go :: Type -> Kind -> Tc c C.Exp -> Tc b (Tc c C.Exp)
    go tau TauK mce = do
        tau_ret <- mkStCT tau
        instType tau_ret exp_ty
        return $ do ce <- collectRvalCtx mce
                    return $ C.ReturnE ce l

    go (RefT tau _) RhoK mce = do
        tau_ret <- mkStCT tau
        instType tau_ret exp_ty
        return $ do ce <- collectRvalCtx mce
                    return $ C.ReturnE ce l

    go tau MuK mce = do
        instType tau exp_ty
        return $ do ce <- mce
                    return $ C.ReturnE ce l

    go tau _ _ = do
        checkKind tau TauK
        panicdoc $ text "Cannot reach this point"

tcExp (Z.TakeE l) exp_ty = do
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (stT (C alpha l) alpha alpha beta) exp_ty
    return $ return $ C.TakeE l

tcExp (Z.TakesE i l) exp_ty = do
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (stT (C (ArrT (ConstI i l) alpha l) l) alpha alpha beta) exp_ty
    return $ return $ C.TakesE (fromIntegral i) l

tcExp (Z.EmitE e l) exp_ty = do
    (tau, mce) <- inferExp e
    go tau mce
  where
    go :: Type -> Tc c C.Exp -> Tc b (Tc c C.Exp)
    go (ArrT _ beta _) mce = do
        sigma <- newMetaTvT TauK l
        alpha <- newMetaTvT TauK l
        instType (stT (C (UnitT l) l) sigma alpha beta) exp_ty
        return $ do ce <- mce
                    return $ C.EmitsE ce l

    go beta mce = do
        sigma <- newMetaTvT TauK l
        alpha <- newMetaTvT TauK l
        instType (stT (C (UnitT l) l) sigma alpha beta) exp_ty
        return $ do ce <- mce
                    return $ C.EmitE ce l

tcExp (Z.RepeatE _ e l) exp_ty = do
    (sigma, alpha, beta, mce) <-
        withSummaryContext e $ do
        (tau, mce)           <- inferExp e
        (sigma, alpha, beta) <- checkSTCUnitType tau
        return (sigma, alpha, beta, mce)
    instType (stT (T l) sigma alpha beta) exp_ty
    return $ do ce <- mce
                return $ C.RepeatE ce l

tcExp (Z.ArrE _ e1 e2 l) tau_exp = do
    (omega1, sigma, alpha, beta, mce1) <-
        withSummaryContext e1 $ do
        (tau_e1, mce1)               <- inferExp e1
        (omega1, sigma, alpha, beta) <- checkSTType tau_e1
        return (omega1, sigma, alpha, beta, mce1)
    (omega2, mce2) <-
        withSummaryContext e2 $ do
        omega2 <- newMetaTvT OmegaK e2
        mce2   <- checkExp e2 (stT omega2 sigma alpha beta)
        return (omega2, mce2)
    omega       <- joinOmega omega1 omega2
    instType (stT omega sigma alpha beta) tau_exp
    checkForSplitContext
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.ArrE ce1 ce2 l
  where
    checkForSplitContext :: Tc b ()
    checkForSplitContext = do
        common_refs <- filterM isRefVar (Set.toList common_fvs)
        when (not (null common_refs)) $
            faildoc $ text "Branches of arrow expression share mutable state:" <+>
                      commasep (map ppr common_refs)
      where
        common_fvs :: Set Z.Var
        common_fvs = fvs e1 `Set.intersection` fvs e2

tcExp (Z.ReadE ztau l) exp_ty = do
    alpha <- fromZ (ztau, TauK)
    beta  <- newMetaTvT TauK ztau
    instType (stT (T l) alpha alpha beta) exp_ty
    return $ do cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.varE cx)

tcExp (Z.WriteE ztau l) exp_ty = do
    sigma <- newMetaTvT TauK ztau
    alpha <- newMetaTvT TauK ztau
    beta  <- fromZ (ztau, TauK)
    instType (stT (T l) sigma alpha beta) exp_ty
    return $ do cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.varE cx)

tcExp (Z.StandaloneE e _) exp_ty =
    tcExp e exp_ty

tcExp (Z.MapE _ f ztau l) exp_ty = do
    tau  <- fromZ (ztau, PhiK)
    tau' <- lookupVar f
    unifyTypes tau' tau
    (gamma, delta, sigma, alpha, beta) <- checkMapFunType f tau
    unifyTypes sigma gamma
    unifyTypes alpha gamma
    unifyTypes beta  delta
    instType (stT (T l) sigma alpha beta) exp_ty
    return $ do cf <- trans f
                cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.callE cf [C.varE cx])

tcExp (Z.CompLetE cl e _) exp_ty =
    checkCompLet cl $
    tcExp e exp_ty

tcExp (Z.StmE stms _) exp_ty =
    tcStms stms exp_ty

tcExp (Z.CmdE cmds _) exp_ty =
    tcCmds cmds exp_ty

tcExp e _ = faildoc $ text "tcExp: can't type check:" <+> ppr e

checkExp :: Z.Exp -> Type -> Tc b (Tc c C.Exp)
checkExp e tau = tcExp e (Check tau)

inferExp :: Z.Exp -> Tc b (Type, Tc c C.Exp)
inferExp e = do
    ref <- newRef (error "inferExp: empty result")
    mce <- tcExp e (Infer ref)
    tau <- readRef ref
    return (tau, mce)

tcStms :: [Z.Stm] -> Expected Type -> Tc b (Tc c C.Exp)
tcStms (stm@(Z.LetS {}) : []) _ =
    withSummaryContext stm $
    faildoc $ text "Last statement in statement sequence must be an expression"

tcStms (stm@(Z.LetS v ztau e l) : stms) exp_ty = do
    (tau, mce1) <- withSummaryContext stm $
                   checkLet v ztau TauK e
    mce2        <- extendVars [(v, tau)] $
                   tcStms stms exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

tcStms (stm@(Z.LetRefS {}) : []) _ =
    withSummaryContext stm $
    faildoc $ text "Last statement in statement sequence must be an expression"

tcStms (stm@(Z.LetRefS v ztau e_init l) : stms) exp_ty = do
    (tau, mce1) <- withSummaryContext stm $
                   checkLetRef v ztau e_init
    mce2        <- extendVars [(v, tau)] $
                   tcStms stms exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

tcStms (stm@(Z.ExpS e _) : []) exp_ty =
    withSummaryContext stm $ do
    ce <- tcExp e exp_ty
    _  <- readExpected exp_ty >>= checkSTType
    return ce

tcStms (stm@(Z.ExpS e _) : stms) exp_ty =
    withSummaryContext stm $ do
    (tau1, mce1)            <- inferExp e
    (_, sigma, alpha, beta) <- checkSTCType tau1
    omega                   <- newMetaTvT OmegaK e
    let tau                 =  stT omega sigma alpha beta
    instType tau exp_ty
    mce2 <- checkStms stms tau
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcStms [] _ =
    panicdoc $ text "Empty statement sequence!"

checkStms :: [Z.Stm] -> Type -> Tc b (Tc c C.Exp)
checkStms stms tau = tcStms stms (Check tau)

tcCmds :: [Z.Cmd] -> Expected Type -> Tc b (Tc c C.Exp)
tcCmds (cmd@(Z.LetC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (Z.LetC cl _ : cmds) exp_ty =
    checkCompLet cl $ tcCmds cmds exp_ty

tcCmds (cmd@(Z.BindC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (cmd@(Z.BindC v ztau e l) : cmds) exp_ty = do
    (nu, tau, mce1) <-
        withSummaryContext cmd $ do
        nu    <- fromZ (ztau, TauK)
        sigma <- newMetaTvT TauK l
        alpha <- newMetaTvT TauK l
        beta  <- newMetaTvT TauK l
        extendVars [(v, nu)] $ do
        mce1    <- checkExp e (stT (C nu l) sigma alpha beta)
        omega   <- newMetaTvT OmegaK l
        let tau =  stT omega sigma alpha beta
        instType tau exp_ty
        return (nu, tau, mce1)
    mce2 <- extendVars [(v, nu)] $
            checkCmds cmds tau
    return $ do cv  <- trans v
                ce1 <- mce1
                ce2 <- mce2
                return $ C.BindE (C.BindV cv) ce1 ce2 l

tcCmds (cmd@(Z.ExpC e _) : []) exp_ty =
    withSummaryContext cmd $ do
    ce <- tcExp e exp_ty
    _  <- readExpected exp_ty >>= checkSTType
    return ce

tcCmds (cmd@(Z.ExpC e _) : cmds) exp_ty =
    withSummaryContext cmd $ do
    (tau1, mce1)            <- inferExp e
    (_, sigma, alpha, beta) <- checkSTCType tau1
    omega                   <- newMetaTvT OmegaK e
    let tau                 =  stT omega sigma alpha beta
    instType tau exp_ty
    mce2 <- tcCmds cmds exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcCmds [] _ =
    panicdoc $ text "Empty command sequence!"

checkCmds :: [Z.Cmd] -> Type -> Tc b (Tc c C.Exp)
checkCmds cmds tau = tcCmds cmds (Check tau)

kcType :: Type -> Expected Kind -> Tc b ()
kcType tau@(UnitT {})    kappa_exp = instKind tau TauK kappa_exp
kcType tau@(BoolT {})    kappa_exp = instKind tau TauK kappa_exp
kcType tau@(BitT {})     kappa_exp = instKind tau TauK kappa_exp
kcType tau@(IntT {})     kappa_exp = instKind tau TauK kappa_exp
kcType tau@(FloatT {})   kappa_exp = instKind tau TauK kappa_exp
kcType tau@(ComplexT {}) kappa_exp = instKind tau TauK kappa_exp
kcType tau@(StringT {})  kappa_exp = instKind tau TauK kappa_exp
kcType tau@(StructT {})  kappa_exp = instKind tau TauK kappa_exp
kcType tau@(ArrT {})     kappa_exp = instKind tau TauK kappa_exp

kcType tau0@(C tau _) kappa_exp = do
    checkKind tau TauK
    instKind tau0 OmegaK kappa_exp

kcType tau@(T _) kappa_exp =
    instKind tau OmegaK kappa_exp

kcType tau0@(ST alphas omega sigma tau1 tau2 _) kappa_exp = do
    checkKind omega OmegaK
    extendTyVars (alphas `zip` repeat TauK) $ do
    checkKind sigma TauK
    checkKind tau1 TauK
    checkKind tau2 TauK
    instKind tau0 MuK kappa_exp

kcType tau0@(RefT tau _) kappa_exp = do
    checkKind tau TauK
    instKind tau0 RhoK kappa_exp

kcType tau0@(FunT ivs taus tau_ret _) kappa_exp =
    extendIVars  (ivs `zip` repeat IotaK) $ do
    mapM_ (\tau -> checkKind tau RhoK) taus
    checkKind tau_ret MuK
    instKind tau0 PhiK kappa_exp

kcType tau0@(ConstI {}) kappa_exp =
    instKind tau0 IotaK kappa_exp

kcType tau0@(VarI iv _) kappa_exp = do
    kappa <- lookupIVar iv
    instKind tau0 kappa kappa_exp

kcType tau0@(TyVarT tv _) kappa_exp = do
    kappa <- lookupTyVar tv
    instKind tau0 kappa kappa_exp

kcType tau0@(MetaT (MetaTv _ kappa _) _) kappa_exp =
    instKind tau0 kappa kappa_exp

instKind :: Type -> Kind -> Expected Kind -> Tc b ()
instKind _ kappa (Infer ref) =
    writeRef ref kappa

instKind _ kappa1 (Check kappa2) | kappa1 == kappa2 =
    return ()

instKind _ TauK (Check RhoK) =
    return ()

instKind tau kappa1 (Check kappa2) = do
    [tau'] <- sanitizeTypes [tau]
    faildoc $
      text "Expected:" <+> friendly kappa2 </>
      text "but got: " <+> ppr tau' </>
      text "which is a" <+> friendly kappa1
  where
    friendly :: Kind -> Doc
    friendly TauK   = text "base type"
    friendly OmegaK = text "'C tau' or 'T'"
    friendly MuK    = text "type of the form 'ST omega tau tau'"
    friendly RhoK   = text "mutable type"
    friendly PhiK   = text "function type"
    friendly IotaK  = text "array index type"

checkKind :: Type -> Kind -> Tc b ()
checkKind tau kappa = kcType tau (Check kappa)

inferKind :: Type -> Tc b Kind
inferKind tau = do
    ref <- newRef (error "inferKind: empty result")
    kcType tau (Infer ref)
    readRef ref

generalize :: Type -> Tc b Type
generalize tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Tc b Type
    go tau@(ST [] omega sigma tau1 tau2 l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let alphaMtvs =  filter (isKind TauK) mtvs
        alphas        <- freshVars (length alphaMtvs) ((Set.toList . fvs) tau)
        extendTyVars (alphas `zip` repeat TauK) $ do
        zipWithM_ kcWriteTv alphaMtvs [TyVarT alpha noLoc | alpha <- alphas]
        return $ ST alphas omega sigma tau1 tau2 l

    go tau@(ST {}) =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau@(FunT [] taus (ST [] omega sigma tau1 tau2 l2) l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let iotaMtvs  =  filter (isKind IotaK) mtvs
        iotas         <- freshVars (length iotaMtvs) ((Set.toList . fvs) tau)
        extendIVars (iotas `zip` repeat IotaK) $ do
        zipWithM_ kcWriteTv iotaMtvs [VarI iota noLoc | iota <- iotas]
        let alphaMtvs =  filter (isKind TauK) mtvs
        alphas        <- freshVars (length alphaMtvs) ((Set.toList . fvs) tau)
        extendTyVars (alphas `zip` repeat TauK) $ do
        zipWithM_ kcWriteTv alphaMtvs [TyVarT alpha noLoc | alpha <- alphas]
        return $ FunT iotas taus (ST alphas omega sigma tau1 tau2 l2) l

    go tau@(FunT [] taus tau_ret l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let iotaMtvs  =  filter (isKind IotaK) mtvs
        iotas         <- freshVars (length iotaMtvs) ((Set.toList . fvs) tau)
        extendIVars (iotas `zip` repeat IotaK) $ do
        zipWithM_ kcWriteTv iotaMtvs [VarI iota noLoc | iota <- iotas]
        return $ FunT iotas taus tau_ret l

    go tau@(FunT {}) =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau =
        pure tau

    isKind :: Kind -> MetaTv -> Bool
    isKind kappa1 (MetaTv _ kappa2 _) = kappa2 == kappa1

instantiate :: Type -> Tc b Type
instantiate tau =
    compress tau >>= go
  where
    go :: Type -> Tc b Type
    go (ST alphas omega sigma tau1 tau2 l) = do
        (theta, phi) <- instVars alphas TauK
        return $ ST [] omega (subst theta phi sigma)
                   (subst theta phi tau1) (subst theta phi tau2) l

    go (FunT iotas taus tau_ret l) = do
        (theta, phi) <- instVars iotas IotaK
        return $ FunT [] (subst theta phi taus) (subst theta phi tau_ret) l

    go tau =
        pure tau

    instVars :: (Located tv, Subst Type tv Type)
             => [tv] -> Kind -> Tc b (Map tv Type, Set tv)
    instVars tvs kappa = do
        mtvs      <- mapM (newMetaTvT kappa) tvs
        let theta =  Map.fromList (tvs `zip` mtvs)
        let phi   =  fvs tau <\\> fromList tvs
        return (theta, phi)

-- | Update a type meta-variable with a type while checking that the type's kind
-- matches the meta-variable's kind.
kcWriteTv :: MetaTv -> Type -> Tc b ()
kcWriteTv mtv@(MetaTv _ kappa _) tau = do
    checkKind tau kappa
    writeTv mtv tau

-- | Return 'True' if @v@ has a reference type, 'False' otherwise
isRefVar :: Z.Var -> Tc b Bool
isRefVar v = do
    tau <- lookupVar v >>= compress
    case tau of
      RefT {} -> return True
      _       -> return False

checkFunType :: Z.Var -> Int -> Type -> Tc b ([Type], Type)
checkFunType _ nargs tau =
    instantiate tau >>= go
  where
    go :: Type -> Tc b ([Type], Type)
    go (FunT [] taus tau_ret _) =
        return (taus, tau_ret)

    go tau_f = do
        taus    <- replicateM nargs (newMetaTvT TauK tau)
        tau_ret <- newMetaTvT TauK tau
        unifyTypes tau_f (funT taus tau_ret)
        return (taus, tau_ret)

-- | Check that a function type is appropriate for a @map@. The function result
-- must have type @forall s a b . ST (C c) s a b@. This guarantees that although
-- it may read and write references, it neither consumes nor produces values
-- from the stream.
checkMapFunType :: Z.Var -> Type -> Tc b (Type, Type, Type, Type, Type)
checkMapFunType _ tau = do
    -- Instantiate the function type's outer forall, which quantifies over array
    -- index variables.
    tau_f <- instantiate tau
    (gamma, tau_ret) <-
        case tau_f of
          FunT [] [gamma] tau_ret@(ST {}) _ -> return (gamma, tau_ret)
          _ -> err
    -- Check that the return type of the function we are mapping is
    -- @forall s a b . ST tau s a b@.
    checkMapReturnType tau_ret
    -- XXX Instantiate over the return type, which must be an ST type. We should
    -- handle pure functions here too!
    tau_ret' <- instantiate tau_ret
    (delta, sigma, alpha, beta) <-
        case tau_ret' of
          ST [] (C delta _) sigma alpha beta _ -> return (delta, sigma, alpha, beta)
          _ -> err
    return (gamma, delta, sigma, alpha, beta)
  where
    checkMapReturnType :: Type -> Tc b ()
    checkMapReturnType (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _)
        | sort [s',a',b'] == sort [s,a,b] =
        return ()

    checkMapReturnType _ =
        err

    err :: Tc b a
    err =
        expectedTypeErr tau tau2
      where
        alpha, beta, gamma, delta, sigma :: TyVar
        alpha = TyVar "a"
        beta  = TyVar "b"
        gamma = TyVar "c"
        delta = TyVar "d"
        sigma = TyVar "s"

        tau2 :: Type
        tau2 =
            FunT []
                 [tyVarT gamma]
                 (ST [sigma, alpha, beta]
                     (C (tyVarT delta) l)
                     (tyVarT sigma)
                     (tyVarT alpha)
                     (tyVarT beta)
                     l)
                 l

    l :: SrcLoc
    l = srclocOf tau

-- | Check that a type is an array type, returning the array's size.
checkArrInd :: Type -> Tc b Type
checkArrInd (ArrT ind _ _) =
    return ind

checkArrInd tau =
    faildoc $ text "Expected array type, but got:" <+> ppr tau

-- | Check that a type is an @ref \alpha@ type, returning @\alpha@.
checkRefType :: Type -> Tc b Type
checkRefType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b Type
    go (RefT alpha _) =
        return alpha

    go tau = do
        alpha <- newMetaTvT TauK tau
        unifyTypes tau (refT alpha)
        return alpha

-- | Check that a type is an @arr \iota \alpha@ type, returning @\iota@ and
-- @\alpha@.
checkArrType :: Type -> Tc b (Type, Type)
checkArrType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type)
    go (ArrT iota alpha _) =
        return (iota, alpha)

    go tau = do
        iota  <- newMetaTvT IotaK tau
        alpha <- newMetaTvT TauK tau
        unifyTypes tau (arrT iota alpha)
        return (iota, alpha)

-- | Check that a type is an @ST \omega \sigma \alpha \beta@ type, returning the
-- four type indices
checkSTType :: Type -> Tc b (Type, Type, Type, Type)
checkSTType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type, Type)
    go (ST [] omega sigma alpha beta _) =
        return (omega, sigma, alpha, beta)

    go tau = do
        omega <- newMetaTvT OmegaK tau
        sigma <- newMetaTvT TauK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT omega sigma alpha beta)
        return (omega, sigma, alpha, beta)

-- | Check that a type is an @ST (C \nu) \sigma \alpha \beta@ type, returning
-- the four type indices
checkSTCType :: Type -> Tc b (Type, Type, Type, Type)
checkSTCType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type, Type)
    go (ST [] (C nu _) sigma alpha beta _) =
        return (nu, sigma, alpha, beta)

    go tau = do
        nu    <- newMetaTvT TauK tau
        sigma <- newMetaTvT TauK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT (cT nu) sigma alpha beta)
        return (nu, sigma, alpha, beta)

-- | Check that a type is an @ST (C ()) \sigma \alpha \beta@ type, returning the
-- three type indices
checkSTCUnitType :: Type -> Tc b (Type, Type, Type)
checkSTCUnitType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type)
    go (ST [] (C (UnitT _) _) sigma alpha beta _) =
        return (sigma, alpha, beta)

    go tau = do
        sigma <- newMetaTvT TauK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT (cT unitT) sigma alpha beta)
        return (sigma, alpha, beta)

-- | Check that a type is an integral type
checkIntType :: Type -> Tc b ()
checkIntType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b ()
    go (IntT _ _) = return ()
    go tau        = unifyTypes tau intT

-- | Check that a type is a numerical type
checkNumType :: Type -> Tc b ()
checkNumType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b ()
    go (IntT _ _)     = return ()
    go (FloatT _ _)   = return ()
    go (ComplexT _ _) = return ()
    go tau            = unifyTypes tau intT

mkStCT :: Type -> Tc b Type
mkStCT tau = do
    sigma <- newMetaTvT TauK l
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    return $ ST [] (C tau l) sigma alpha beta l
  where
    l :: SrcLoc
    l = srclocOf tau

-- | Implement the join operation for types of kind omega
joinOmega :: Type -> Type -> Tc b Type
joinOmega tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Tc b Type
    go tau1@(C {}) (T {})      = return tau1
    go (T {})      tau2@(C {}) = return tau2
    go tau1@(T {}) (T {})      = return tau1

    go tau1 tau2 =
        faildoc $ text "Cannot join" <+> ppr tau1 <+> text "and" <+> ppr tau2

instType :: Type -> Expected Type -> Tc b ()
instType tau1 (Infer ref)  = writeRef ref tau1
instType tau1 (Check tau2) = unifyTypes tau1 tau2

-- | Throw a "Expected type.." error. @tau1@ is the type we got, and @tau2@ is
-- the expected type.
expectedTypeErr :: Type -> Type -> Tc b a
expectedTypeErr tau1 tau2 = do
    [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
    faildoc $
      text "Expected type:" <+> ppr tau2' </>
      text "but got:      " <+> ppr tau1'

-- | Unify two types. The first argument is what we got, and the second is what
-- we expect.
unifyTypes :: Type -> Type -> Tc b ()
unifyTypes tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    unify tau1' tau2'
  where
    unify :: Type -> Type -> Tc b ()
    unify tau1 tau2 = do
        tau1' <- compress tau1
        tau2' <- compress tau2
        go tau1' tau2'

    go :: Type -> Type -> Tc b ()
    go (MetaT mtv1 _) (MetaT mtv2 _) | mtv1 == mtv2 =
        return ()

    go tau1@(MetaT mtv _) tau2 =
        updateMetaTv mtv tau1 tau2

    go tau1 tau2@(MetaT mtv _) =
        updateMetaTv mtv tau2 tau1

    go (UnitT {})      (UnitT {})                 = return ()
    go (BoolT {})      (BoolT {})                 = return ()
    go (BitT {})       (BitT {})                  = return ()
    go (IntT w1 _)     (IntT w2 _)     | w1 == w2 = return ()
    go (FloatT w1 _)   (FloatT w2 _)   | w1 == w2 = return ()
    go (ComplexT w1 _) (ComplexT w2 _) | w1 == w2 = return ()
    go (StringT {})    (StringT {})               = return ()

    go (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    go (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify tau1a tau1b
        unify tau2a tau2b

    go (C tau1 _) (C tau2 _) =
        unify tau1 tau2

    go (T {}) (T {}) =
        unify tau1 tau2

    go (ST alphas_a omega_a tau_1a tau_2a tau_3a _)
       (ST alphas_b omega_b tau_1b tau_2b tau_3b _) | alphas_a == alphas_b = do
        unify omega_a omega_b
        unify tau_1a tau_1b
        unify tau_2a tau_2b
        unify tau_3a tau_3b

    go (RefT tau1 _) (RefT tau2 _) =
        unify tau1 tau2

    go (FunT iotas1 taus1 tau1 _) (FunT iotas2 taus2 tau2 _)
        | length taus1 == length taus2 && iotas1 == iotas2 = do
        zipWithM_ unify taus1 taus2
        unify tau1 tau2

    go (ConstI i1 _) (ConstI i2 _)  | i1 == i2 =
        return ()

    go (VarI v1 _) (VarI v2 _)  | v1 == v2 =
        return ()

    go (TyVarT tv1 _) (TyVarT tv2 _) | tv1 == tv2 =
        return ()

    go tau1 tau2 =
        expectedTypeErr tau1 tau2

    updateMetaTv :: MetaTv -> Type -> Type -> Tc b ()
    updateMetaTv mtv tau1 tau2 = do
        mtvs2 <- metaTvs [tau2]
        when (mtv `elem` mtvs2) $ do
            [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
            faildoc $ nest 2 $
              text "Cannot construct the infinite type:" <+/>
              ppr tau1' <+> text "=" <+> ppr tau2'
        kcWriteTv mtv tau2

traceVar :: Z.Var -> Type -> Tc b ()
traceVar v tau = do
    [tau'] <- sanitizeTypes [tau]
    traceTc $ text "Variable" <+> ppr v <+> colon <+> ppr tau'

class FromZ a b | a -> b where
    fromZ :: a -> Tc c b

instance FromZ Z.W W where
    fromZ Z.W8  = pure W8
    fromZ Z.W16 = pure W16
    fromZ Z.W32 = pure W32
    fromZ Z.W64 = pure W64

instance FromZ Z.Type Type where
    fromZ (Z.UnitT l)      = pure $ UnitT l
    fromZ (Z.BoolT l)      = pure $ BoolT l
    fromZ (Z.BitT l)       = pure $ BitT l
    fromZ (Z.IntT w l)     = IntT <$> fromZ w <*> pure l
    fromZ (Z.FloatT w l)   = FloatT <$> fromZ w <*> pure l
    fromZ (Z.ComplexT w l) = ComplexT <$> fromZ w <*> pure l
    fromZ (Z.ArrT i tau l) = ArrT <$> fromZ i <*> fromZ tau <*> pure l
    fromZ (Z.StructT s l)  = StructT <$> fromZ s <*> pure l
    fromZ (Z.C tau l)      = C <$> fromZ tau <*> pure l
    fromZ (Z.T l)          = T <$> pure l

    fromZ (Z.ST omega tau1 tau2 l) =
        ST <$> pure [] <*> fromZ omega <*> newMetaTvT TauK l <*>
           fromZ tau1 <*> fromZ tau2 <*> pure l

instance FromZ (Maybe Z.Type, Kind) Type where
    fromZ (Just tau, _)    = fromZ tau
    fromZ (Nothing, kappa) = newMetaTvT kappa NoLoc

instance FromZ Z.Ind Type where
    fromZ (Z.ConstI i l) =
        pure $ ConstI i l

    fromZ (Z.ArrI v _) =
        lookupVar v >>= checkArrInd

    fromZ (Z.NoneI l) =
        newMetaTvT IotaK l

instance FromZ Z.Struct Struct where
    fromZ (Z.Struct n) = pure $ Struct n

instance FromZ Z.VarBind (Z.Var, Type) where
    fromZ (Z.VarBind v False ztau) = do
          tau <- fromZ ztau
          return (v, tau)

    fromZ (Z.VarBind v True ztau) = do
          tau <- refT <$> fromZ ztau
          return (v, tau)

class Trans a b | b -> a where
    trans :: a -> Tc c b

instance Trans Z.Var C.Var where
    trans (Z.Var n) = pure $ C.Var n

instance Trans TyVar C.TyVar where
    trans (TyVar n) = pure $ C.TyVar n

instance Trans IVar C.IVar where
    trans (IVar n) = pure $ C.IVar n

instance Trans W C.W where
    trans W8  = pure C.W8
    trans W16 = pure C.W16
    trans W32 = pure C.W32
    trans W64 = pure C.W64

instance Trans Type C.Type where
    trans tau = compress tau >>= go
      where
        go :: Type -> Tc b C.Type
        go (UnitT l)      = C.UnitT <$> pure l
        go (BoolT l)      = C.BoolT <$> pure l
        go (BitT l)       = C.BitT <$> pure l
        go (IntT w l)     = C.IntT <$> trans w <*> pure l
        go (FloatT w l)   = C.FloatT <$> trans w <*> pure l
        go (ComplexT w l) = C.ComplexT <$> trans w <*> pure l
        go (StringT l)    = pure $ C.StringT l
        go (RefT tau l)   = C.RefT <$> go tau <*> pure l
        go (ArrT i tau l) = C.ArrT <$> trans i <*> go tau <*> pure l

        go (ST alphas omega tau1 tau2 tau3 l) =
            C.ST <$> mapM trans alphas <*>  trans omega <*>
             go tau1 <*> go tau2 <*> go tau3 <*> pure l

        go (FunT iotas taus tau l) =
            C.FunT <$> mapM trans iotas <*> mapM go taus <*> go tau <*> pure l

        go (TyVarT alpha l) =
            C.TyVarT <$> trans alpha <*> pure l

        go tau =
            faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core type"

instance Trans Type C.Omega where
    trans (C omega _) = C.C <$> trans omega
    trans (T _)       = pure C.T
    trans tau         = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core omega"

instance Trans Type C.Iota where
    trans (ConstI i l)      = pure $ C.ConstI i l
    trans (VarI (IVar n) l) = pure $ C.VarI (C.IVar n) l
    trans tau               = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core iota"

instance Trans (Z.Var, Type) C.VarBind where
    trans (v, tau) = C.VarBind <$> trans v <*> trans tau
