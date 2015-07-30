{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Loc
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

checkLet :: Z.Var -> Maybe Z.Type -> Z.Exp
         -> Tc b (Type, Tc c C.Exp)
checkLet v ztau e = do
    tau <- fromZ ztau
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

checkLetFun :: Z.Var -> Maybe Z.Type -> [Z.VarBind] -> Z.Exp
            -> Tc b (Type, [(Z.Var, Type)], Tc c C.Exp)
checkLetFun f ztau ps e = do
    tau   <- fromZ ztau
    ptaus <- mapM fromZ ps
    extendVars ((f,tau) : ptaus) $ do
    (tau_ret, mce1) <- inferExp e
    unifyTypes (funT (map snd ptaus) tau_ret) tau
    return (tau, ptaus, mce1)

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
                   checkLet v ztau e
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
    (tau, ptaus, mce1) <- withSummaryContext cl $
                          checkLetFun f ztau ps e
    mce2               <- extendVars ((f,tau) : ptaus) $
                          k
    return $ do cf     <- trans f
                cptaus <- mapM trans ptaus
                ctau   <- trans tau
                ce1    <- mce1
                ce2    <- mce2
                return $ C.LetFunE cf [] cptaus ctau ce1 ce2 l

checkCompLet cl@(Z.LetCompCL v ztau _ e l) k = do
    (tau, mce1) <- withSummaryContext cl $
                   checkLet v ztau e
    mce2        <- extendVars [(v, tau)] $ k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

checkCompLet cl@(Z.LetFunCompCL f ztau _ ps e l) k = do
    (tau, ptaus, mce1) <- withSummaryContext cl $
                          checkLetFun f ztau ps e
    mce2               <- extendVars ((f,tau) : ptaus) $
                          k
    return $ do cf     <- trans f
                cptaus <- mapM trans ptaus
                ctau   <- trans tau
                ce1    <- mce1
                ce2    <- mce2
                return $ C.LetFunE cf [] cptaus ctau ce1 ce2 l

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
    tau    <- lookupVar v >>= compress
    checkVarE isRval tau
  where
    checkVarE :: Bool -> Type -> Tc b (Tc c C.Exp)
    -- If we are in an r-value context, we need to generate code that
    -- dereferences the variable and return the dereferenced value.
    checkVarE True (RefT tau _) = do
        instType tau exp_ty
        return $ do cv <- trans v
                    derefRvalueE $ C.VarE cv l

    checkVarE _ tau = do
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
    mce2 <- tcExp e2 exp_ty
    mce3 <- tcExp e3 exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                ce3 <- mce3
                return $ C.IfE ce1 ce2 ce3 l

tcExp (Z.LetE v ztau e1 e2 l) exp_ty = do
    (tau, mce1) <- checkLet v ztau e1
    mce2        <- extendVars [(v, tau)] $
                   tcExp e2 exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

tcExp (Z.CallE v es l) exp_ty = do
    (taus, tau) <- lookupVar v >>= checkFunType (length es)
    mces        <- zipWithM checkArg es taus
    instType tau exp_ty
    return $ collectRvalCtx $ do
             cv  <- trans v
             ces <- sequence mces
             return $ C.CallE cv [] ces l
  where
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
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (ST (C (UnitT l) l) alpha beta l) exp_ty
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
    tau_i <- fromZ ztau_i
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
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (ST (C (UnitT l) l) alpha beta l) exp_ty
    return $ do ces <- sequence mces
                return $ C.PrintE newline ces l
  where
    checkArg :: Z.Exp -> Tc b (Tc c C.Exp)
    checkArg e = do
        (_, mce) <- inferExp e
        return mce

tcExp (Z.ReturnE _ e l) exp_ty = do
    (nu, mce) <- inferExp e
    alpha     <- newMetaTvT TauK l
    beta      <- newMetaTvT TauK l
    instType (ST (C nu l) alpha beta l) exp_ty
    return $ do ce <- mce
                return $ C.ReturnE ce l

tcExp (Z.TakeE l) exp_ty = do
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (ST (C alpha l) alpha beta l) exp_ty
    return $ return $ C.TakeE l

tcExp (Z.TakesE i l) exp_ty = do
    alpha <- newMetaTvT TauK l
    beta  <- newMetaTvT TauK l
    instType (ST (C (ArrT (ConstI i l) alpha l) l) alpha beta l) exp_ty
    return $ return $ C.TakesE (fromIntegral i) l

tcExp (Z.EmitE e l) exp_ty = do
    alpha       <- newMetaTvT TauK l
    (beta, mce) <- inferExp e
    instType (ST (C (UnitT l) l) alpha beta l) exp_ty
    return $ do ce <- mce
                return $ C.EmitE ce l

tcExp (Z.RepeatE _ e l) exp_ty = do
    (alpha, beta, mce) <- withSummaryContext e $ do
                          (tau, mce)    <- inferExp e
                          (alpha, beta) <- checkSTCUnitType tau
                          return (alpha, beta, mce)
    instType (ST (T l) alpha beta l) exp_ty
    return $ do ce <- mce
                return $ C.RepeatE ce l

tcExp (Z.ArrE _ e1 e2 l) tau_exp = do
    (omega1, alpha, beta, mce1) <-
        withSummaryContext e1 $ do
        (tau_e1, mce1)        <- inferExp e1
        (omega1, alpha, beta) <- checkSTType tau_e1
        return (omega1, alpha, beta, mce1)
    (omega2, mce2) <-
        withSummaryContext e2 $ do
        omega2 <- newMetaTvT OmegaK e2
        mce2   <- checkExp e2 (stT omega2 alpha beta)
        return (omega2, mce2)
    omega       <- joinOmega omega1 omega2
    common_refs <- filterM isRefVar (Set.toList common_fvs)
    when (not (null common_refs)) $
        faildoc $ text "Branches of arrow expression share mutable state:" <+>
                  commasep (map ppr common_refs)
    instType (stT omega alpha beta) tau_exp
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.ArrE ce1 ce2 l
  where
    common_fvs :: Set Z.Var
    common_fvs = fvs e1 `Set.intersection` fvs e2

tcExp (Z.ReadE ztau l) exp_tau = do
    alpha <- fromZ ztau
    beta  <- newMetaTvT TauK ztau
    instType (ST (T l) alpha beta l) exp_tau
    return $ do cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.varE cx)

tcExp (Z.WriteE ztau l) exp_tau = do
    alpha <- newMetaTvT TauK ztau
    beta  <- fromZ ztau
    instType (ST (T l) alpha beta l) exp_tau
    return $ do cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.varE cx)

tcExp (Z.StandaloneE e _) exp_tau =
    tcExp e exp_tau

tcExp (Z.MapE _ v ztau l) exp_tau = do
    tau  <- fromZ ztau
    tau' <- lookupVar v
    unifyTypes tau' tau
    (alpha, beta) <- checkFunType tau
    instType (ST (T l) alpha beta l) exp_tau
    return $ do cv <- trans v
                cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.callE cv [C.varE cx])
  where
    checkFunType :: Type -> Tc b (Type, Type)
    checkFunType tau =
        compress tau >>= go
      where
        go :: Type -> Tc b (Type, Type)
        go (FunT [] [alpha] (ST (C beta _) alpha' beta' _) _) = do
            unifyTypes alpha' alpha
            unifyTypes beta'  beta
            return (alpha, beta)

        go tau = do
            alpha <- newMetaTvT TauK tau
            beta  <- newMetaTvT TauK tau
            unifyTypes tau (FunT [] [alpha] (ST (C beta l) alpha beta l) l)
            return (alpha, beta)

tcExp (Z.CompLetE cl e _) exp_tau =
    checkCompLet cl $
    tcExp e exp_tau

tcExp (Z.StmE stms _) exp_tau =
    tcStms stms exp_tau

tcExp (Z.CmdE cmds _) exp_tau =
    tcCmds cmds exp_tau

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
                   checkLet v ztau e
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
                ctau <- trans (refT tau)
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
    (tau1, mce1)     <- inferExp e
    (_, alpha, beta) <- checkSTCType tau1
    omega            <- newMetaTvT OmegaK e
    let tau          =  stT omega alpha beta
    instType tau exp_ty
    mce2 <- tcStms stms exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcStms [] _ =
    panicdoc $ text "Empty statement sequence!"

tcCmds :: [Z.Cmd] -> Expected Type -> Tc b (Tc c C.Exp)
tcCmds (cmd@(Z.LetC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (Z.LetC cl _ : cmds) exp_tau =
    checkCompLet cl $ tcCmds cmds exp_tau

tcCmds (cmd@(Z.BindC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (cmd@(Z.BindC v ztau e l) : cmds) exp_tau = do
    (nu, mce1) <- withSummaryContext cmd $ do
                  (tau, mce1)       <- checkLet v ztau e
                  (nu, alpha, beta) <- checkSTCType tau
                  omega             <- newMetaTvT OmegaK l
                  instType (ST omega alpha beta l) exp_tau
                  return (nu, mce1)
    mce2       <- extendVars [(v, nu)] $
                  tcCmds cmds exp_tau
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
    (tau1, mce1)     <- inferExp e
    (_, alpha, beta) <- checkSTCType tau1
    omega            <- newMetaTvT OmegaK e
    let tau          =  stT omega alpha beta
    instType tau exp_ty
    mce2 <- tcCmds cmds exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcCmds [] _ =
    panicdoc $ text "Empty command sequence!"

-- | Return 'True' if @v@ has a reference type, 'False' otherwise
isRefVar :: Z.Var -> Tc b Bool
isRefVar v = do
    tau <- lookupVar v >>= compress
    case tau of
      RefT {} -> return True
      _       -> return False

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

checkFunType :: Int -> Type -> Tc b ([Type], Type)
checkFunType nargs tau =
    compress tau >>= go
  where
    go :: Type -> Tc b ([Type], Type)
    go (FunT [] taus tau _) = do
        when (length taus /= nargs) $
            faildoc $
              text "Expected" <+> ppr nargs <+>
              text "arguments but got" <+> ppr (length taus)
        return (taus, tau)

    go tau_f = do
        taus <- replicateM nargs (newMetaTvT TauK tau)
        tau  <- newMetaTvT TauK tau
        unifyTypes tau_f (funT taus tau)
        return (taus, tau)

-- | Check that a type is an @ST \omega \alpha \beta@ type, returning the three type indices
checkSTType :: Type -> Tc b (Type, Type, Type)
checkSTType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type)
    go (ST omega alpha beta _) =
        return (omega, alpha, beta)

    go tau = do
        omega <- newMetaTvT OmegaK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT omega alpha beta)
        return (omega, alpha, beta)

-- | Check that a type is an @ST (C \nu) \alpha \beta@ type, returning the three type indices
checkSTCType :: Type -> Tc b (Type, Type, Type)
checkSTCType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type)
    go (ST (C nu _) alpha beta _) =
        return (nu, alpha, beta)

    go tau = do
        nu    <- newMetaTvT TauK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT (cT nu) alpha beta)
        return (nu, alpha, beta)

-- | Check that a type is an @ST (C ()) \alpha \beta@ type, returning the two type indices
checkSTCUnitType :: Type -> Tc b (Type, Type)
checkSTCUnitType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type)
    go (ST (C (UnitT _) _) alpha beta _) =
        return (alpha, beta)

    go tau = do
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT (cT unitT) alpha beta)
        return (alpha, beta)

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
instType tau  (Infer ref)  = writeRef ref tau
instType tau1 (Check tau2) = unifyTypes tau1 tau2

-- | Unify two types. The first argument is what we got, and the second is what
-- we expect.
unifyTypes :: Type -> Type -> Tc b ()
unifyTypes tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    unify tau1' tau2'
  where
    unify :: Type -> Type -> Tc b ()
    unify tau1@(MetaT mtv _) tau2 =
        updateMetaTv mtv tau1 tau2

    unify tau1 tau2@(MetaT mtv _) =
        updateMetaTv mtv tau2 tau1

    unify (UnitT {})      (UnitT {})                 = return ()
    unify (BoolT {})      (BoolT {})                 = return ()
    unify (BitT {})       (BitT {})                  = return ()
    unify (IntT w1 _)     (IntT w2 _)     | w1 == w2 = return ()
    unify (FloatT w1 _)   (FloatT w2 _)   | w1 == w2 = return ()
    unify (ComplexT w1 _) (ComplexT w2 _) | w1 == w2 = return ()
    unify (StringT {})    (StringT {})               = return ()

    unify (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    unify (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify tau1a tau1b
        unify tau2a tau2b

    unify (C tau1 _) (C tau2 _) =
        unify tau1 tau2

    unify (T {}) (T {}) =
        unify tau1 tau2

    unify (ST tau1a tau2a tau3a _) (ST tau1b tau2b tau3b _) = do
        unify tau1a tau1b
        unify tau2a tau2b
        unify tau3a tau3b

    unify (RefT tau1 _) (RefT tau2 _) =
        unify tau1 tau2

    unify (FunT iotas1 taus1 tau1 _) (FunT iotas2 taus2 tau2 _)
        | length taus1 == length taus2 && length iotas1 == length iotas2 = do
        zipWithM_ unify iotas1 iotas2
        zipWithM_ unify taus1 taus2
        unify tau1 tau2

    unify (ConstI i1 _) (ConstI i2 _)  | i1 == i2 =
        return ()

    unify (VarI v1 _) (VarI v2 _)  | v1 == v2 =
        return ()

    unify (TyVarT tv1 _) (TyVarT tv2 _) | tv1 == tv2 =
        return ()

    unify tau1 tau2 = do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        faildoc $
          text "Expected type:" <+> ppr tau2' </>
          text "but got:      " <+> ppr tau1'

    updateMetaTv :: MetaTv -> Type -> Type -> Tc b ()
    updateMetaTv mtv tau1 tau2 = do
        mtvs2 <- metaTvs [tau2]
        when (mtv `elem` mtvs2) $ do
            [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
            faildoc $ nest 2 $
              text "Cannot construct the infinite type:" <+/>
              ppr tau1' <+> text "=" <+> ppr tau2'
        writeTv mtv tau2

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
    fromZ (Z.ST tau1 tau2 tau3 l) = ST <$> fromZ tau1 <*> fromZ tau2 <*> fromZ tau3 <*> pure l

instance FromZ (Maybe Z.Type) Type where
    fromZ (Just tau) = fromZ tau
    fromZ Nothing    = newMetaTvT TauK NoLoc

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

instance Trans W C.W where
    trans W8  = pure C.W8
    trans W16 = pure C.W16
    trans W32 = pure C.W32
    trans W64 = pure C.W64

instance Trans Type C.Type where
    trans tau = compress tau >>= go
      where
        go :: Type -> Tc b C.Type
        go (UnitT l)               = C.UnitT <$> pure l
        go (BoolT l)               = C.BoolT <$> pure l
        go (BitT l)                = C.BitT <$> pure l
        go (IntT w l)              = C.IntT <$> trans w <*> pure l
        go (FloatT w l)            = C.FloatT <$> trans w <*> pure l
        go (ComplexT w l)          = C.ComplexT <$> trans w <*> pure l
        go (StringT l)             = pure $ C.StringT l
        go (RefT tau l)            = C.RefT <$> go tau <*> pure l
        go (ArrT i tau l)          = C.ArrT <$> trans i <*> go tau <*> pure l
        go (ST tau1 tau2 tau3 l)   = C.ST <$> trans tau1 <*> go tau2 <*> go tau3 <*> pure l
        go (FunT iotas taus tau l) = C.FunT <$> mapM trans iotas <*> mapM go taus <*> go tau <*> pure l
        go tau                     = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core type"

instance Trans Type C.Omega where
    trans (C omega _) = C.C <$> trans omega
    trans (T _)       = pure C.T
    trans tau         = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core omega"

instance Trans Type C.Iota where
    trans (ConstI i l)      = pure $ C.ConstI i l
    trans (VarI (IVar n) l) = pure $ C.VarI (C.IVar n) l
    trans tau               = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core iota"

instance Trans Type C.IVar where
    trans (VarI (IVar n) _) = pure $ C.IVar n
    trans tau               = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core IVar"

instance Trans (Z.Var, Type) C.VarBind where
    trans (v, tau) = C.VarBind <$> trans v <*> trans tau
