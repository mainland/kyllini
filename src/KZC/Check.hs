{-# LANGUAGE DeriveDataTypeable #-}
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
    withTi,

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
import Control.Monad.Exception
import Control.Monad.Ref
import Data.IORef
import Data.List (sort)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
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

type Co = Ti C.Exp -> Ti C.Exp

data Expected a = Infer (IORef a)
                | Check a
  deriving (Show)

readExpected :: MonadRef IORef m => Expected a -> m a
readExpected (Infer r)   = readRef r
readExpected (Check tau) = return tau

checkProgram :: [Z.CompLet] -> Ti C.Exp
checkProgram cls = do
    mce <- go cls
    mce
  where
    go :: [Z.CompLet] -> Ti (Ti C.Exp)
    go []       = return $ return $ C.varE (C.mkVar "main")
    go (cl:cls) = checkCompLet cl $ go cls

checkLet :: Z.Var -> Maybe Z.Type -> Kind -> Z.Exp
         -> Ti (Type, Ti C.Exp)
checkLet v ztau TauK e =
    withExpContext e $ do
    tau <- fromZ (ztau, TauK)
    extendVars [(v, tau)] $ do
    mce1 <- castVal tau e
    return (tau, mce1)

checkLet f ztau kappa e =
    withExpContext e $ do
    tau <- fromZ (ztau, kappa)
    mce <- extendVars [(f, tau)] $
           collectValCtx tau $
           checkExp e tau
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    return (tau_gen, co mce)

checkLetRef :: Z.Var -> Z.Type -> Maybe Z.Exp
            -> Ti (Type, Ti (Maybe C.Exp))
checkLetRef v ztau e_init =
    withMaybeExpContext e_init $ do
    tau <- fromZ ztau
    extendVars [(v, refT tau)] $ do
    mce1 <- case e_init of
              Nothing -> return $ return Nothing
              Just e  -> do mce <- castVal tau e
                            return $ Just <$> mce
    return (tau, mce1)
  where
    withMaybeExpContext :: Maybe Z.Exp -> Ti a -> Ti a
    withMaybeExpContext Nothing  m = m
    withMaybeExpContext (Just e) m = withExpContext e m

checkLetFun :: Z.Var -> Maybe Z.Type -> [Z.VarBind] -> Z.Exp -> SrcLoc
            -> Ti (Type, Ti C.Exp -> Ti C.Exp)
checkLetFun f ztau ps e l = do
    tau   <- fromZ (ztau, PhiK)
    ptaus <- fromZ ps
    (tau_ret, mce1) <-
        extendVars ((f,tau) : ptaus) $ do
        tau_ret           <- newMetaTvT MuK l
        mce1              <- collectValCtx tau_ret $
                             checkExp e tau_ret
        (tau_ret_gen, co) <- generalize tau_ret
        unifyTypes (funT (map snd ptaus) tau_ret_gen) tau
        return (tau_ret_gen, co mce1)
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    let mkLetFun mce2 = co $ do
        cf       <- trans f
        cptaus   <- mapM trans ptaus
        ctau_ret <- trans tau_ret
        ce1      <- withSummaryContext e $ mce1
        ce2      <- mce2
        return $ C.LetFunE cf [] cptaus ctau_ret ce1 ce2 l
    return (tau_gen, mkLetFun)

checkLetExtFun :: Z.Var -> [Z.VarBind] -> Z.Type -> SrcLoc
               -> Ti (Type, Ti C.Exp -> Ti C.Exp)
checkLetExtFun f ps ztau_ret l = do
    ptaus        <- fromZ ps
    -- Note that the output type may depend on the parameters because of array
    -- lengths
    tau_ret       <- extendVars ptaus $
                     checkRetType ztau_ret
    let tau       =  funT (map snd ptaus) tau_ret
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    let mkLetExtFun mce2 = co $ do
        cf       <- trans f
        cptaus   <- mapM trans ptaus
        ctau_ret <- trans tau_ret
        ce2      <- mce2
        return $ C.LetExtFunE cf [] cptaus ctau_ret ce2 l
    return (tau_gen, mkLetExtFun)
  where
    checkRetType :: Z.Type -> Ti Type
    checkRetType (Z.UnitT {}) = do
        s <- newMetaTvT TauK l
        a <- newMetaTvT TauK l
        b <- newMetaTvT TauK l
        fst <$> generalize (ST [] (C (UnitT l) l) s a b l)

    checkRetType ztau = fromZ ztau

checkCompLet :: Z.CompLet
             -> Ti (Ti C.Exp)
             -> Ti (Ti C.Exp)
checkCompLet cl@(Z.LetCL v ztau e l) k = do
    tau_ret <- newMetaTvT MuK l
    collectValCtx tau_ret $ do
    (tau, mce1) <- withSummaryContext cl $ do
                   checkLet v ztau TauK e
    mce2        <- extendVars [(v, tau)] $
                   k
    return $ withSummaryContext cl $ do
        cv   <- trans v
        ctau <- trans tau
        ce1  <- withSummaryContext cl $ mce1
        ce2  <- mce2
        return $ C.LetE cv ctau ce1 ce2 l

checkCompLet cl@(Z.LetRefCL v ztau e_init l) k = do
    (tau, mce1) <- withSummaryContext cl $
                   checkLetRef v ztau e_init
    mce2        <- extendVars [(v, refT tau)] $
                   k
    return $ withSummaryContext cl $ do
        cv   <- trans v
        ctau <- trans tau
        ce1  <- withSummaryContext cl $ mce1
        ce2  <- mce2
        return $ C.LetRefE cv ctau ce1 ce2 l

checkCompLet cl@(Z.LetFunCL f ztau ps e l) k = do
    (tau, mkLetFun) <- withSummaryContext cl $
                       checkLetFun f ztau ps e l
    mce2            <- extendVars [(f,tau)] $
                       k
    return $ withSummaryContext cl $
             mkLetFun mce2

checkCompLet cl@(Z.LetFunExternalCL f ps ztau_ret l) k = do
    (tau, mkLetExtFun) <- withSummaryContext cl $
                          checkLetExtFun f ps ztau_ret l
    mce2               <- extendVars [(f,tau)] $
                          k
    return $ withSummaryContext cl $
             mkLetExtFun mce2

checkCompLet cl@(Z.LetStructCL (Z.StructDef zs zflds l1) l2) k = do
    (taus, mkLetStruct) <-
        withSummaryContext cl $ do
        checkStructNotRedefined zs
        checkDuplicates "field names" zfnames
        taus <- mapM fromZ ztaus
        mapM_ (\tau -> checkKind tau TauK) taus
        let mkLetStruct ce = do
            cs      <- trans zs
            cfnames <- mapM trans zfnames
            ctaus   <- mapM trans taus
            return $ C.LetStruct cs (cfnames `zip` ctaus) ce l2
        return (taus, mkLetStruct)
    mce <- extendStructs [StructDef zs (zfnames `zip` taus) l1] $
           k
    return $ withSummaryContext cl $ do
        ce <- mce
        mkLetStruct ce
  where
    (zfnames, ztaus) = unzip zflds

    checkStructNotRedefined :: Z.Struct -> Ti ()
    checkStructNotRedefined s = do
      maybe_sdef <- maybeLookupStruct zs
      case maybe_sdef of
        Nothing   -> return ()
        Just sdef -> faildoc $ text "Struct" <+> ppr s <+> text "redefined" <+>
                     parens (text "original definition at" <+> ppr (locOf sdef))

checkCompLet cl@(Z.LetCompCL v ztau _ e l) k = do
    (tau, mce1) <- withSummaryContext cl $
                   checkLet v ztau MuK e
    mce2        <- extendVars [(v, tau)] $ k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- withSummaryContext cl $ mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

checkCompLet cl@(Z.LetFunCompCL f ztau _ ps e l) k = do
    (tau, mkLetFun) <- withSummaryContext cl $
                       checkLetFun f ztau ps e l
    mce2            <- extendVars [(f,tau)] $
                       k
    return $ withSummaryContext cl $
             mkLetFun mce2

tcExp :: Z.Exp -> Expected Type -> Ti (Ti C.Exp)
tcExp (Z.ConstE zc l) exp_ty = do
    cc <- tcConst zc
    return $ return $ C.ConstE cc l
  where
    tcConst :: Z.Const -> Ti C.Const
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

    tcConst(Z.StringC s)  = do
        instType (StringT l) exp_ty
        return $ C.StringC s

tcExp (Z.VarE v _) exp_ty = do
    (tau, co) <- lookupVar v >>= instantiate
    instType tau exp_ty
    return $ co $ C.varE <$> trans v

tcExp (Z.UnopE op e1 l) exp_ty = do
    (tau1, mce1) <- inferVal e1
    (tau, mcop)  <- unop op tau1
    instType tau exp_ty
    return $ do ce1 <- mce1
                cop <- mcop
                return $ C.UnopE cop ce1 l
  where
    unop :: Z.Unop -> Type -> Ti (Type, Ti C.Unop)
    unop Z.Lnot tau = do
        checkBoolT tau
        return (tau, return C.Lnot)

    unop Z.Bnot tau = do
        checkBitT tau
        return (tau, return C.Bnot)

    unop Z.Neg tau = do
        checkSignedNumT tau
        return (tau, return C.Neg)

    unop (Z.Cast ztau2) tau1 = do
        tau2 <- fromZ ztau2
        checkCast tau1 tau2
        let mcop = do ctau2 <- trans tau2
                      return $ C.Cast ctau2
        return (tau2, mcop)

    unop Z.Len tau = do
        _ <- checkArrT tau
        return (intT, return C.Len)

tcExp (Z.BinopE op e1 e2 l) exp_ty =
    binop op
  where
    binop :: Z.Binop -> Ti (Ti C.Exp)
    binop Z.Lt   = checkOrdBinop C.Lt
    binop Z.Le   = checkOrdBinop C.Le
    binop Z.Eq   = checkEqBinop C.Eq
    binop Z.Ge   = checkOrdBinop C.Ge
    binop Z.Gt   = checkOrdBinop C.Gt
    binop Z.Ne   = checkEqBinop C.Ne
    binop Z.Land = checkBoolBinop C.Land
    binop Z.Lor  = checkBoolBinop C.Lor
    binop Z.Band = checkBitBinop C.Band
    binop Z.Bor  = checkBitBinop C.Bor
    binop Z.Bxor = checkBitBinop C.Bxor
    binop Z.LshL = checkBitShiftBinop C.LshL
    binop Z.LshR = checkBitShiftBinop C.LshR
    binop Z.AshR = checkBitShiftBinop C.AshR
    binop Z.Add  = checkNumBinop C.Add
    binop Z.Sub  = checkNumBinop C.Sub
    binop Z.Mul  = checkNumBinop C.Mul
    binop Z.Div  = checkNumBinop C.Div
    binop Z.Rem  = checkNumBinop C.Rem
    binop Z.Pow  = checkNumBinop C.Pow

    checkEqBinop :: C.Binop -> Ti (Ti C.Exp)
    checkEqBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkEqT tau
        instType boolT exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkOrdBinop :: C.Binop -> Ti (Ti C.Exp)
    checkOrdBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkOrdT tau
        instType boolT exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBoolBinop :: C.Binop -> Ti (Ti C.Exp)
    checkBoolBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkBoolT tau
        instType tau exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkNumBinop :: C.Binop -> Ti (Ti C.Exp)
    checkNumBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkNumT tau
        instType tau exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBitBinop :: C.Binop -> Ti (Ti C.Exp)
    checkBitBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkBitT tau
        instType tau exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBitShiftBinop :: C.Binop -> Ti (Ti C.Exp)
    checkBitShiftBinop cop = do
        (tau1, mce1) <- inferVal e1
        (tau2, mce2) <- inferVal e2
        checkBitT tau1
        checkIntT tau2
        instType tau1 exp_ty
        return $ C.BinopE cop <$> mce1 <*> mce2 <*> pure l

tcExp (Z.IfE e1 e2 Nothing l) exp_ty = do
    mce1        <- checkVal e1 (BoolT l)
    (tau, mce2) <- inferExp e2
    checkSTCUnit tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.IfE ce1 ce2 (C.returnE C.unitE) l

tcExp (Z.IfE e1 e2 (Just e3) l) exp_ty = do
    mce1              <- checkVal e1 (BoolT l)
    (tau, mce2, mce3) <- unifyExpTypes e2 e3
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                ce3 <- mce3
                return $ C.IfE ce1 ce2 ce3 l

tcExp (Z.LetE v ztau e1 e2 l) exp_ty = do
    (tau, mce1) <- checkLet v ztau TauK e1
    mce2        <- withExpContext e2 $
                   extendVars [(v, tau)] $ do
                   tcExp e2 exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

tcExp (Z.CallE f es l) exp_ty = do
    (taus, tau_ret, co1) <- lookupVar f >>= checkFunT f nargs
    when (length taus /= nargs) $
        faildoc $
          text "Expected" <+> ppr nargs <+>
          text "arguments but got" <+> ppr (length taus)
    (tau_ret', co2) <- instantiate tau_ret
    instType tau_ret' exp_ty
    collectValCtx tau_ret' $ do
    mces <- zipWithM checkArg es taus
    return $ co2 $ co1 $ do
        cf  <- C.varE <$> trans f
        ces <- sequence mces
        return $ C.CallE cf [] ces l
  where
    nargs :: Int
    nargs = length es

    -- If a parameter is a ref type, then we do not want to implicitly
    -- dereference the corresponding argument, since it should be passed by
    -- reference. Similarly, if a parameter is an ST type, we do not want to
    -- implicitly run the corresponding argument. Otherwise, we assume we are in
    -- an r-value context.
    checkArg :: Z.Exp -> Type -> Ti (Ti C.Exp)
    checkArg e tau =
        withArgContext e $
        compress tau >>= go
      where
        go :: Type -> Ti (Ti C.Exp)
        go (RefT {}) = checkExp e tau
        go (ST {})   = checkExp e tau
        go _         = castVal tau e

    withArgContext :: MonadErr m
                   => Z.Exp
                   -> m b
                   -> m b
    withArgContext e act =
        localLocContext e doc act
      where
        doc = text "In argument:" <+> ppr e

tcExp (Z.LetRefE v ztau e1 e2 l) exp_ty = do
    (tau, mce1) <- checkLetRef v ztau e1
    mce2        <- extendVars [(v, refT tau)] $
                   tcExp e2 exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetRefE cv ctau ce1 ce2 l

tcExp (Z.AssignE e1 e2 l) exp_ty = do
    (gamma, mce1) <-
        withSummaryContext e1 $ do
        (tau, mce1) <- inferExp e1
        gamma       <- checkRefT tau
        return (gamma, mce1)
    tau <- mkSTC (UnitT l)
    instType tau exp_ty
    collectValCtx tau $ do
    mce2  <- withSummaryContext e2 $
             castVal gamma e2
    return $ do
        ce1   <- mce1
        ce2   <- mce2
        return $ C.AssignE ce1 ce2 l

tcExp (Z.WhileE e1 e2 l) exp_ty = do
    tau  <- mkSTC (UnitT l)
    mce1 <- collectValCtx tau $ do
            checkBoolVal e1
    mce2 <- collectValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.WhileE ce1 ce2 l

tcExp (Z.UntilE e1 e2 l) exp_ty = do
    tau  <- mkSTC (UnitT l)
    mce1 <- collectValCtx tau $ do
            checkBoolVal e1
    mce2 <- collectValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.UntilE ce1 ce2 l

tcExp (Z.TimesE _ e1 e2 l) exp_ty = do
    (tau1, mce1) <- inferVal e1
    checkIntT tau1
    (tau, mce2) <- inferExp e2
    _           <- checkSTCUnit tau
    instType tau exp_ty
    return $ do cx  <- C.mkUniqVar "x" l
                ce1 <- mce1
                ce2 <- mce2
                return $ C.ForE cx C.intT (C.intE 1) ce1 ce2 l

tcExp (Z.ForE _ i ztau_i e1 e2 e3 l) exp_ty = do
    tau_i <- fromZ (ztau_i, TauK)
    checkIntT tau_i
    mce1 <- castVal tau_i e1
    mce2 <- castVal tau_i e2
    tau  <- mkSTC (UnitT l)
    mce3 <- extendVars [(i, tau_i)] $
            collectValCtx tau $
            checkExp e3 tau
    instType tau exp_ty
    return $ do ci     <- trans i
                ctau_i <- trans tau_i
                ce1    <- mce1
                ce2    <- mce2
                ce3    <- mce3
                return $ C.ForE ci ctau_i ce1 ce2 ce3 l

tcExp (Z.ArrayE es l) exp_ty = do
    tau  <- newMetaTvT TauK l
    instType (ArrT (ConstI (length es) l) tau l) exp_ty
    mces <- mapM (\e -> checkExp e tau) es
    return $ do ces <- sequence mces
                return $ C.ArrayE ces l

tcExp (Z.IdxE e1 e2 len l) exp_ty = do
    (tau, mce1) <- withSummaryContext e1 $
                   inferExp e1
    mce2        <- withSummaryContext e2 $ do
                   (tau2, mce2) <- inferVal e2
                   checkIntT tau2
                   return mce2
    checkIdxE tau mce1 mce2
  where
    checkIdxE :: Type
              -> Ti C.Exp
              -> Ti C.Exp
              -> Ti (Ti C.Exp)
    checkIdxE tau mce1 mce2 = do
        compress tau >>= go
      where
        go :: Type -> Ti (Ti C.Exp)
        -- Indexing into a reference to an array returns a reference to an
        -- element of the array.
        go (RefT (ArrT _ tau _) _) = do
            instType (RefT (mkArrSlice tau len) l) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ C.IdxE ce1 ce2 len l

        -- A plain old array gets indexed as one would expect.
        go (ArrT _ tau _) = do
            instType (mkArrSlice tau len) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ C.IdxE ce1 ce2 len l

        -- Otherwise we assert that the type of @e1@ should be an array type.
        go tau = do
            i     <- newMetaTvT IotaK l
            alpha <- newMetaTvT TauK l
            unifyTypes tau (ArrT i alpha l)
            compress tau >>= go

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (ConstI i l) tau l

tcExp e0@(Z.StructE s flds l) exp_ty =
    withSummaryContext e0 $ do
    StructDef _ fldDefs _ <- lookupStruct s
    checkMissingFields flds fldDefs
    checkExtraFields flds fldDefs
    (fs, mces) <- unzip <$> mapM (checkField fldDefs) flds
    instType (StructT s l) exp_ty
    return $ do cs  <- trans s
                cfs <- mapM trans fs
                ces <- sequence mces
                return $ C.StructE cs (cfs `zip` ces) l
  where
    checkField :: [(Z.Field, Type)] -> (Z.Field, Z.Exp) -> Ti (Z.Field, Ti C.Exp)
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc $ "checkField: missing field!"
               Just tau -> return tau
      mce <- castVal tau e
      return (f, mce)

    checkMissingFields :: [(Z.Field, Z.Exp)] -> [(Z.Field, Type)] -> Ti ()
    checkMissingFields flds fldDefs =
        when (not (Set.null missing)) $
          faildoc $
            text "Struct definition has missing fields:" <+>
            (commasep . map ppr . Set.toList) missing
      where
        fs, fs', missing :: Set Z.Field
        fs  = Set.fromList [f | (f,_) <- flds]
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        missing = fs Set.\\ fs'

    checkExtraFields :: [(Z.Field, Z.Exp)] -> [(Z.Field, Type)] -> Ti ()
    checkExtraFields flds fldDefs =
        when (not (Set.null extra)) $
          faildoc $
            text "Struct definition has extra fields:" <+>
            (commasep . map ppr . Set.toList) extra
      where
        fs, fs', extra :: Set Z.Field
        fs  = Set.fromList [f | (f,_) <- flds]
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        extra = fs' Set.\\ fs

tcExp (Z.ProjE e f l) exp_ty = do
    (tau, mce) <- inferExp e
    checkProjE tau mce
  where
    checkProjE :: Type
               -> Ti C.Exp
               -> Ti (Ti C.Exp)
    checkProjE tau mce = do
        compress tau >>= go
      where
        go :: Type -> Ti (Ti C.Exp)
        go (RefT tau _) = do
            sdef  <- checkStructT tau >>= lookupStruct
            tau_f <- checkStructFieldT sdef f
            instType (RefT tau_f l) exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ C.ProjE ce cf l

        go tau = do
            sdef  <- checkStructT tau >>= lookupStruct
            tau_f <- checkStructFieldT sdef f
            instType tau_f exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ C.ProjE ce cf l

tcExp (Z.PrintE newline es l) exp_ty = do
    tau <- mkSTC (UnitT l)
    instType tau exp_ty
    collectValCtx tau $ do
    mces <- mapM checkArg es
    return $ do
        ces <- sequence mces
        return $ C.PrintE newline ces l
  where
    checkArg :: Z.Exp -> Ti (Ti C.Exp)
    checkArg e = do
        (tau, mce) <- inferVal e
        checkKind tau TauK
        return mce

tcExp (Z.ErrorE s l) exp_ty = do
    tau <- mkSTC (UnitT l)
    instType tau exp_ty
    return $ do
        return $ C.ErrorE s l

tcExp (Z.ReturnE _ e l) exp_ty = do
    tau     <- newMetaTvT TauK l
    tau_ret <- mkSTC tau
    instType tau_ret exp_ty
    collectValCtx tau_ret $ do
    (tau', mce) <- inferVal e
    unifyTypes tau' tau
    return $ do
        ce <- mce
        return $ C.ReturnE ce l

tcExp (Z.TakeE l) exp_ty = do
    a <- newMetaTvT TauK l
    b <- newMetaTvT TauK l
    instType (stT (C a l) a a b) exp_ty
    return $ do ca <- trans a
                return $ C.takeE ca

tcExp (Z.TakesE i l) exp_ty = do
    a <- newMetaTvT TauK l
    b <- newMetaTvT TauK l
    instType (stT (C (ArrT (ConstI i l) a l) l) a a b) exp_ty
    return $ do ca <- trans a
                return $ C.takesE (fromIntegral i) ca

-- Some Ziria code uses @emit@ with an array argument when it should really use
-- @emits@. How do we know whether to compile this to @emit@ or @emits@ in core?
-- We use a heuristic:
--
--   1) If the output type is an array type, we compile to @emits@.
--
--   2) If either the input or output type of the stream cannot possibly be an
--      array type, i.e., it is neither an array type nor a type meta-variable,
--      we compile to @emits@ and output a warning
--
--   3) Otherwise we compile to @emit@.
--
-- Obviously, if the output type of the stream cannot be an array, we have to
-- compile to @emits@. Often the input type of the stream is known, but the
-- @emit@ we are type checking determines the output type of the stream; our
-- heuristic assumes that if the input type of the stream is not an array, the
-- output type shouldn't be either. This means that a computation that reads
-- scalars and writes arrays needs an annotation.

tcExp (Z.EmitE e l) exp_ty = do
    s       <- newMetaTvT TauK l
    a       <- newMetaTvT TauK l
    b       <- newMetaTvT TauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    collectValCtx tau $ do
    (tau_e, mce)      <- inferVal e
    ST [] _ _ a' b' _ <- compress tau
    tau_e'            <- compress tau_e
    (b_e, co)         <- go a' b' tau_e'
    unifyTypes b_e b
    return $ co mce
  where
    go :: Type -> Type -> Type -> Ti (Type, Co)
    go _ b tau@(ArrT _ _ _) | isArrT b =
        return (tau, \mce -> C.EmitE <$> mce <*> pure l)

    go a b tau0@(ArrT _ tau _) | not (couldBeArrT a) || not (couldBeArrT b) = do
        [a', b'] <- sanitizeTypes [a, b]
        warndoc $ nest 2 $
          text "emit called with argument of type" <+> ppr tau0 <+/>
          text "on a stream of type" <+>
          text "ST" <+> pprPrec appPrec1 a' <+> pprPrec appPrec1 b' <>
          text "; use emits"
        return (tau, \mce -> C.EmitsE <$> mce <*> pure l)

    go _ _ tau =
        return (tau, \mce -> C.EmitE <$> mce <*> pure l)

    isArrT :: Type -> Bool
    isArrT (ArrT {}) = True
    isArrT _         = False

    couldBeArrT :: Type -> Bool
    couldBeArrT (ArrT {})  = True
    couldBeArrT (MetaT {}) = True
    couldBeArrT _          = False

tcExp (Z.EmitsE e l) exp_ty = do
    iota    <- newMetaTvT IotaK l
    s       <- newMetaTvT TauK l
    a       <- newMetaTvT TauK l
    b       <- newMetaTvT TauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    collectValCtx tau $ do
    mce <- checkVal e (arrT iota b)
    return $ do ce <- mce
                return $ C.EmitsE ce l

tcExp (Z.RepeatE _ e l) exp_ty = do
    (sigma, alpha, beta, mce) <-
        withSummaryContext e $ do
        (tau, mce)           <- inferExp e
        (sigma, alpha, beta) <- checkSTCUnit tau
        return (sigma, alpha, beta, mce)
    instType (stT (T l) sigma alpha beta) exp_ty
    return $ do ce <- mce
                return $ C.RepeatE ce l

tcExp (Z.ArrE _ (Z.ReadE zalpha _) (Z.WriteE zbeta _) l) exp_ty = do
    tau  <- fromZ (zalpha, TauK)
    tau' <- fromZ (zbeta, TauK)
    unifyTypes tau' tau
    instType (stT (T l) tau tau tau) exp_ty
    return $ do ctau <- trans tau
                cx   <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx (C.takeE ctau) $
                         C.emitE (C.varE cx)

tcExp (Z.ArrE _ (Z.ReadE ztau l) e _) tau_exp = do
    omega   <- newMetaTvT OmegaK l
    a       <- fromZ (ztau, TauK)
    b       <- newMetaTvT TauK l
    let tau =  ST [] omega a a b l
    instType tau tau_exp
    checkExp e tau

tcExp (Z.ArrE _ e (Z.WriteE ztau l) _) tau_exp = do
    omega   <- newMetaTvT OmegaK l
    s       <- newMetaTvT TauK l
    a       <- newMetaTvT TauK l
    b       <- fromZ (ztau, TauK)
    let tau =  ST [] omega s a b l
    instType tau tau_exp
    checkExp e tau

tcExp (Z.ArrE _ e1 e2 l) tau_exp = do
    omega1   <- newMetaTvT OmegaK l
    omega2   <- newMetaTvT OmegaK l
    a        <- newMetaTvT TauK l
    b        <- newMetaTvT TauK l
    b'       <- newMetaTvT TauK l
    c        <- newMetaTvT TauK l
    let tau1 =  ST [] omega1 a  a  b l
    let tau2 =  ST [] omega2 b' b' c l
    mce1     <- withSummaryContext e1 $
                checkExp e1 tau1
    mce2     <- withSummaryContext e2 $
                checkExp e2 tau2
    co       <- withSTContext tau1 tau2 $
                withSummaryContext e2 $
                mkCastT b b'
    omega  <- joinOmega omega1 omega2
    instType (ST [] omega a a c l) tau_exp
    checkForSplitContext
    return $ co $ do
        cb  <- trans b
        ce1 <- mce1
        ce2 <- mce2
        return $ C.ArrE cb ce1 ce2 l
  where
    checkForSplitContext :: Ti ()
    checkForSplitContext = do
        common_refs <- filterM isRefVar (Set.toList common_fvs)
        when (not (null common_refs)) $
            faildoc $ text "Branches of arrow expression share mutable state:" <+>
                      commasep (map ppr common_refs)
      where
        common_fvs :: Set Z.Var
        common_fvs = fvs e1 `Set.intersection` fvs e2

    withSTContext :: Type -> Type -> Ti a -> Ti a
    withSTContext tau1 tau2 m = do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        let doc = text "When pipelining a computation of type:" <+> ppr tau1' </>
                  text "             to a computation of type:" <+> ppr tau2'
        localLocContext (tau1 <--> tau2) doc m

tcExp e@(Z.ReadE {}) _ =
    withSummaryContext e $
        faildoc $
        text "Naked read. That's odd!"

tcExp e@(Z.WriteE {}) _ =
    withSummaryContext e $
        faildoc $
        text "Naked write. That's odd!"

tcExp (Z.StandaloneE e _) exp_ty =
    tcExp e exp_ty

tcExp (Z.MapE _ f ztau l) exp_ty = do
    tau  <- fromZ (ztau, PhiK)
    tau' <- lookupVar f
    unifyTypes tau' tau
    (a, b, co) <- checkMapFunT f tau
    instType (stT (T l) a a b) exp_ty
    return $ do cx     <- C.mkUniqVar "x" l
                cy     <- C.mkUniqVar "y" l
                ccalle <- co $ return $ C.varE cx
                ca     <- trans a
                return $ C.repeatE $
                         C.bindE cx (C.takeE ca) $
                         C.bindE cy ccalle $
                         C.emitE (C.varE cy)

tcExp (Z.CompLetE cl e l) exp_ty =
    checkCompLet cl $ do
    tau <- newMetaTvT MuK l
    instType tau exp_ty
    collectValCtx tau $ do
    checkExp e tau

tcExp (Z.StmE stms _) exp_ty =
    tcStms stms exp_ty

tcExp (Z.CmdE cmds _) exp_ty =
    tcCmds cmds exp_ty

tcExp e _ = faildoc $ text "tcExp: can't type check:" <+> ppr e

checkExp :: Z.Exp -> Type -> Ti (Ti C.Exp)
checkExp e tau = tcExp e (Check tau)

inferExp :: Z.Exp -> Ti (Type, Ti C.Exp)
inferExp e = do
    ref <- newRef (error "inferExp: empty result")
    mce <- tcExp e (Infer ref)
    tau <- readRef ref
    return (tau, mce)

tcStms :: [Z.Stm] -> Expected Type -> Ti (Ti C.Exp)
tcStms (stm@(Z.LetS {}) : []) _ =
    withSummaryContext stm $
    faildoc $ text "Last statement in statement sequence must be an expression"

tcStms (stm@(Z.LetS v ztau e l) : stms) exp_ty = do
    tau <- mkSTOmega
    instType tau exp_ty
    collectValCtx tau $ do
    (tau1, mce1) <- withSummaryContext stm $
                    checkLet v ztau TauK e
    mce2         <- extendVars [(v, tau1)] $
                    checkStms stms tau
    return $ do cv    <- trans v
                ctau1 <- trans tau1
                ce1   <- withSummaryContext stm $ mce1
                ce2   <- mce2
                return $ C.LetE cv ctau1 ce1 ce2 l

tcStms (stm@(Z.LetRefS {}) : []) _ =
    withSummaryContext stm $
    faildoc $ text "Last statement in statement sequence must be an expression"

tcStms (stm@(Z.LetRefS v ztau e_init l) : stms) exp_ty = do
    tau <- mkSTOmega
    instType tau exp_ty
    collectValCtx tau $ do
    (tau1, mce1) <- withSummaryContext stm $
                    checkLetRef v ztau e_init
    mce2         <- extendVars [(v, refT tau1)] $
                    checkStms stms tau
    return $ do cv    <- trans v
                ctau1 <- trans tau1
                ce1   <- withSummaryContext stm $ mce1
                ce2   <- mce2
                return $ C.LetRefE cv ctau1 ce1 ce2 l

tcStms (stm@(Z.ExpS e _) : []) exp_ty =
    withSummaryContext stm $ do
    tau <- mkSTOmega
    instType tau exp_ty
    collectValCtx tau $ do
    checkExp e tau

tcStms (stm@(Z.ExpS e l) : stms) exp_ty = do
    nu                     <- newMetaTvT TauK l
    tau1@(ST [] _ s a b _) <- mkSTC nu
    omega2                 <- newMetaTvT OmegaK l
    let tau2               =  ST [] omega2 s a b l
    instType tau2 exp_ty
    mce1  <- withSummaryContext stm $
             collectValCtx tau1 $
             checkExp e tau1
    mce2  <- checkStms stms tau2
    return $ do ce1 <- withSummaryContext stm $ mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcStms [] _ =
    panicdoc $ text "Empty statement sequence!"

checkStms :: [Z.Stm] -> Type -> Ti (Ti C.Exp)
checkStms stms tau = tcStms stms (Check tau)

tcCmds :: [Z.Cmd] -> Expected Type -> Ti (Ti C.Exp)
tcCmds (cmd@(Z.LetC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (Z.LetC cl _ : cmds) exp_ty = do
    tau <- mkSTOmega
    instType tau exp_ty
    collectValCtx tau $ do
    checkCompLet cl $ do
    checkCmds cmds tau

tcCmds (cmd@(Z.BindC {}) : []) _ =
    withSummaryContext cmd $
    faildoc $ text "Last command in command sequence must be an expression"

tcCmds (cmd@(Z.BindC v ztau e l) : cmds) exp_ty = do
    nu                     <- fromZ (ztau, TauK)
    tau1@(ST [] _ s a b _) <- mkSTC nu
    omega2                 <- newMetaTvT OmegaK l
    let tau2               =  ST [] omega2 s a b l
    instType tau2 exp_ty
    mce1 <- withSummaryContext cmd $ do
            collectValCtx tau1 $ do
            checkExp e tau1
    mce2 <- extendVars [(v, nu)] $
            checkCmds cmds tau2
    return $ do cv  <- trans v
                ce1 <- withSummaryContext cmd $ mce1
                ce2 <- mce2
                return $ C.BindE (C.BindV cv) ce1 ce2 l

tcCmds (cmd@(Z.ExpC e _) : []) exp_ty =
    withSummaryContext cmd $ do
    tau <- mkSTOmega
    instType tau exp_ty
    collectValCtx tau $ do
    checkExp e tau

tcCmds (cmd@(Z.ExpC e l) : cmds) exp_ty = do
    nu                     <- newMetaTvT TauK l
    tau1@(ST [] _ s a b _) <- mkSTC nu
    omega2                 <- newMetaTvT OmegaK l
    let tau2               =  ST [] omega2 s a b l
    instType tau2 exp_ty
    mce1 <- withSummaryContext cmd $
            collectValCtx tau1 $
            checkExp e tau1
    mce2 <- checkCmds cmds tau2
    return $ do ce1 <- withSummaryContext cmd $ mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcCmds [] _ =
    panicdoc $ text "Empty command sequence!"

checkCmds :: [Z.Cmd] -> Type -> Ti (Ti C.Exp)
checkCmds cmds tau = tcCmds cmds (Check tau)

-- | Type check an expression in a context where a value is needed. This will
-- generate extra code to dereference any references and run any actions of type
-- @forall s a b . ST tau s a b@.
tcVal :: Z.Exp -> Expected Type -> Ti (Ti C.Exp)
tcVal e exp_ty = do
    (tau, mce) <- inferExp e
    tau' <- compress tau
    go tau' mce
  where
    go :: Type -> Ti C.Exp -> Ti (Ti C.Exp)
    go (RefT tau _) mce = do
        let mce' = do
            ce1 <- mce
            cx  <- C.mkUniqVar "x" ce1
            tellValCtx $ \ce2 -> C.bindE cx (C.derefE ce1) ce2
            return $ C.varE cx
        instType tau exp_ty
        return mce'

    go (ST [] (C tau _) s a b l) mce = do
        mu    <- askValCtxType
        omega <- newMetaTvT OmegaK l
        unifyTypes (ST [] omega s a b l) mu
        instType tau exp_ty
        return $ do
            ce1   <- mce
            cx    <- C.mkUniqVar "x" ce1
            tellValCtx $ \ce2 -> C.bindE cx ce1 ce2
            return $ C.varE cx

    go tau mce = do
        instType tau exp_ty
        return mce

checkVal :: Z.Exp -> Type -> Ti (Ti C.Exp)
checkVal e tau = tcVal e (Check tau)

inferVal :: Z.Exp -> Ti (Type, Ti C.Exp)
inferVal e = do
    ref <- newRef (error "inferVal: empty result")
    mce <- tcVal e (Infer ref)
    tau <- readRef ref
    return (tau, mce)

checkBoolVal :: Z.Exp -> Ti (Ti C.Exp)
checkBoolVal e = do
    mce <- checkExp e (BoolT l)
    return $ do ce <- mce
                return $ C.returnE ce
  where
    l :: SrcLoc
    l = srclocOf e

kcType :: Type -> Expected Kind -> Ti ()
kcType tau@(UnitT {})    kappa_exp = instKind tau TauK kappa_exp
kcType tau@(BoolT {})    kappa_exp = instKind tau TauK kappa_exp
kcType tau@(BitT {})     kappa_exp = instKind tau TauK kappa_exp
kcType tau@(IntT {})     kappa_exp = instKind tau TauK kappa_exp
kcType tau@(FloatT {})   kappa_exp = instKind tau TauK kappa_exp
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
    mapM_ checkArgKind taus
    checkRetKind tau_ret
    instKind tau0 PhiK kappa_exp
  where
    checkArgKind :: Type -> Ti ()
    checkArgKind tau = do
        kappa <- inferKind tau
        case kappa of
          TauK -> return ()
          RhoK -> return ()
          MuK  -> return ()
          _    -> checkKind tau TauK

    checkRetKind :: Type -> Ti ()
    checkRetKind tau = do
        kappa <- inferKind tau
        case kappa of
          TauK -> return ()
          MuK  -> return ()
          _    -> checkKind tau MuK

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

instKind :: Type -> Kind -> Expected Kind -> Ti ()
instKind _ kappa (Infer ref) =
    writeRef ref kappa

instKind _ kappa1 (Check kappa2) | kappa1 == kappa2 =
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

checkKind :: Type -> Kind -> Ti ()
checkKind tau kappa = kcType tau (Check kappa)

inferKind :: Type -> Ti Kind
inferKind tau = do
    ref <- newRef (error "inferKind: empty result")
    kcType tau (Infer ref)
    readRef ref

generalize :: Type -> Ti (Type, Co)
generalize tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Ti (Type, Co)
    go tau@(ST [] omega sigma tau1 tau2 l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let alphaMtvs =  filter (isKind TauK) mtvs
        alphas        <- freshVars (length alphaMtvs) ((Set.toList . fvs) tau)
        extendTyVars (alphas `zip` repeat TauK) $
            zipWithM_ kcWriteTv alphaMtvs [TyVarT alpha noLoc | alpha <- alphas]
        tau <- compress $ ST alphas omega sigma tau1 tau2 l
        let co mce = do
            extendTyVars (alphas `zip` repeat TauK) $ do
            mce
        return (tau, co)

    go tau@(ST {}) =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau@(FunT [] taus tau_ret l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let iotaMtvs  =  filter (isKind IotaK) mtvs
        iotas         <- freshVars (length iotaMtvs) ((Set.toList . fvs) tau)
        extendIVars (iotas `zip` repeat IotaK) $
            zipWithM_ kcWriteTv iotaMtvs [VarI iota noLoc | iota <- iotas]
        tau <- compress $ FunT iotas taus tau_ret l
        let co mce = do
            extendIVars (iotas `zip` repeat IotaK) $ do
            ciotas <- mapM trans iotas
            mce >>= checkLetFunE ciotas
        return (tau, co)
      where
        checkLetFunE :: [C.IVar] -> C.Exp -> Ti C.Exp
        checkLetFunE ciotas (C.LetFunE cf [] cvtaus ctau ce1 ce2 l) =
            return $ C.LetFunE cf ciotas cvtaus ctau ce1 ce2 l

        checkLetFunE ciotas (C.LetExtFunE cf [] cvtaus ctau ce2 l) =
            return $ C.LetExtFunE cf ciotas cvtaus ctau ce2 l

        checkLetFunE _ ce =
            panicdoc $
            text "generalize: expected to coerce a letfun, but got:" <+> ppr ce

    go tau@(FunT {}) =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau =
        panicdoc $ text "Asked to generalize non-ST/non-function type:" <+> (text . show) tau

    isKind :: Kind -> MetaTv -> Bool
    isKind kappa1 (MetaTv _ kappa2 _) = kappa2 == kappa1

instantiate :: Type -> Ti (Type, Co)
instantiate tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Ti (Type, Co)
    go (ST alphas omega sigma tau1 tau2 l) = do
        (_, theta, phi) <- instVars alphas TauK
        let tau = ST [] (subst theta phi omega) (subst theta phi sigma)
                     (subst theta phi tau1) (subst theta phi tau2) l
        return (tau, id)

    go (FunT iotas taus tau_ret l) = do
        (mtvs, theta, phi) <- instVars iotas IotaK
        let tau  = FunT [] (subst theta phi taus) (subst theta phi tau_ret) l
        let co mce = do
                (cf, ces, l) <- mce >>= checkFunE
                ciotas       <- compress mtvs >>= mapM trans
                return $ C.CallE cf ciotas ces l
        return (tau, co)
      where
        checkFunE :: C.Exp -> Ti (C.Exp, [C.Exp], SrcLoc)
        checkFunE (C.CallE cf [] ces l) =
            return (cf, ces, l)

        checkFunE ce =
            panicdoc $
            text "instantiate: expected to coerce a call, but got:" <+> ppr ce

    go tau =
        return (tau, id)

    instVars :: (Located tv, Subst Type tv Type)
             => [tv] -> Kind -> Ti ([Type], Map tv Type, Set tv)
    instVars tvs kappa = do
        mtvs      <- mapM (newMetaTvT kappa) tvs
        let theta =  Map.fromList (tvs `zip` mtvs)
        let phi   =  fvs tau0 <\\> fromList tvs
        return (mtvs, theta, phi)

-- | Update a type meta-variable with a type while checking that the type's kind
-- matches the meta-variable's kind.
kcWriteTv :: MetaTv -> Type -> Ti ()
kcWriteTv mtv@(MetaTv _ kappa _) tau = do
    maybe_tau <- readTv mtv
    case maybe_tau of
      Nothing -> return ()
      Just _  -> panicdoc $ text "Type meta-variable already written"
    checkKind tau kappa
    writeTv mtv tau

-- | Return 'True' if @v@ has a reference type, 'False' otherwise
isRefVar :: Z.Var -> Ti Bool
isRefVar v = do
    tau <- lookupVar v >>= compress
    case tau of
      RefT {} -> return True
      _       -> return False

-- | Check that a type supports equality.
checkEqT :: Type -> Ti ()
checkEqT tau =
    checkKind tau TauK

-- | Check that a type supports ordering.
checkOrdT :: Type -> Ti ()
checkOrdT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (BitT {})              = return ()
    go (IntT {})              = return ()
    go (FloatT {})            = return ()
    go (StructT s _)
        | Z.isComplexStruct s = return ()
    go tau                    = unifyTypes tau intT `catch`
                                    \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected comparable type, but got:" <+> ppr tau'

-- | Check that a type is a type on which we can perform Boolean operations.
checkBoolT :: Type -> Ti ()
checkBoolT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (BitT {})  = return ()
    go (BoolT {}) = return ()
    go (IntT {})  = return ()
    go tau        = unifyTypes tau intT `catch`
                        \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected a Boolean type, e.g., bit, bool, or int, but got:" <+> ppr tau'

-- | Check that a type is a type on which we can perform bitwise operations.
checkBitT :: Type -> Ti ()
checkBitT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (BitT {}) = return ()
    go (IntT {}) = return ()
    go tau       = unifyTypes tau intT `catch`
                       \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected a bit type, e.g., bit or int, but got:" <+> ppr tau'

-- | Check that a type is an integral type
checkIntT :: Type -> Ti ()
checkIntT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (IntT _ _) = return ()
    go tau        = unifyTypes tau intT

-- | Check that a type is a numerical type.
checkNumT :: Type -> Ti ()
checkNumT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (IntT {})              = return ()
    go (FloatT {})            = return ()
    go (StructT s _)
        | Z.isComplexStruct s = return ()
    go tau                    = unifyTypes tau intT `catch`
                                    \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected integral type, but got:" <+> ppr tau'

-- | Check that a type is a /signed/ numerical type.
checkSignedNumT :: Type -> Ti ()
checkSignedNumT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go (IntT {})              = return ()
    go (FloatT {})            = return ()
    go (StructT s _)
        | Z.isComplexStruct s = return ()
    go tau                    = unifyTypes tau intT `catch`
                                    \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected signed integral type, but got:" <+> ppr tau'

-- | Check that a type is an @ref \alpha@ type, returning @\alpha@.
checkRefT :: Type -> Ti Type
checkRefT tau =
    compress tau >>= go
  where
    go :: Type -> Ti Type
    go (RefT alpha _) =
        return alpha

    go tau = do
        alpha <- newMetaTvT TauK tau
        unifyTypes tau (refT alpha)
        return alpha

-- | Check that a type is an @arr \iota \alpha@ type, returning @\iota@ and
-- @\alpha@.
checkArrT :: Type -> Ti (Type, Type)
checkArrT tau =
    compress tau >>= go
  where
    go :: Type -> Ti (Type, Type)
    go (ArrT iota alpha _) =
        return (iota, alpha)

    go tau = do
        iota  <- newMetaTvT IotaK tau
        alpha <- newMetaTvT TauK tau
        unifyTypes tau (arrT iota alpha)
        return (iota, alpha)

-- | Check that a type is a struct type, returning the name of the struct.
checkStructT :: Type -> Ti Z.Struct
checkStructT tau =
    compress tau >>= go
  where
    go :: Type -> Ti Z.Struct
    go (StructT s _) =
        return s

    go tau =
        faildoc $ nest 2 $
        text "Expected struct type, but got:" <+/> ppr tau

checkStructFieldT :: StructDef -> Z.Field -> Ti Type
checkStructFieldT (StructDef s flds _) f =
    case lookup f flds of
      Just tau -> return tau
      Nothing ->
          faildoc $
          text "Struct" <+> ppr s <+>
          text "does not have a field named" <+> ppr f

-- | Check that a type is an @ST (C ()) \sigma \alpha \beta@ type, returning the
-- three type indices
checkSTCUnit :: Type -> Ti (Type, Type, Type)
checkSTCUnit tau =
    compress tau >>= go
  where
    go :: Type -> Ti (Type, Type, Type)
    go (ST [] (C (UnitT _) _) sigma alpha beta _) =
        return (sigma, alpha, beta)

    go tau = do
        sigma <- newMetaTvT TauK tau
        alpha <- newMetaTvT TauK tau
        beta  <- newMetaTvT TauK tau
        unifyTypes tau (stT (cT unitT) sigma alpha beta)
        return (sigma, alpha, beta)

checkFunT :: Z.Var -> Int -> Type
          -> Ti ([Type], Type, Co)
checkFunT _ nargs tau =
    instantiate tau >>= go
  where
    go :: (Type, Co) -> Ti ([Type], Type, Co)
    go (FunT [] taus tau_ret _, co) =
        return (taus, tau_ret, co)

    go (tau_f, co) = do
        taus    <- replicateM nargs (newMetaTvT TauK tau)
        tau_ret <- newMetaTvT TauK tau
        unifyTypes tau_f (funT taus tau_ret)
        return (taus, tau_ret, co)

-- | Check that a function type is appropriate for a @map@. The function result
-- must have type @forall s a b . ST (C c) s a b@. This guarantees that although
-- it may read and write references, it neither consumes nor produces values
-- from the stream.
checkMapFunT :: Z.Var -> Type
             -> Ti (Type, Type, Co)
checkMapFunT f tau = do
    -- Instantiate the function type's outer forall, which quantifies over array
    -- index variables.
    (tau_f, co1) <- instantiate tau
    (c, tau_ret) <-
        case tau_f of
          FunT [] [c] tau_ret@(ST {}) _ -> return (c, tau_ret)
          _ -> err
    -- Check that the return type of the function we are mapping is
    -- @forall s a b . ST tau s a b@.
    checkMapReturnType tau_ret
    -- XXX Instantiate over the return type, which must be an ST type. We should
    -- handle pure functions here too!
    (tau_ret', co2) <- instantiate tau_ret
    (d, s, a, b) <-
        case tau_ret' of
          ST [] (C d _) s a b _ -> return (d, s, a, b)
          _ -> err
    unifyTypes c a
    unifyTypes s a
    unifyTypes d b
    let co mce = co2 $ co1 $ do
        ce <- mce
        cf <- C.varE <$> trans f
        return $ C.callE cf [ce]
    return (a, b, co)
  where
    checkMapReturnType :: Type -> Ti ()
    checkMapReturnType (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _)
        | sort [s',a',b'] == sort [s,a,b] =
        return ()

    checkMapReturnType _ =
        err

    err :: Ti a
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

mkSTC :: Type -> Ti Type
mkSTC tau = do
    s <- newMetaTvT TauK l
    a <- newMetaTvT TauK l
    b <- newMetaTvT TauK l
    return $ ST [] (C tau l) s a b l
  where
    l :: SrcLoc
    l = srclocOf tau

mkSTOmega :: Ti Type
mkSTOmega = do
    omega <- newMetaTvT OmegaK l
    s     <- newMetaTvT TauK l
    a     <- newMetaTvT TauK l
    b     <- newMetaTvT TauK l
    return $ ST [] omega s a b l
  where
    l :: SrcLoc
    l = noLoc

-- | @castVal tau e@ infers the type of @e@ and, if possible, generates an appropriate
-- cast to the type @tau@. It returns an elaborated value expression. We special
-- case casting array expressions---array expressions are the only time we cast
-- between arrays types. This is all we need for the common case of arrays of
-- integers that need to be represented as arrays on, say, int8's, and it is
-- also the only case where we know we can make casting memory efficient.
castVal :: Type -> Z.Exp -> Ti (Ti C.Exp)
castVal tau2 e = do
    (tau1, mce) <- inferVal e
    co <- case (e, tau1, tau2) of
            (Z.ArrayE {}, ArrT iota1 etau1 _, ArrT iota2 etau2 _) -> do
                unifyTypes iota1 iota2
                mkArrayCast etau1 etau2
            _ ->
                mkCast tau1 tau2
    return $ co mce
  where
    mkArrayCast :: Type -> Type -> Ti Co
    mkArrayCast tau1 tau2 = do
        co <- mkCast tau1 tau2
        return $ \mce -> do
            (ces, l) <- mce >>= checkArrayE
            ces'     <- sequence (map (co . return) ces)
            return $ C.ArrayE ces' l


    checkArrayE :: C.Exp -> Ti ([C.Exp], SrcLoc)
    checkArrayE (C.ArrayE ces l) =
        return (ces, l)

    checkArrayE e =
        faildoc $ nest 2 $
        text "Expected array expression but got:" <+/> ppr e

mkCast :: Type -> Type -> Ti Co
mkCast tau1 tau2 = do
    checkCast tau1 tau2
    return $ \mce -> do
        tau1' <- compress tau1
        tau2' <- compress tau2
        go tau1' tau2' mce
  where
    go :: Type -> Type -> Co
    go tau1 tau2 mce | tau1 == tau2 =
        mce

    go _ tau2 mce = do
        ctau <- trans tau2
        ce   <- mce
        return $ C.UnopE (C.Cast ctau) ce (srclocOf ce)

-- | @mkCastT tau1 tau2@ generates a computation of type @ST T tau1 tau2@ that
-- casts values from @tau1@ to @tau2@.
mkCastT :: Type -> Type -> Ti Co
mkCastT tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti Co
    go tau1 tau2 | tau1 == tau2 =
        return id

    go tau1 tau2 = do
        co <- mkCast tau1 tau2
        let mkPipe = do
            ctau1 <- trans tau1
            cx    <- C.mkUniqVar "x" (srclocOf tau1)
            cxe   <- co $ return (C.varE cx)
            return $ C.repeatE $
                     C.bindE cx (C.takeE ctau1) $
                     C.emitE cxe
        return $ \mce -> do
            (clhs, crhs, l) <- mce >>= checkArrE
            ctau1           <- trans tau1
            ctau2           <- trans tau2
            cpipe           <- mkPipe
            return $ C.ArrE ctau2 (C.ArrE ctau1 clhs cpipe l) crhs l
      where
        checkArrE :: C.Exp -> Ti (C.Exp, C.Exp, SrcLoc)
        checkArrE (C.ArrE _ clhs crhs l) =
            return (clhs, crhs, l)

        checkArrE e =
            faildoc $ nest 2 $
            text "Expected arrow expression, but got:" <+/> ppr e

-- | @checkCast tau1 tau2@ checks that a value of type @tau1@ can be cast to a
-- value of type @tau2@.
checkCast :: Type -> Type -> Ti ()
checkCast tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti ()
    go tau1 tau2 | tau1 == tau2 =
        return ()

    go (IntT {}) (IntT {}) =
        return ()

    go (IntT {}) (BitT {}) =
        return ()

    go (BitT {}) (IntT {}) =
        return ()

    go (IntT {}) (FloatT {}) =
        return ()

    go (FloatT {}) (IntT {}) =
        return ()

    go (FloatT {}) (FloatT {}) =
        return ()

    go (StructT s1 _) (StructT s2 _) | Z.isComplexStruct s1 && Z.isComplexStruct s2 =
        return ()

    go tau1 tau2 =
        unifyTypes tau1 tau2
      `catch` \(_ :: UnificationException) -> do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        faildoc $ text "Cannot cast" <+> ppr tau1' <+> text "to" <+> ppr tau2'

-- | Implement the join operation for types of kind omega
joinOmega :: Type -> Type -> Ti Type
joinOmega tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti Type
    go tau1@(C {}) (T {})      = return tau1
    go (T {})      tau2@(C {}) = return tau2
    go tau1@(T {}) (T {})      = return tau1

    go tau1 tau2 =
        faildoc $ text "Cannot join" <+> ppr tau1 <+> text "and" <+> ppr tau2

instType :: Type -> Expected Type -> Ti ()
instType tau1 (Infer ref)  = writeRef ref tau1
instType tau1 (Check tau2) = unifyTypes tau1 tau2

-- | Throw a "Expected type.." error. @tau1@ is the type we got, and @tau2@ is
-- the expected type.
expectedTypeErr :: Type -> Type -> Ti a
expectedTypeErr tau1 tau2 = do
    [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
    faildoc $
      text "Expected type:" <+> ppr tau2' </>
      text "but got:      " <+> ppr tau1'

data UnificationException = UnificationException Type Type
  deriving (Typeable)

instance Show UnificationException where
    show (UnificationException tau1 tau2) =
        pretty 80 $
        text "Expected type:" <+> ppr tau2 </>
        text "but got:      " <+> ppr tau1

instance Exception UnificationException

-- | Unify two types. The first argument is what we got, and the second is what
-- we expect.
unifyTypes :: Type -> Type -> Ti ()
unifyTypes tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    unify Map.empty Map.empty tau1' tau2'
  where
    unify :: Map TyVar TyVar
          -> Map IVar IVar
          -> Type
          -> Type
          -> Ti ()
    unify theta phi tau1 tau2 = do
        tau1' <- compress tau1
        tau2' <- compress tau2
        go theta phi tau1' tau2'

    go :: Map TyVar TyVar
       -> Map IVar IVar
       -> Type
       -> Type
       -> Ti ()
    go _ _ (MetaT mtv1 _) (MetaT mtv2 _) | mtv1 == mtv2 =
        return ()

    go _ _ tau1@(MetaT mtv _) tau2 =
        updateMetaTv mtv tau1 tau2

    go _ _ tau1 tau2@(MetaT mtv _) =
        updateMetaTv mtv tau2 tau1

    go _ _ (UnitT {})    (UnitT {})                 = return ()
    go _ _ (BoolT {})    (BoolT {})                 = return ()
    go _ _ (BitT {})     (BitT {})                  = return ()
    go _ _ (IntT w1 _)   (IntT w2 _)     | w1 == w2 = return ()
    go _ _ (FloatT w1 _) (FloatT w2 _)   | w1 == w2 = return ()
    go _ _ (StringT {})  (StringT {})               = return ()

    go _ _ (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    go theta phi (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify theta phi tau1a tau1b
        unify theta phi tau2a tau2b

    go theta phi (C tau1 _) (C tau2 _) =
        unify theta phi tau1 tau2

    go _ _ (T {}) (T {}) =
        return ()

    go theta phi (ST alphas_a omega_a tau_1a tau_2a tau_3a _)
                 (ST alphas_b omega_b tau_1b tau_2b tau_3b _)
        | length alphas_a == length alphas_b =
          extendTyVars (alphas_b `zip` repeat TauK) $ do
          unify theta' phi omega_a omega_b
          unify theta' phi tau_1a tau_1b
          unify theta' phi tau_2a tau_2b
          unify theta' phi tau_3a tau_3b
      where
        theta' :: Map TyVar TyVar
        theta' = Map.fromList (alphas_a `zip` alphas_b) `Map.union` theta

    go theta phi (RefT tau1 _) (RefT tau2 _) =
        unify theta phi tau1 tau2

    go theta phi (FunT iotas_a taus_a tau_a _)
                 (FunT iotas_b taus_b tau_b _)
        | length iotas_a == length iotas_b && length taus_a == length taus_b =
          extendIVars (iotas_b `zip` repeat IotaK) $ do
          zipWithM_ (unify theta phi') taus_a taus_b
          unify theta phi' tau_a tau_b
      where
        phi' :: Map IVar IVar
        phi' = Map.fromList (iotas_a `zip` iotas_b) `Map.union` phi

    go _ _ (ConstI i1 _) (ConstI i2 _)  | i1 == i2 =
        return ()

    go _ _ (VarI v1 _) (VarI v2 _)  | v1 == v2 =
        return ()

    go theta _ (TyVarT tv1 _) (TyVarT tv2 _) | Just tv2' <- Map.lookup tv2 theta
                                             , tv1 == tv2' = do
        return ()

    go _ _ _ _ = do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        throw $ UnificationException tau1' tau2'

    updateMetaTv :: MetaTv -> Type -> Type -> Ti ()
    updateMetaTv mtv tau1 tau2 = do
        mtvs2 <- metaTvs [tau2]
        when (mtv `elem` mtvs2) $ do
            [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
            faildoc $ nest 2 $
              text "Cannot construct the infinite type:" <+/>
              ppr tau1' <+> text "=" <+> ppr tau2'
        kcWriteTv mtv tau2

-- | Type check two expressions and attempt to unify their types. This may
-- requires adding casts.
unifyExpTypes :: Z.Exp -> Z.Exp -> Ti (Type, Ti C.Exp, Ti C.Exp)
unifyExpTypes e1 e2 = do
    (tau1, mce1) <- inferExp e1
    (tau2, mce2) <- inferExp e2
    unifyCompiledExpTypes tau1 e1 mce1 tau2 e2 mce2

-- | Type check two expressions, treating them as values, and attempt to unify their types. This may
-- requires adding casts.
unifyValTypes :: Z.Exp -> Z.Exp -> Ti (Type, Ti C.Exp, Ti C.Exp)
unifyValTypes e1 e2 = do
    (tau1, mce1) <- inferVal e1
    (tau2, mce2) <- inferVal e2
    unifyCompiledExpTypes tau1 e1 mce1 tau2 e2 mce2

unifyCompiledExpTypes :: Type -> Z.Exp -> Ti C.Exp
                      -> Type -> Z.Exp -> Ti C.Exp
                      -> Ti (Type, Ti C.Exp, Ti C.Exp)
unifyCompiledExpTypes tau1 e1 mce1 tau2 e2 mce2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' e1 mce1 tau2' e2 mce2
  where
    go :: Type -> Z.Exp -> Ti C.Exp
       -> Type -> Z.Exp -> Ti C.Exp
       -> Ti (Type, Ti C.Exp, Ti C.Exp)
    go tau1@(MetaT {}) _ mce1 tau2 _ mce2 = do
        unifyTypes tau1 tau2
        return (tau2, mce1, mce2)

    go tau1 _ mce1 tau2@(MetaT {}) _ mce2 = do
        unifyTypes tau2 tau1
        return (tau1, mce1, mce2)

    go tau1 _ mce1 tau2 _ mce2 | tau1 == tau2 = do
        return (tau1, mce1, mce2)

    go tau1 (Z.ConstE {}) mce1 tau2 _ mce2 = do
        co <- mkCast tau1 tau2
        return (tau2, co mce1, mce2)

    go tau1 _ mce1 tau2 (Z.ConstE {}) mce2 = do
        co <- mkCast tau2 tau1
        return (tau1, mce1, co mce2)

    go tau1 _ mce1 tau2 _ mce2 = do
        maybe_tau <- lubType tau1 tau2
        case maybe_tau of
          Just tau -> do co1 <- mkCast tau1 tau
                         co2 <- mkCast tau2 tau
                         return (tau, co1 mce1, co2 mce2)
          Nothing  -> do unifyTypes tau1 tau2
                         return (tau1, mce1, mce2)

    lubType :: Type -> Type -> Ti (Maybe Type)
    lubType (IntT w1 l) (IntT w2 _) =
        return $ Just $ IntT (max w1 w2) l

    lubType (FloatT w1 l) (FloatT w2 _) =
        return $ Just $ FloatT (max w1 w2) l

    lubType (StructT s1 l) (StructT s2 _) | Z.isComplexStruct s1 && Z.isComplexStruct s2 = do
        s <- lubComplex s1 s2
        return $ Just $ StructT s l

    lubType _ _ =
        return Nothing

    lubComplex :: Z.Struct -> Z.Struct -> Ti Z.Struct
    lubComplex s1 s2 = do
        i1 <- complexToInt s1
        i2 <- complexToInt s2
        intToComplex (max i1 i2)
      where
        complexToInt :: Z.Struct -> Ti Int
        complexToInt "complex"   = return 3
        complexToInt "complex8"  = return 0
        complexToInt "complex16" = return 1
        complexToInt "complex32" = return 2
        complexToInt "complex64" = return 3
        complexToInt _           = fail "intFromComplex: not a complex struct"

        intToComplex :: Int -> Ti Z.Struct
        intToComplex 0 = return "complex8"
        intToComplex 1 = return "complex16"
        intToComplex 2 = return "complex32"
        intToComplex 3 = return "complex64"
        intToComplex _ = fail "intToComplex: out of bounds"

traceVar :: Z.Var -> Type -> Ti ()
traceVar v tau = do
    [tau'] <- sanitizeTypes [tau]
    traceTc $ text "Variable" <+> ppr v <+> colon <+> ppr tau'

class FromZ a b | a -> b where
    fromZ :: a -> Ti b

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
    fromZ (Z.ArrT i tau l) = ArrT <$> fromZ i <*> fromZ tau <*> pure l
    fromZ (Z.StructT s l)  = pure $ StructT s l
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

    fromZ (Z.ArrI v _) = do
        (ind, _) <- lookupVar v >>= checkArrT
        return ind

    fromZ (Z.NoneI l) =
        newMetaTvT IotaK l

instance FromZ Z.VarBind (Z.Var, Type) where
    fromZ (Z.VarBind v False ztau) = do
          tau <- fromZ ztau
          return (v, tau)

    fromZ (Z.VarBind v True ztau) = do
          tau <- refT <$> fromZ ztau
          return (v, tau)

instance FromZ [Z.VarBind] [(Z.Var, Type)] where
    fromZ [] =
        return []

    fromZ (Z.VarBind v False ztau : vbs) = do
          tau  <- fromZ ztau
          vbs' <- extendVars [(v, tau)] $
                  fromZ vbs
          return $ (v, tau) : vbs'

    fromZ (Z.VarBind v True ztau : vbs) = do
          tau  <- refT <$> fromZ ztau
          vbs' <- extendVars [(v, tau)] $
                  fromZ vbs
          return $ (v, tau) : vbs'

class Trans a b | b -> a where
    trans :: a -> Ti b

instance Trans Z.Var C.Var where
    trans (Z.Var n) = pure $ C.Var n

instance Trans Z.Field C.Field where
    trans (Z.Field n) = pure $ C.Field n

instance Trans Z.Struct C.Struct where
    trans (Z.Struct n) = pure $ C.Struct n

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
        go :: Type -> Ti C.Type
        go (UnitT l)      = C.UnitT <$> pure l
        go (BoolT l)      = C.BoolT <$> pure l
        go (BitT l)       = C.BitT <$> pure l
        go (IntT w l)     = C.IntT <$> trans w <*> pure l
        go (FloatT w l)   = C.FloatT <$> trans w <*> pure l
        go (StringT l)    = pure $ C.StringT l
        go (StructT s l)  = C.StructT <$> trans s <*> pure l
        go (RefT tau l)   = C.RefT <$> go tau <*> pure l
        go (ArrT i tau l) = C.ArrT <$> trans i <*> go tau <*> pure l

        go (ST alphas omega tau1 tau2 tau3 l) =
            extendTyVars (alphas `zip` repeat TauK) $
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

instance Trans (Z.Var, Type) (C.Var, C.Type) where
    trans (v, tau) = (,) <$> trans v <*> trans tau
