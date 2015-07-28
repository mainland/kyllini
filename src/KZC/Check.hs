{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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

checkCompLet :: Z.CompLet
             -> Tc C.Exp (Tc b C.Exp)
             -> Tc C.Exp (Tc b C.Exp)
checkCompLet cl@(Z.LetCL v ztau e l) k = do
    (tau, mce1) <- withSummaryContext cl $ do
                   tau <- fromZ ztau
                   extendVars [(v, tau)] $ do
                   mce1 <- checkExp e tau
                   return (tau, mce1)
    mce2 <- extendVars [(v, tau)] $
            k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

checkCompLet cl@(Z.LetRefCL v ztau init l) k = do
    (tau, mce1) <- withSummaryContext cl $ do
                   tau <- fromZ ztau
                   extendVars [(v, tau)] $ do
                   mce1 <- case init of
                             Nothing -> return $ return Nothing
                             Just e  -> do mce <- checkExp e tau
                                           return $ Just <$> mce
                   return (tau, mce1)
    mce2  <- extendVars [(v, tau)] $
             k
    return $ do cv   <- trans v
                ctau <- trans (refT tau)
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau ce1 ce2 l

checkCompLet cl@(Z.LetFunCL f ztau ps e l) k = do
    (tau, ptaus, mce1) <- withSummaryContext cl $ do
                          tau   <- fromZ ztau
                          ptaus <- mapM fromZ ps
                          extendVars ((f,tau) : ptaus) $ do
                          (tau_ret, mce1) <- inferExp e
                          unifyTypes (funT (map snd ptaus) tau_ret) tau
                          return (tau, ptaus, mce1)
    mce2 <- extendVars ((f,tau) : ptaus) $
            k
    return $ do cf     <- trans f
                cptaus <- mapM trans ptaus
                ctau   <- trans tau
                ce1    <- mce1
                ce2    <- mce2
                return $ C.LetFunE cf [] cptaus ctau ce1 ce2 l

checkCompLet cl@(Z.LetCompCL v ztau _ e l) k = do
    (tau, mce1) <- withSummaryContext cl $ do
                   tau <- fromZ ztau
                   extendVars [(v, tau)] $ do
                   mce1 <- checkExp e tau
                   return (tau, mce1)
    mce2  <- extendVars [(v, tau)] $ k
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

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
    tau <- lookupVar v
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

tcExp (Z.ReturnE _ e l) exp_ty = do
    (nu, mce) <- inferExp e
    alpha     <- newMetaTvT l
    beta      <- newMetaTvT l
    instType (ST (C nu l) alpha beta l) exp_ty
    return $ do ce <- mce
                return $ C.ReturnE ce l

tcExp (Z.ArrE _ e1 e2 l) tau_exp = do
    (tau_e1, mce1)        <- inferExp e1
    (omega1, alpha, beta) <- checkSTType tau_e1
    omega2                <- newMetaTvT e2
    mce2                  <- checkExp e2 (stT omega2 alpha beta)
    common_refs           <- filterM isRefVar (Set.toList common_fvs)
    omega                 <- joinOmega omega1 omega2
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
    beta  <- newMetaTvT ztau
    instType (ST (T l) alpha beta l) exp_tau
    return $ do cx <- C.mkUniqVar "x" l
                return $ C.repeatE $
                         C.bindE cx C.takeE $
                         C.emitE (C.varE cx)

tcExp (Z.WriteE ztau l) exp_tau = do
    alpha <- newMetaTvT ztau
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
    checkFunType (FunT [alpha] (ST (C beta _) alpha' beta' _) _) = do
        unifyTypes alpha' alpha
        unifyTypes beta'  beta
        return (alpha, beta)

    checkFunType tau = do
        alpha <- newMetaTvT tau
        beta  <- newMetaTvT tau
        unifyTypes tau (FunT [alpha] (ST (C beta l) alpha beta l) l)
        return (alpha, beta)

tcExp (Z.StmE stms _) exp_tau =
    tcStms stms exp_tau

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
    (tau, mce1) <- withSummaryContext stm $ do
                   tau <- fromZ ztau
                   extendVars [(v, tau)] $ do
                   mce1 <- checkExp e tau
                   return (tau, mce1)
    mce2 <- extendVars [(v, tau)] $
            tcStms stms exp_ty
    return $ do cv   <- trans v
                ctau <- trans tau
                ce1  <- mce1
                ce2  <- mce2
                return $ C.LetE cv ctau (Just ce1) ce2 l

tcStms (stm@(Z.LetRefS {}) : []) _ =
    withSummaryContext stm $
    faildoc $ text "Last statement in statement sequence must be an expression"

tcStms (stm@(Z.LetRefS v ztau init l) : stms) exp_ty = do
    (tau, mce1) <- withSummaryContext stm $ do
                   tau <- fromZ ztau
                   extendVars [(v, tau)] $ do
                   mce1 <- case init of
                             Nothing -> return $ return Nothing
                             Just e  -> do mce <- checkExp e tau
                                           return $ Just <$> mce
                   return (tau, mce1)
    mce2  <- extendVars [(v, tau)] $
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
    omega            <- newMetaTvT e
    let tau          =  stT omega alpha beta
    instType tau exp_ty
    mce2 <- tcStms stms exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ C.seqE ce1 ce2

tcStms [] _ =
    panicdoc $ text "Empty statement sequence!"

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

-- | Check that a type is an @ST \omega \alpha \beta@ type, returning the three type indices
checkSTType :: Type -> Tc b (Type, Type, Type)
checkSTType tau =
    compress tau >>= go
  where
    go :: Type -> Tc b (Type, Type, Type)
    go (ST omega alpha beta _) =
        return (omega, alpha, beta)

    go tau = do
        omega <- newMetaTvT tau
        alpha <- newMetaTvT tau
        beta  <- newMetaTvT tau
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
        nu    <- newMetaTvT tau
        alpha <- newMetaTvT tau
        beta  <- newMetaTvT tau
        unifyTypes tau (stT (cT nu) alpha beta)
        return (nu, alpha, beta)

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

    unify (RefT tau1 _) (RefT tau2 _) =
        unify tau1 tau2

    unify (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify tau1a tau1b
        unify tau2a tau2b

    unify (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    unify (ST tau1a tau2a tau3a _) (ST tau1b tau2b tau3b _) = do
        unify tau1a tau1b
        unify tau2a tau2b
        unify tau3a tau3b

    unify (FunT taus1 tau1 _) (FunT taus2 tau2 _) | length taus1 == length taus2 = do
        zipWithM_ unify taus1 taus2
        unify tau1 tau2

    unify (NatI {}) (NatI {}) =
        return ()

    unify (C tau1 _) (C tau2 _) =
        unify tau1 tau2

    unify (T {}) (T {}) =
        unify tau1 tau2

    unify (ConstI i1 _) (ConstI i2 _)  | i1 == i2 =
        return ()

    unify (TyVarT tv1 _) (TyVarT tv2 _) | tv1 == tv2 =
        return ()

    unify tau1 tau2 =
        faildoc $ text "Expected type:" <+> ppr tau2 </>
                  text "but got:      " <+> ppr tau1

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
    fromZ Nothing    = newMetaTvT NoLoc

instance FromZ Z.Ind Type where
    fromZ (Z.ConstI i l) =
        pure $ ConstI i l

    fromZ (Z.ArrI v _) =
        lookupVar v >>= checkArrInd

    fromZ (Z.NoneI l) =
        newMetaTvT l

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
        go (UnitT l)             = C.UnitT <$> pure l
        go (BoolT l)             = C.BoolT <$> pure l
        go (BitT l)              = C.BitT <$> pure l
        go (IntT w l)            = C.IntT <$> trans w <*> pure l
        go (FloatT w l)          = C.FloatT <$> trans w <*> pure l
        go (ComplexT w l)        = C.ComplexT <$> trans w <*> pure l
        go (StringT l)           = pure $ C.StringT l
        go (RefT tau l)          = C.RefT <$> go tau <*> pure l
        go (ArrT i tau l)        = C.ArrT <$> trans i <*> go tau <*> pure l
        go (ST tau1 tau2 tau3 l) = C.ST <$> trans tau1 <*> go tau2 <*> go tau3 <*> pure l
        go (FunT taus tau l)     = C.FunT <$> pure [] <*> mapM go taus <*> go tau <*> pure l
        go tau                   = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core type"

instance Trans Type C.Omega where
    trans (C omega _) = C.C <$> trans omega
    trans (T _)       = pure C.T
    trans tau         = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core omega"

instance Trans Type C.Ind where
    trans (ConstI i l) = pure $ C.ConstI i l
    trans tau          = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core index"

instance Trans (Z.Var, Type) C.VarBind where
    trans (v, tau) = C.VarBind <$> trans v <*> trans tau
