{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Expr.Lint
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Expr.Lint (
    module KZC.Expr.Lint.Monad,

    Tc(..),
    runTc,
    liftTc,

    extendWildVars,

    checkProgram,

    checkDecls,

    inferConst,
    checkConst,

    inferExp,
    checkExp,

    refPath,

    checkStructDecl,
    checkStructUse,

    inferKind,
    checkKind,
    checkTauOrRhoKind,
    checkTyApp,

    checkCast,
    checkBitcast,

    checkTypeEquality,
    checkKindEquality,

    joinOmega,

    checkComplexT,
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

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (unless,
                      when,
                      zipWithM_,
                      void)
import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Primitive (PrimMonad(..),
                                RealWorld)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Foldable (traverse_)
import Data.IORef
import Data.List (nub)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.Mainland

import KZC.Check.Path
import KZC.Config
import KZC.Expr.Lint.Monad
import KZC.Expr.Smart
import KZC.Expr.Syntax
import KZC.Monad
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

newtype Tc a = Tc { unTc :: ReaderT TcEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TcEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadPlatform,
              MonadTrace)

instance MonadTc Tc where
    askTc     = Tc ask
    localTc f = Tc . local f . unTc

instance PrimMonad Tc where
    type PrimState Tc = RealWorld
    primitive = Tc . primitive

instance MonadTcRef Tc where

runTc :: Tc a -> TcEnv -> KZC a
runTc = runReaderT . unTc

-- | Run a 'Tc' computation in the 'KZC' monad with the current 'TcEnv'.
liftTc :: forall a . Tc a -> KZC a
liftTc m = do
    env <- asks tcenvref >>= readRef
    runTc m env

extendWildVars :: MonadTc m => [(WildVar, Type)] -> m a -> m a
extendWildVars wvs = extendVars [(v, tau) | (TameV v, tau) <- wvs]

checkProgram :: MonadTc m => Program -> m ()
checkProgram (Program _ decls) =
    checkDecls decls

checkDecls :: MonadTc m => [Decl] -> m ()
checkDecls = foldr checkDecl (return ())

checkDecl :: forall m a . MonadTc m => Decl -> m a -> m a
checkDecl decl@(StructD s tvks flds l) k = do
    alwaysWithSummaryContext decl $
        checkStructDecl s tvks flds
    extendStructs [StructDef s tvks flds l] k

checkDecl decl@(LetD v tau e _) k = do
    alwaysWithSummaryContext decl $ do
        void $ inferKind tau
        tau' <- withFvContext e $
                extendLet v tau $
                inferExp e >>= instST >>= genST
        checkTypeEquality tau' tau
    extendVars [(v, tau)] k

checkDecl decl@(LetRefD v tau Nothing _) k = do
    alwaysWithSummaryContext decl $ checkKind tau tauK
    extendVars [(v, refT tau)] k

checkDecl decl@(LetRefD v tau (Just e) _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau tauK
        checkExp e tau
    extendVars [(v, refT tau)] k

checkDecl decl@(LetFunD f tvks vbs tau_ret e l) k = do
    alwaysWithSummaryContext decl $ do
        checkNatTauPoly tvks
        checkKind tau PhiK
    extendVars [(f, tau)] $ do
      alwaysWithSummaryContext decl $ do
          tau_ret' <- extendLetFun f tvks vbs tau_ret $
                      withFvContext e $
                      inferExp e >>= genST
          checkTypeEquality tau_ret' tau_ret
      k
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

checkDecl decl@(LetExtFunD f tvks vbs tau_ret l) k = do
    alwaysWithSummaryContext decl $ do
        checkNatPoly tvks
        checkKind tau PhiK
    extendExtFuns [(f, tau)] k
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

-- | Check that we quantify only over type variables of kind Nat.
checkNatPoly :: forall m . MonadTc m => [Tvk] -> m ()
checkNatPoly tvks =
    extendTyVars tvks $
    mapM_ check tvks
  where
    check :: Tvk -> m ()
    check (alpha, kappa) = checkKind (tyVarT alpha) kappa

-- | Check that we quantify only over type variables of kind Tau or Nat.
checkNatTauPoly :: forall m . MonadTc m => [Tvk] -> m ()
checkNatTauPoly = mapM_ check
  where
    check :: Tvk -> m ()
    check (_alpha, TauK{}) =
        return ()

    check (_alpha, NatK) =
        return ()

    check (alpha, kappa) =
        withSummaryContext alpha $
        faildoc $
        text "Expected type-level nat or base type but got:" <+> ppr kappa

inferConst :: forall m . MonadTc m => SrcLoc -> Const -> m Type
inferConst l UnitC         = return (UnitT l)
inferConst l BoolC{}       = return (BoolT l)
inferConst l (FixC ip _)   = return (FixT ip l)
inferConst l (FloatC fp _) = return (FloatT fp l)
inferConst l (StringC _)   = return (StringT l)

inferConst l (ArrayC cs) = do
    taus <- V.mapM (inferConst l) cs
    when (V.null taus) $
      faildoc $ text "Empty array"
    let tau = V.head taus
    unless (V.all (== tau) (V.drop 1 taus)) $
      faildoc $ text "Constant array elements do not all have the same type"
    return $ ArrT (NatT (length cs) l) tau l

inferConst l (ReplicateC n c) = do
    tau <- inferConst l c
    return $ arrKnownT n tau

inferConst _ (EnumC tau) = do
    checkKind tau tauK
    w <- typeSize tau
    return $ arrKnownT (2^w) tau

inferConst l (StructC s taus flds) = do
    fdefs <- checkStructUse s taus (map fst flds)
    mapM_ (checkField fdefs) flds
    return $ StructT s taus l
  where
    checkField :: [(Field, Type)] -> (Field, Const) -> m ()
    checkField fldDefs (f, c) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc "checkField: missing field!"
               Just tau -> return tau
      checkConst l c tau

checkConst :: MonadTc m => SrcLoc -> Const -> Type -> m ()
checkConst l c tau = do
    tau' <- inferConst l c
    checkTypeEquality tau' tau

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
        mkSigned (FixT (U w) l) = FixT (I w) l
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

    unop (Cast tau2) tau1 = do
        checkCast tau1 tau2
        return tau2

    unop (Bitcast tau2) tau1 = do
        checkBitcast tau1 tau2
        return tau2

    unop Len tau = do
        _ <- checkArrOrRefArrT tau
        return intT

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
        inferCall tau_op [tau1] [e1]
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
        (iota1, tau1_elem) <- checkArrT tau1
        (iota2, tau2_elem) <- checkArrT tau2
        checkTypeEquality tau2_elem tau1_elem
        case (iota1, iota2) of
          (NatT n _, NatT m _) -> return $ ArrT (NatT (n+m) s) tau1_elem s
          _ -> faildoc $ text "Cannot determine type of concatenation of arrays of unknown length"
      where
        s :: SrcLoc
        s = tau1 `srcspan` tau2

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
        inferCall tau_op [tau1] [e1, e2]
      where
        tau_op :: Type
        tau_op = ForallT tvks (FunT [a, b] c l) l

inferExp (IfE e1 e2 e3 _) = do
    checkExp e1 boolT
    tau2 <- withFvContext e2 $ inferExp e2
    tau3 <- withFvContext e3 $ inferExp e3
    go tau2 tau3
  where
    -- If both branches are pureish, then we're good. Otherwise we need to make
    -- sure both branches have fully instantiated ST types.
    go :: Type -> Type -> m Type
    go tau2 tau3 | isPureishT tau2 && isPureishT tau3 = do
        withFvContext e3 $ checkTypeEquality tau3 tau2
        return tau2

    go tau2 tau3 = do
        tau2' <- withFvContext e2 $ instST tau2
        tau3' <- withFvContext e3 $ instST tau3
        withFvContext e3 $ checkTypeEquality tau3' tau2'
        return tau2'

inferExp (LetE decl body _) =
    withSummaryContext decl $
    checkDecl decl $ do
    tau <- inferExp body
    inferKind tau >>= checkLetKind
    return tau
  where
    checkLetKind :: Kind -> m ()
    checkLetKind TauK{} = return ()
    checkLetKind MuK    = return ()

    checkLetKind kappa =
      faildoc $ text "Body of let has kind" <+> ppr kappa

inferExp (CallE f taus es _) = do
    tau_f <- lookupVar f
    inferCall tau_f taus es

inferExp (DerefE e l) = do
    tau <- withFvContext e $ inferExp e >>= checkRefT
    return $ forallST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (AssignE e1 e2 l) = do
    tau  <- withSummaryContext e1 $ withFvContext e1 $ inferExp e1 >>= checkRefT
    tau' <- withSummaryContext e2 $ inferExp e2
    withFvContext e2 $ checkTypeEquality tau' tau
    return $ forallST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (WhileE e1 e2 _) = do
    withFvContext e1 $ do
        tau <- inferExp e1 >>= checkForallSTC
        checkTypeEquality tau boolT
    withFvContext e2 $ do
        tau <- inferExp e2
        void $ checkForallSTCUnit tau
        return tau

inferExp (ForE _ v tau int e _) = do
    checkKind tau intK
    traverse_ (\e -> withFvContext e $ checkExp e tau) int
    extendVars [(v, tau)] $
        withFvContext e $ do
        tau_body <- inferExp e
        void $ checkForallSTCUnit tau_body
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
        (s, taus) <- checkStructT tau
        sdef      <- lookupStruct s
        tau_f     <- checkStructFieldT sdef taus f
        return $ RefT tau_f l

    go tau = do
        (s, taus) <- checkStructT tau
        sdef      <- lookupStruct s
        checkStructFieldT sdef taus f

inferExp e0@(StructE s taus flds l) =
    withFvContext e0 $ do
    fdefs <- checkStructUse s taus (map fst flds)
    mapM_ (checkField fdefs) flds
    return $ StructT s taus l
  where
    checkField :: [(Field, Type)] -> (Field, Exp) -> m ()
    checkField fdefs (f, e) = do
      tau <- case lookup f fdefs of
               Nothing  -> panicdoc "checkField: missing field!"
               Just tau -> return tau
      checkExp e tau

inferExp (PrintE _ es l) = do
    mapM_ inferExp es
    instST $ forallST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (ErrorE nu _ l) =
    instST $ forallST [s,a,b] (C nu) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp (ReturnE _ e l) = do
    tau <- inferExp e
    return $ forallST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s = "s"
    a = "a"
    b = "b"

inferExp e@(BindE wv tau e1 e2 _) = do
    tau1 <- withFvContext e1 $ inferExp e1
    tau' <- withFvContext e1 $ checkForallSTC tau1
    withFvContext e $ checkTypeEquality tau' tau
    tau2 <- withFvContext e2 $
            extendWildVars [(wv, tau)] $
            inferExp e2
    go tau1 tau2
  where
    -- If both expressions being sequenced are pureish, then we're
    -- good. Otherwise we need to make sure they both have fully instantiated ST
    -- types.
    go :: Type -> Type -> m Type
    go tau1 tau2 | isPureishT tau1 && isPureishT tau2 =
        return tau2

    go tau1 tau2 = do
        tau1' <- withFvContext e1 $ instST tau1
        tau2' <- withFvContext e2 $ instST tau2
        (_, s,  a,  b) <- withFvContext e1 $
                          checkSTC tau1'
        withFvContext e2 $ do
            (omega, _, _, _) <- checkST tau2'
            checkTypeEquality tau2' (stT omega s a b)
        return tau2'

inferExp (TakeE tau l) = do
    checkKind tau tauK
    instST $ forallST [b] (C tau) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferExp (TakesE i tau l) = do
    checkKind tau tauK
    instST $ forallST [b] (C (arrKnownT i tau)) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferExp (EmitE e l) = do
    tau <- withFvContext e $ inferExp e
    instST $ forallST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s = "s"
    a = "a"

inferExp (EmitsE e l) = do
    (_, tau) <- withFvContext e $ inferExp e >>= checkArrT
    instST $ forallST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s = "s"
    a = "a"

inferExp (RepeatE _ e l) = do
    (s, a, b) <- withFvContext e $ inferExp e >>= instST >>= checkSTCUnit
    return $ forallST [] T s a b l

inferExp e0@(ParE _ b e1 e2 l) = do
    (s, a, c) <- askSTIndices
    (omega1, s', a',    b') <- withFvContext e1 $
                               localSTIndices (Just (s, a, b)) $
                               inferExp e1 >>= instST >>= checkST
    (omega2, b'', b''', c') <- withFvContext e2 $
                               localSTIndices (Just (b, b, c)) $
                               inferExp e2 >>= instST >>= checkST
    withFvContext e1 $
        checkTypeEquality (stT omega1 s'  a'   b') (stT omega1 s a b)
    withFvContext e2 $
        checkTypeEquality (stT omega2 b'' b''' c') (stT omega2 b b c)
    omega <- withFvContext e0 $
             joinOmega omega1 omega2
    return $ forallST [] omega s a c l

-- | Infer the type of a function call.
inferCall :: forall m . MonadTc m => Type -> [Type] -> [Exp] -> m Type
inferCall tau_f taus es = do
    (tvks, taus_args, tau_ret) <- checkFunT tau_f
    checkTyApp tvks taus
    checkNumArgs (length es) (length taus_args)
    extendTyVars tvks $ do
      zipWithM_ checkKind taus (map snd tvks)
      let theta      = Map.fromList (map fst tvks `zip` taus)
      let phi        = fvs taus_args <> fvs tau_ret
      let taus_args' = subst theta phi taus_args
      let tau_ret'   = subst theta phi tau_ret
      zipWithM_ checkArg es taus_args'
      unless (isPureishT tau_ret') $
          checkNoAliasing (es `zip` taus_args')
      return tau_ret'
  where
    -- The argument may not have a fully instantiated ST type even though the
    -- parameter is a fully instantiated ST type.
    checkArg :: Exp -> Type -> m ()
    checkArg e tau
        | isPureishT tau = withFvContext e $ checkExp e tau
        | otherwise      = withFvContext e $ do
                           tau' <- inferExp e >>= instST
                           checkTypeEquality tau tau'

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

-- | Check that a struct is not being re-defined.
checkStructNotRedefined :: MonadTc m => Struct -> m ()
checkStructNotRedefined s = do
    maybe_sdef <- maybeLookupStruct s
    case maybe_sdef of
      Nothing   -> return ()
      Just sdef -> faildoc $ text "Struct" <+> ppr s <+> text "redefined" <+>
                   parens (text "original definition at" <+> ppr (locOf sdef))

-- | Check a struct declaration.
checkStructDecl :: MonadTc m => Struct -> [Tvk] -> [(Field, Type)] -> m ()
checkStructDecl s tvks flds = do
    checkStructNotRedefined s
    checkDuplicates "field names" fnames
    extendTyVars tvks $
      mapM_ (`checkKind` tauK) taus
  where
    (fnames, taus) = unzip flds

-- | Check that a struct has no missing and no extra fields.
checkStructUse :: forall m . MonadTc m
               => Struct
               -> [Type]
               -> [Field]
               -> m [(Field, Type)]
checkStructUse struct taus flds = do
    sdef  <- lookupStruct struct
    checkStructTyApp sdef taus
    fdefs <- lookupStructFields struct taus
    checkMissingFields flds fdefs
    checkExtraFields flds fdefs
    return fdefs
  where
    checkMissingFields :: [Field] -> [(Field, Type)] -> m ()
    checkMissingFields flds fldDefs =
        unless (Set.null missing) $
          faildoc $
            text "Struct definition has missing fields:" <+>
            (commasep . map ppr . Set.toList) missing
      where
        fs, fs', missing :: Set Field
        fs  = Set.fromList flds
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        missing = fs Set.\\ fs'

    checkExtraFields :: [Field] -> [(Field, Type)] -> m ()
    checkExtraFields flds fldDefs =
        unless (Set.null extra) $
          faildoc $
            text "Struct definition has extra fields:" <+>
            (commasep . map ppr . Set.toList) extra
      where
        fs, fs', extra :: Set Field
        fs  = Set.fromList flds
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        extra = fs' Set.\\ fs

-- | Check a struct type application.
checkStructTyApp :: MonadTc m => StructDef -> [Type] -> m ()
checkStructTyApp (StructDef _ tvks _ _) taus =
    checkTyApp tvks taus

-- | @checkCast tau1 tau2@ checks that a value of type @tau1@ can be cast to a
-- value of type @tau2@.
checkCast :: forall m . MonadTc m => Type -> Type -> m ()
checkCast = go
  where
    go tau1 tau2 | tau1 == tau2 =
        return ()

    go FixT{} FixT{} =
        return ()

    go FixT{} FloatT{} =
        return ()

    go FloatT{} FixT{} =
        return ()

    go FloatT{} FloatT{} =
        return ()

    go tau1@FixT{} tau2@TyVarT{} =
        polyUpcast tau1 tau2

    go tau1@FloatT{} tau2@TyVarT{} =
        polyUpcast tau1 tau2

    go tau1 tau2 =
        cannotCast tau1 tau2

    -- | Polymorphic up-cast from type @tau1@ to type @tau2@. We use this to
    -- cast a constant to a polymorphic type.
    polyUpcast :: Type -> Type -> m ()
    polyUpcast tau1 tau2 = do
        kappa <- constKind tau1
        checkKind tau2 kappa `catch` \(_ :: SomeException) -> cannotCast tau1 tau2

    -- | Return the kind of constants of the given type. We use this to cast
    -- constants "polymorphically."
    constKind :: Type -> m Kind
    constKind FixT{}   = return numK
    constKind FloatT{} = return fracK
    constKind tau      = inferKind tau

    cannotCast :: Type -> Type -> m ()
    cannotCast tau1 tau2 =
        faildoc $ text "Cannot cast" <+> ppr tau1 <+> text "to" <+> ppr tau2

-- | @checkBitcast tau1 tau2@ checks that a value of type @tau1@ can be bitcast
-- to a value of type @tau2@.
checkBitcast :: MonadTc m => Type -> Type -> m ()
checkBitcast tau1 tau2 = do
    checkKind tau1 tauK
    checkKind tau2 tauK
    w1 <- typeSize tau1
    w2 <- typeSize tau2
    when (w2 /= w1) $
        faildoc $
        text "Cannot bitcast between types with differing widths" <+>
        ppr w1 <+> text "and" <+> ppr w2

-- | Check that @tau1@ is equal to @tau2@.
checkTypeEquality :: forall m . MonadTc m => Type -> Type -> m ()
checkTypeEquality tau1 tau2 =
    checkT Map.empty tau1 tau2
  where
    checkT :: Map TyVar TyVar
           -> Type
           -> Type
           -> m ()
    checkT _ UnitT{} UnitT{} = return ()
    checkT _ BoolT{} BoolT{} = return ()

    checkT _ (FixT ip _) (FixT ip' _) | ip' == ip =
        return ()

    checkT _ (FloatT fp _)  (FloatT fp' _) | fp' == fp =
        return ()

    checkT _ StringT{} StringT{} = return ()

    checkT theta (ArrT nat1 tau1 _) (ArrT nat2 tau2 _) = do
        checkT theta nat1 nat2
        checkT theta tau1 tau2

    checkT theta (StructT s1 taus1 _) (StructT s2 taus2 _) | s1 == s2 && length taus1 == length taus2 =
        zipWithM_ (checkT theta) taus1 taus2

    checkT theta (ST omega_a tau1_a tau2_a tau3_a _)
                 (ST omega_b tau1_b tau2_b tau3_b _) = do
          checkO theta  omega_a omega_b
          checkT theta tau1_a tau1_b
          checkT theta tau2_a tau2_b
          checkT theta tau3_a tau3_b

    checkT theta (FunT taus_a tau_a _)
                 (FunT taus_b tau_b _)
        | length taus_a == length taus_b = do
          zipWithM_ (checkT theta) taus_a taus_b
          checkT theta tau_a tau_b

    checkT theta (RefT tau1 _) (RefT tau2 _) =
        checkT theta tau1 tau2

    checkT theta (TyVarT alpha _) (TyVarT beta _)
        | fromMaybe alpha (Map.lookup alpha theta) == beta =
        return ()

    checkT _ (NatT n1 _) (NatT n2 _) | n2 == n1 =
        return ()

    checkT theta (ForallT tvks1 tau1 _) (ForallT tvks2 tau2 _)
        | length tvks1 == length tvks2 = do
          zipWithM_ checkKindEquality (map snd tvks1) (map snd tvks2)
          checkT theta' tau1 tau2
      where
        theta' :: Map TyVar TyVar
        theta' = Map.fromList (map fst tvks1 `zip` map fst tvks2) `Map.union` theta

    checkT _ _ _ =
        err

    checkO :: Map TyVar TyVar
           -> Omega
           -> Omega
           -> m ()
    checkO theta (C tau1) (C tau2) =
        checkT theta tau1 tau2

    checkO _ T{} T{} =
        return ()

    checkO _ _ _ =
        err

    err :: m ()
    err = expectedTypeErr tau1 tau2

-- | Throw a "Expected type.." error. @tau1@ is the type we got, and @tau2@ is
-- the expected type.
expectedTypeErr :: MonadTc m => Type -> Type -> m a
expectedTypeErr tau1 tau2 = do
    msg <- relevantBindings
    faildoc $ align $
      text "Expected type:" <+> ppr tau2 </>
      text "but got:      " <+> ppr tau1 <>
      msg

-- Must be kept in sync with 'KZC.Check.kcType'
inferKind :: forall m . MonadTc m => Type -> m Kind
inferKind = inferType
  where
    inferType :: Type -> m Kind
    inferType UnitT{} =
        return $ qualK [EqR]

    inferType BoolT{} =
        return $ qualK [EqR, OrdR, BoolR]

    inferType (FixT (U 1) _) =
        return $ qualK [EqR, OrdR, BoolR, BitsR]

    inferType (FixT UDefault _) =
        return $ qualK [EqR, OrdR, NumR, IntegralR, BitsR]

    inferType (FixT U{} _) =
        return $ qualK [EqR, OrdR, NumR, IntegralR, BitsR]

    inferType (FixT IDefault _) =
        return $ qualK [EqR, OrdR, NumR, IntegralR]

    inferType (FixT I{} _) =
        return $ qualK [EqR, OrdR, NumR, IntegralR]

    inferType FloatT{} =
        return $ qualK [EqR, OrdR, NumR, FractionalR]

    inferType StringT{} =
        return tauK

    inferType tau_struct@(StructT s taus _) = do
        StructDef _ tvks _ _ <- lookupStruct s
        checkTyApp tvks taus
        maybe_tau <- runMaybeT $ checkComplexT tau_struct
        case maybe_tau of
          -- A struct has traits Eq, Ord, and Num if its elements do.
          Just tau -> do kappa <- inferKind tau
                         case kappa of
                           TauK ts -> return $ TauK (ts `intersectTraits` traits [EqR, OrdR, NumR])
                           _       -> return tauK
          Nothing  -> return tauK

    inferType (ArrT n tau _) = do
        checkKind n NatK
        kappa <- inferType tau
        checkKindImplies kappa tauK
        return tauK

    inferType (ST omega tau1 tau2 tau3 _) = do
        void $ inferOmega omega
        checkKind tau1 tauK
        checkKind tau2 tauK
        checkKind tau3 tauK
        return MuK

    inferType (RefT tau _) = do
        checkKind tau tauK
        return RhoK

    inferType (FunT taus tau_ret _) = do
        mapM_ (checkArgKind (isPureishT tau_ret)) taus
        checkRetKind tau_ret
        return PhiK
      where
        -- If a function is pureish, i.e., it performs no takes or emits, then
        -- it may not take a computation as an argument, i.e., it may have an
        -- argument that is a computation, but that argument must itself then be
        -- pureish.
        checkArgKind :: Bool -> Type -> m ()
        checkArgKind pureish tau = do
            kappa <- inferType tau
            case kappa of
              TauK{}          -> return ()
              RhoK            -> return ()
              MuK | pureish   -> checkPureish tau
                  | otherwise -> return ()
              _               -> checkKindImplies kappa tauK

        checkRetKind :: Type -> m ()
        checkRetKind tau = do
            kappa <- inferType tau
            case kappa of
              TauK{} -> return ()
              MuK    -> return ()
              _      -> checkKindImplies kappa tauK

    inferType NatT{} =
        return NatK

    inferType (ForallT tvks tau _) =
        extendTyVars tvks $
        inferType tau

    inferType (TyVarT alpha _) =
        lookupTyVar alpha

    inferOmega :: Omega -> m Kind
    inferOmega (C tau) = do
        checkKind tau tauK
        return OmegaK

    inferOmega T =
        return OmegaK

checkKind :: MonadTc m => Type -> Kind -> m ()
checkKind tau kappa = do
    kappa' <- inferKind tau
    checkKindImplies kappa' kappa

checkTauOrRhoKind :: forall m . MonadTc m => Type -> m ()
checkTauOrRhoKind tau =
    inferKind tau >>= go
  where
    go :: Kind -> m ()
    go TauK{} = return ()
    go RhoK   = return ()
    go kappa  = faildoc $ text "Expected tau or rho kind but got:" <+> ppr kappa

checkTyApp :: forall m . MonadTc m => [Tvk] -> [Type] -> m ()
checkTyApp tvks taus = do
    checkNumTypeArgs (length taus) (length tvks)
    zipWithM_ (\(_alpha, kappa) tau -> checkKind tau kappa) tvks taus
  where
    checkNumTypeArgs :: Int -> Int -> m ()
    checkNumTypeArgs ntaus ntvks =
        when (ntaus /= ntvks) $
        faildoc $
        text "Expected" <+> ppr ntvks <+>
        text "type arguments but got" <+> ppr ntaus </> ppr tvks </> ppr taus

checkKindEquality :: MonadTc m => Kind -> Kind -> m ()
checkKindEquality kappa1 kappa2 | kappa1 == kappa2 =
    return ()

checkKindEquality kappa1 kappa2 =
    faildoc $ align $
    text "Expected kind:" <+> ppr kappa2 </>
    text "but got:      " <+> ppr kappa1

-- | Check that the first kind implies the second.
checkKindImplies :: MonadTc m => Kind -> Kind -> m ()
checkKindImplies (TauK ts1) (TauK ts2) = do
    unless (ts1 `impliesTraits` ts2) $
      faildoc $ align $
      text "Expected traits:" <+> pprTraits ts2 </>
      text "but got:        " <+> pprTraits ts1
  where
    pprTraits :: Traits -> Doc
    pprTraits ts
      | nullTraits ts = text "no traits"
      | otherwise     = ppr ts

checkKindImplies kappa1 kappa2 =
    checkKindEquality kappa1 kappa2

-- | Check that two omega types can be joined.
joinOmega :: MonadTc m => Omega -> Omega -> m Omega
joinOmega omega1@C{} T{}        = return omega1
joinOmega T{}        omega2@C{} = return omega2
joinOmega omega1@T{} T{}        = return omega1

joinOmega omega1 omega2 =
    faildoc $ text "Cannot join" <+> ppr omega1 <+> text "and" <+> ppr omega2

-- | Check that a type is a complex type, returning the type of its constituent
-- fields. A complex type has two fields named "re" and "im", in that order, and
-- both fields must have the same type.
checkComplexT :: MonadTc m => Type -> m Type
checkComplexT (StructT struct taus _) = do
    flds <- lookupStructFields struct taus
    case flds of
      [("re", tau), ("im", tau')] | tau' == tau -> return tau
      _                                         -> fail "Not a complex type"

checkComplexT _ =
    fail "Not a complex type"

-- | Check that a type is an @arr \iota \alpha@ type, returning @\iota@ and
-- @\alpha@.
checkArrT :: MonadTc m => Type -> m (Type, Type)
checkArrT (ArrT nat alpha _) = do
    checkKind nat NatK
    return (nat, alpha)

checkArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

-- | Check that a type is an array of known length, returning the length and
--the type of the array elements
checkKnownArrT :: forall m . MonadTc m => Type -> m (Int, Type)
checkKnownArrT tau =
    checkArrT tau >>= go
  where
    go :: (Type, Type) -> m (Int, Type)
    go (NatT n _, tau) =
        return (n, tau)

    go _ =
         faildoc $ text "Array type" <+> ppr tau <+>
                   text "does not have known length."

-- | Check that the argument is either an array or a reference to an array and
-- return the array's size and the type of its elements.
checkArrOrRefArrT :: Monad m => Type -> m (Type, Type)
checkArrOrRefArrT (ArrT n tau _) =
    return (n, tau)

checkArrOrRefArrT (RefT (ArrT n tau _) _) =
    return (n, tau)

checkArrOrRefArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

-- | Check that a type is a struct type, returning the name of the struct.
checkStructT :: MonadTc m => Type -> m (Struct, [Type])
checkStructT (StructT s taus _) = do
    sdef <- lookupStruct s
    checkStructTyApp sdef taus
    return (s, taus)

checkStructT tau =
    faildoc $ nest 2 $
    text "Expected struct type, but got:" <+/> ppr tau

-- | Check that a type is a struct or struct reference type, returning the name
-- of the struct.
checkStructOrRefStructT :: MonadTc m => Type -> m (Struct, [Type])
checkStructOrRefStructT (StructT s taus _)          = return (s, taus)
checkStructOrRefStructT (RefT (StructT s taus _) _) = return (s, taus)
checkStructOrRefStructT tau =
    faildoc $ nest 2 $
    text "Expected struct type, but got:" <+/> ppr tau

checkStructFieldT :: MonadTc m => StructDef -> [Type] -> Field -> m Type
checkStructFieldT sdef@(StructDef s _ _ _) taus f = do
    flds <- tyAppStruct sdef taus
    case lookup f flds of
      Just tau -> return tau
      Nothing ->
          faildoc $
          text "Struct" <+> ppr s <+>
          text "does not have a field named" <+> ppr f

checkRefT :: MonadTc m => Type -> m Type
checkRefT (RefT tau _) =
    return tau

checkRefT tau =
    faildoc $ nest 2 $ group $
    text "Expected ref type but got:" <+/> ppr tau

checkFunT :: MonadTc m => Type -> m ([Tvk], [Type], Type)
checkFunT (ForallT tvks (FunT taus tau_ret _) _) =
    return (tvks, taus, tau_ret)

checkFunT (FunT taus tau_ret _) =
    return ([], taus, tau_ret)

checkFunT tau =
    faildoc $ nest 2 $ group $
    text "Expected function type but got:" <+/> ppr tau

{- Note [The ST type]

The ST type represents unpure computations and has the form forall a ..., ST
omega tau tau tau. It can distinguish between computations that use references,
computations that take, and computations that emit. For example

  forall s a b . ST (C ()) s a b

is the type of a computation that may use references but returns unit. We term
computations that may use references but that do not take or emit "pureish."

  forall a b . ST (C ()) a a b

is the type of a computation that takes something and throws it away but does
not emit.

  forall s a int . ST (C ()) s a int

is the type of a computation that only emits values of type int.

The omega can be either C tau, for a computation that returns a value of type
tau, or T, for a transformer.

The ST type provides a very limited form of polymorphism. To avoid type
abstraction and application, we keep track of the current "ST typing context,"
which consist of the three ST index types. Whenever we type check a value with
an ST type, we immediately instantiate it by applying it to the current ST
context using the function 'instST'.

In the core language, we differentiate syntactically between expressions, which
may be pure or pureish, and computations that take and emit. In that language,
we /do not/ instantiate ST types immediately in the expression language.
Instead, we must instantiate any ST types when they become part of a
computation.
-}

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context.
withInstantiatedTyVars :: MonadTc m => Type -> m a -> m a
withInstantiatedTyVars tau@(ForallT tvks (ST _ s a b _) _) k = do
    ST _ s' a' b' _ <- instST tau
    extendTyVarTypes [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b'], alpha `elem` alphas] k
  where
    alphas :: [TyVar]
    alphas = map fst tvks

withInstantiatedTyVars _tau k =
    k

-- | Generalize an ST type.
genST :: forall m . MonadTc m => Type -> m Type
genST (ST omega s a b l) = do
    -- We can't quantify over in-scope type variables *except* those that the
    -- current ST type already quantifies over.
    tvs        <- (Set.\\) <$> inScopeTyVars <*> askSTTyVars
    (s',a',b') <- askSTIndices
    let alphas =  nub [alpha | TyVarT alpha _ <- [s',a',b'], alpha `Set.notMember` tvs]
    kappas     <- mapM lookupTyVar alphas
    case alphas `zip` kappas of
      []   -> return $ ST omega s a b l
      tvks -> return $ ForallT tvks (ST omega s a b l) l

genST tau =
    return tau

-- | Instantiate an ST type.
instST :: MonadTc m => Type -> m Type
instST tau@(ForallT tvks (ST omega s a b l) _) = do
    (s',a',b') <- askSTIndices
    let theta  = Map.fromList [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']
                                            , alpha `elem` alphas]
    let phi    = fvs tau
    return $ subst theta phi $ ST omega s a b l
  where
    alphas :: [TyVar]
    alphas = map fst tvks

instST tau =
    return tau

checkForallSTC :: MonadTc m => Type -> m Type
checkForallSTC (ForallT _ tau _) =
    checkForallSTC tau

checkForallSTC (ST (C tau) _ _ _ _) =
    return tau

checkForallSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C tau) s a b' but got:" </> ppr tau

checkForallSTCUnit :: MonadTc m => Type -> m ()
checkForallSTCUnit (ForallT _ tau _) =
    checkForallSTCUnit tau

checkForallSTCUnit (ST (C (UnitT _)) _ _ _ _) =
    return ()

checkForallSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C ()) s a b' but got:" <+/> ppr tau

checkST :: MonadTc m => Type -> m (Omega, Type, Type, Type)
checkST (ST omega s a b _) =
    return (omega, s, a, b)

checkST tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST omega s a b' but got:" <+/> ppr tau

checkSTC :: MonadTc m => Type -> m (Type, Type, Type, Type)
checkSTC (ST (C tau) s a b _) =
    return (tau, s, a, b)

checkSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C tau) s a b' but got:" </> ppr tau

checkSTCUnit :: MonadTc m => Type -> m (Type, Type, Type)
checkSTCUnit (ST (C (UnitT _)) s a b _) =
    return (s, a, b)

checkSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C ()) s a b' but got:" <+/> ppr tau

checkPure :: MonadTc m => Type -> m ()
checkPure tau@ST{} =
    faildoc $ nest 2 $ group $
    text "Expected pure type got:" <+/> ppr tau

checkPure _ =
    return ()

checkPureish :: MonadTc m => Type -> m ()
checkPureish tau@ST{} = void $ checkPureishST tau
checkPureish _        = return ()

checkPureishST :: MonadTc m => Type -> m ([TyVar], Omega, Type, Type, Type)
checkPureishST tau@(ForallT tvks (ST omega s a b _) _) | isPureishT tau =
    return (map fst tvks, omega, s, a, b)

checkPureishST tau@(ST omega s a b _) | isPureishT tau =
    return ([], omega, s, a, b)

checkPureishST tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST omega s a b' but got:" <+/> ppr tau

checkPureishSTC :: MonadTc m => Type -> m ([TyVar], Type, Type, Type, Type)
checkPureishSTC tau0@(ForallT tvks (ST (C tau) s a b _) _) | isPureishT tau0 =
    return (map fst tvks, tau, s, a, b)

checkPureishSTC tau0@(ST (C tau) s a b _) | isPureishT tau0 =
    return ([], tau, s, a, b)

checkPureishSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST (C tau) s a b' but got:" </> ppr tau

checkPureishSTCUnit :: MonadTc m => Type -> m ([TyVar], Type, Type, Type)
checkPureishSTCUnit tau@(ForallT tvks (ST (C (UnitT _)) s a b _) _) | isPureishT tau =
    return (map fst tvks, s, a, b)

checkPureishSTCUnit tau@(ST (C (UnitT _)) s a b _) | isPureishT tau =
    return ([], s, a, b)

checkPureishSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST (C ()) s a b' but got:" <+/> ppr tau
