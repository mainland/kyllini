{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Lint
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Core.Lint (
    module KZC.Core.Lint.Monad,

    Tc(..),
    runTc,
    liftTc,
    withTc,

    extendWildVars,

    checkDecls,

    inferConst,
    checkConst,

    inferExp,
    checkExp,

    refPath,

    inferKind,
    checkKind,

    checkCast,
    checkBitcast,

    checkTypeEquality,
    checkKindEquality,

    checkEqT,
    checkOrdT,
    checkBoolT,
    checkBitT,
    checkIntT,
    checkNumT,
    checkArrT,
    checkArrOrRefArrT,
    checkStructT,
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
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (unless,
                      when,
                      zipWithM_,
                      void)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Data.IORef
import Data.List (nub)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ratio (numerator)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Check.Path
import KZC.Core.Lint.Monad
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Summary
import KZC.Trace
import KZC.Uniq
import KZC.Vars

newtype Tc a = Tc { unTc :: ReaderT TcEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader TcEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

instance MonadTc Tc where
    askTc       = Tc $ ask
    localTc f m = Tc $ local f (unTc m)

runTc :: Tc a -> TcEnv -> KZC a
runTc m r = (runReaderT . unTc) m r

-- | Run a 'Tc' computation in the 'KZC' monad and update the 'TcEnv'.
liftTc :: forall a . Tc a -> KZC a
liftTc m = do
    eref <- asks tcenvref
    env  <- readRef eref
    runTc (m' eref) env
  where
    m' :: IORef TcEnv -> Tc a
    m' eref = do
        x <- m
        askTc >>= writeRef eref
        return x

-- | Run a 'Tc' computation in the 'KZC' monad but /do not/ update the 'TcEnv'.
withTc :: forall a . Tc a -> KZC a
withTc m = do
    env <- asks tcenvref >>= readRef
    runTc m env

extendWildVars :: MonadTc m => [(WildVar, Type)] -> m a -> m a
extendWildVars wvs m =
    extendVars [(v, tau) | (TameV v, tau) <- wvs] m

checkDecls :: MonadTc m => [Decl] -> m ()
checkDecls [] =
    return ()

checkDecls (decl:decls) =
    checkDecl  decl $
    checkDecls decls

checkDecl :: forall m a . MonadTc m => Decl -> m a -> m a
checkDecl decl@(LetD v tau e _) k = do
    alwaysWithSummaryContext decl $ do
        void $ inferKind tau
        tau' <- withFvContext e $
                extendLet v tau $
                inferExp e >>= appSTScope >>= absSTScope
        checkTypeEquality tau' tau
    extendVars [(v, tau)] k

checkDecl decl@(LetRefD v tau Nothing _) k = do
    alwaysWithSummaryContext decl $ checkKind tau TauK
    extendVars [(v, refT tau)] k

checkDecl decl@(LetRefD v tau (Just e) _) k = do
    alwaysWithSummaryContext decl $
        inLocalScope $ do
        checkKind tau TauK
        checkExp e tau
    extendVars [(v, refT tau)] k

checkDecl decl@(LetFunD f ivs vbs tau_ret e l) k = do
    alwaysWithSummaryContext decl $
        checkKind tau PhiK
    extendVars [(f, tau)] $ do
    alwaysWithSummaryContext decl $ do
        tau_ret' <- extendLetFun f ivs vbs tau_ret $
                    withFvContext e $
                    inferExp e >>= absSTScope
        checkTypeEquality tau_ret' tau_ret
    k
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

checkDecl decl@(LetExtFunD f ivs vbs tau_ret l) k = do
    alwaysWithSummaryContext decl $ checkKind tau PhiK
    extendExtFuns [(f, tau)] k
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

checkDecl decl@(LetStructD s flds l) k = do
    alwaysWithSummaryContext decl $ do
        checkStructNotRedefined s
        checkDuplicates "field names" fnames
        mapM_ (\tau -> checkKind tau TauK) taus
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

inferConst :: forall m . MonadTc m => SrcLoc -> Const -> m Type
inferConst l UnitC              = return (UnitT l)
inferConst l (BoolC {})         = return (BoolT l)
inferConst l (FixC sc s w bp _) = return (FixT sc s w bp l)
inferConst l (FloatC w _)       = return (FloatT w l)
inferConst l (StringC _)        = return (StringT l)

inferConst l (ArrayC cs) = do
    taus <- mapM (inferConst l) cs
    case taus of
      [] -> faildoc $ text "Empty array"
      tau:taus | all (== tau) taus -> return $ ArrT (ConstI (length cs) l) tau l
               | otherwise -> faildoc $ text "Constant array elements do not all have the same type"

inferConst l (StructC s flds) = do
    fldDefs <- checkStructFields s (map fst flds)
    mapM_ (checkField fldDefs) flds
    return $ StructT s l
  where
    checkField :: [(Field, Type)] -> (Field, Const) -> m ()
    checkField fldDefs (f, c) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc $ "checkField: missing field!"
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
        mkSigned (FixT sc _ w bp l) = FixT sc S w bp l
        mkSigned tau                = tau

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
          (ConstI n _, ConstI m _) -> return $ ArrT (ConstI (n+m) s) tau1_elem s
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
        checkIntT tau2
        return tau1

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
        tau2' <- withFvContext e2 $ appSTScope tau2
        tau3' <- withFvContext e3 $ appSTScope tau3
        withFvContext e3 $ checkTypeEquality tau3' tau2'
        return tau2'

inferExp (LetE decl body _) =
    checkDecl decl $ inferExp body

inferExp (CallE f ies es _) = do
    (ivs, taus, tau_ret) <- lookupVar f >>= checkFunT
    checkNumIotas (length ies) (length ivs)
    checkNumArgs  (length es)  (length taus)
    extendIVars (ivs `zip` repeat IotaK) $ do
    mapM_ checkIotaArg ies
    let theta = Map.fromList (ivs `zip` ies)
    let phi   = fvs taus
    zipWithM_ checkArg es (subst theta phi taus)
    unless (isPureishT tau_ret) $
        checkNoAliasing (es `zip` taus)
    return $ subst theta phi tau_ret
  where
    checkIotaArg :: Iota -> m ()
    checkIotaArg (ConstI {}) =
        return ()

    checkIotaArg (VarI iv _) =
        void $ lookupIVar iv

    -- The argument may not have a fully instantiated ST type even though the
    -- parameter is a fully instantiated ST type.
    checkArg :: Exp -> Type -> m ()
    checkArg e tau
        | isPureishT tau = withFvContext e $ checkExp e tau
        | otherwise      = withFvContext e $ do
                           tau' <- inferExp e >>= appSTScope
                           checkTypeEquality tau tau'

    checkNumIotas :: Int -> Int -> m ()
    checkNumIotas n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "index expression arguments but got" <+> ppr n

    checkNumArgs :: Int -> Int -> m ()
    checkNumArgs n nexp =
        when (n /= nexp) $
             faildoc $
             text "Expected" <+> ppr nexp <+>
             text "arguments but got" <+> ppr n

inferExp (DerefE e l) = do
    tau <- withFvContext e $ inferExp e >>= checkRefT
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
    s = "s"
    a = "a"
    b = "b"

inferExp (AssignE e1 e2 l) = do
    tau  <- withFvContext e1 $ inferExp e1 >>= checkRefT
    tau' <- inferExp e2
    withFvContext e2 $ checkTypeEquality tau' tau
    return $ ST [s,a,b] (C (UnitT l)) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
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

inferExp (ForE _ v tau e1 e2 e3 _) = do
    checkIntT tau
    withFvContext e1 $
        checkExp e1 tau
    withFvContext e2 $
        checkExp e2 tau
    extendVars [(v, tau)] $
        withFvContext e3 $ do
        tau_body <- inferExp e3
        void $ checkForallSTCUnit tau_body
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
    go :: Type -> m Type
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
    go :: Type -> m Type
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
    fldDefs <- checkStructFields s (map fst flds)
    mapM_ (checkField fldDefs) flds
    return $ StructT s l
  where
    checkField :: [(Field, Type)] -> (Field, Exp) -> m ()
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc $ "checkField: missing field!"
               Just tau -> return tau
      checkExp e tau

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
    return $ ST [s,a,b] (C tau) (tyVarT s) (tyVarT a) (tyVarT b) l
  where
    s, a, b :: TyVar
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
        tau1' <- withFvContext e1 $ appSTScope tau1
        tau2' <- withFvContext e2 $ appSTScope tau2
        (_, s,  a,  b) <- withFvContext e1 $
                          checkSTC tau1'
        withFvContext e2 $ do
            (omega, _, _, _) <- checkST tau2'
            checkTypeEquality tau2' (stT omega s a b)
        return tau2'

inferExp (TakeE tau l) = do
    checkKind tau TauK
    appSTScope $ ST [b] (C tau) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferExp (TakesE i tau l) = do
    checkKind tau TauK
    appSTScope $ ST [b] (C (arrKnownT i tau)) tau tau (tyVarT b) l
  where
    b :: TyVar
    b = "b"

inferExp (EmitE e l) = do
    tau <- withFvContext e $ inferExp e
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

inferExp (EmitsE e l) = do
    (_, tau) <- withFvContext e $ inferExp e >>= checkArrT
    appSTScope $ ST [s,a] (C (UnitT l)) (tyVarT s) (tyVarT a) tau l
  where
    s, a :: TyVar
    s = "s"
    a = "a"

inferExp (RepeatE _ e l) = do
    (s, a, b) <- withFvContext e $ inferExp e >>= appSTScope >>= checkSTCUnit
    return $ ST [] T s a b l

inferExp e0@(ParE _ b e1 e2 l) = do
    (s, a, c) <- askSTIndTypes
    (omega1, s', a',    b') <- withFvContext e1 $
                               localSTIndTypes (Just (s, a, b)) $
                               inferExp e1 >>= appSTScope >>= checkST
    (omega2, b'', b''', c') <- withFvContext e2 $
                               localSTIndTypes (Just (b, b, c)) $
                               inferExp e2 >>= appSTScope >>= checkST
    withFvContext e1 $
        checkTypeEquality (stT omega1 s'  a'   b') (stT omega1 s a b)
    withFvContext e2 $
        checkTypeEquality (stT omega2 b'' b''' c') (stT omega2 b b c)
    omega <- withFvContext e0 $
             joinOmega omega1 omega2
    return $ ST [] omega s a c l
  where
    joinOmega :: Omega -> Omega -> m Omega
    joinOmega omega1@(C {}) (T {})        = return omega1
    joinOmega (T {})        omega2@(C {}) = return omega2
    joinOmega omega1@(T {}) (T {})        = return omega1

    joinOmega omega1 omega2 =
        faildoc $ text "Cannot join" <+> ppr omega1 <+> text "and" <+> ppr omega2

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

    go (IdxE e (ConstE (FixC I _ _ 0 r) _) Nothing _) path =
        go e (IdxP (fromIntegral (numerator r)) 1 : path)

    go (IdxE e (ConstE (FixC I _ _ 0 r) _) (Just len) _) path =
        go e (IdxP (fromIntegral (numerator r)) len : path)

    go (IdxE e _ _ _) _ =
        go e []

    go (ProjE e f _) path =
        go e (ProjP f : path)

    go e _ =
        faildoc $ text "refPath: Not a reference:" <+> ppr e

-- | Check that a struct has no missing and no extra fields.
checkStructFields :: forall m . MonadTc m
                  => Struct
                  -> [Field]
                  -> m [(Field, Type)]
checkStructFields s flds = do
    StructDef _ fldDefs _ <- lookupStruct s
    checkMissingFields flds fldDefs
    checkExtraFields flds fldDefs
    return fldDefs
  where
    checkMissingFields :: [Field] -> [(Field, Type)] -> m ()
    checkMissingFields flds fldDefs =
        when (not (Set.null missing)) $
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
        when (not (Set.null extra)) $
          faildoc $
            text "Struct definition has extra fields:" <+>
            (commasep . map ppr . Set.toList) extra
      where
        fs, fs', extra :: Set Field
        fs  = Set.fromList flds
        fs' = Set.fromList [f | (f,_) <- fldDefs]
        extra = fs' Set.\\ fs

-- | @checkCast tau1 tau2@ checks that a value of type @tau1@ can be cast to a
-- value of type @tau2@.
checkCast :: MonadTc m => Type -> Type -> m ()
checkCast tau1 tau2 | tau1 == tau2 =
    return ()

checkCast (FixT {}) (FixT {}) =
    return ()

checkCast (FixT {}) (FloatT {}) =
    return ()

checkCast (FloatT {}) (FixT {}) =
    return ()

checkCast (FloatT {}) (FloatT {}) =
    return ()

checkCast tau1 tau2 | isComplexT tau1 && isComplexT tau2 =
    return ()

checkCast tau1 tau2 =
    faildoc $ text "Cannot cast" <+> ppr tau1 <+> text "to" <+> ppr tau2

-- | @checkBitcast tau1 tau2@ checks that a value of type @tau1@ can be bitcast to
-- a value of type @tau2@.
checkBitcast :: MonadTc m => Type -> Type -> m ()
checkBitcast tau1 tau2 = do
    w1 <- typeSize tau1
    w2 <- typeSize tau2
    when (w2 /= w1) $
        faildoc $
        text "Cannot bitcast between types with differing widths" <+>
        ppr w1 <+> text "and" <+> ppr w2

-- | Check that @tau1@ is equal to @tau2@.
checkTypeEquality :: forall m . MonadTc m => Type -> Type -> m ()
checkTypeEquality tau1 tau2 =
    checkT Map.empty Map.empty tau1 tau2
  where
    checkT :: Map TyVar TyVar
           -> Map IVar IVar
           -> Type
           -> Type
           -> m ()
    checkT _ _ (UnitT {}) (UnitT {}) = return ()
    checkT _ _ (BoolT {}) (BoolT {}) = return ()

    checkT _ _ (FixT sc1 s1 w1 bp1 _) (FixT sc2 s2 w2 bp2 _)
        | sc1 == sc2 && s1 == s2 && w1 == w2 && bp1 == bp2 = return ()

    checkT _ _ (FloatT w1 _)  (FloatT w2 _)
        | w1 == w2 = return ()

    checkT _ _ (StringT {}) (StringT {}) = return ()

    checkT theta phi (ArrT iota1 tau1 _) (ArrT iota2 tau2 _) = do
        checkI phi iota1 iota2
        checkT theta phi tau1 tau2

    checkT _ _ (StructT s1 _) (StructT s2 _) | s1 == s2 =
        return ()

    checkT theta phi (ST alphas_a omega_a tau1_a tau2_a tau3_a _)
                     (ST alphas_b omega_b tau1_b tau2_b tau3_b _)
        | length alphas_a == length alphas_b = do
          checkO theta  phi omega_a omega_b
          checkT theta' phi tau1_a tau1_b
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
           -> m ()
    checkO theta phi (C tau1) (C tau2) =
        checkT theta phi tau1 tau2

    checkO _ _ (T {}) (T {}) =
        return ()

    checkO _ _ _ _ =
        err

    checkI :: Map IVar IVar
           -> Iota
           -> Iota
           -> m ()
    checkI _ (ConstI i1 _) (ConstI i2 _) | i1 == i2 =
        return ()

    checkI phi (VarI iv1 _) (VarI iv2 _)
        | fromMaybe iv1 (Map.lookup iv1 phi) == iv2 =
        return ()

    checkI _ _ _ =
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

inferKind :: forall m . MonadTc m => Type -> m Kind
inferKind tau =
    inferType tau
  where
    inferType :: Type -> m Kind
    inferType (UnitT {})   = return TauK
    inferType (BoolT {})   = return TauK
    inferType (FixT {})    = return TauK
    inferType (FloatT {})  = return TauK
    inferType (StringT {}) = return TauK
    inferType (StructT {}) = return TauK

    inferType (ArrT iota tau _) = do
        void $ inferIota iota
        kappa <- inferType tau
        checkKindEquality kappa TauK
        return TauK

    inferType (ST alphas omega tau1 tau2 tau3 _) =
        extendTyVars (alphas `zip` repeat TauK) $ do
        void $ inferOmega omega
        checkKind tau1 TauK
        checkKind tau2 TauK
        checkKind tau3 TauK
        return MuK

    inferType (RefT tau _) = do
        checkKind tau TauK
        return RhoK

    inferType (FunT ivs taus tau_ret _) =
        extendIVars (ivs `zip` repeat IotaK) $ do
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
              TauK            -> return ()
              RhoK            -> return ()
              MuK | pureish   -> checkPureish tau
                  | otherwise -> return ()
              _               -> checkKindEquality kappa TauK

        checkRetKind :: Type -> m ()
        checkRetKind tau = do
            kappa <- inferType tau
            case kappa of
              TauK -> return ()
              MuK  -> return ()
              _    -> checkKindEquality kappa TauK

    inferType (TyVarT alpha _) =
        lookupTyVar alpha

    inferIota :: Iota -> m Kind
    inferIota (ConstI {}) = return IotaK
    inferIota (VarI iv _) = lookupIVar iv

    inferOmega :: Omega -> m Kind
    inferOmega (C tau) = do
        checkKind tau TauK
        return OmegaK

    inferOmega T =
        return OmegaK

checkKind :: MonadTc m => Type -> Kind -> m ()
checkKind tau kappa = do
    kappa' <- inferKind tau
    checkKindEquality kappa' kappa

checkKindEquality :: MonadTc m => Kind -> Kind -> m ()
checkKindEquality kappa1 kappa2 | kappa1 == kappa2 =
    return ()

checkKindEquality kappa1 kappa2 =
    faildoc $ align $
    text "Expected kind:" <+> ppr kappa2 </>
    text "but got:      " <+> ppr kappa1

-- | Check that a type supports equality.
checkEqT :: MonadTc m => Type -> m ()
checkEqT tau =
    checkKind tau TauK

-- | Check that a type supports ordering.
checkOrdT :: MonadTc m => Type -> m ()
checkOrdT (FixT {})   = return ()
checkOrdT (FloatT {}) = return ()
checkOrdT tau =
    faildoc $ nest 2 $ group $
    text "Expected comparable type but got:" <+/> ppr tau

-- | Check that a type is a type on which we can perform Boolean operations.
checkBoolT :: MonadTc m => Type -> m ()
checkBoolT (BoolT {}) = return ()
checkBoolT (FixT {})  = return ()
checkBoolT tau =
    faildoc $ nest 2 $ group $
    text "Expected a Boolean type, e.g., bool or int, but got:" <+/> ppr tau

-- | Check that a type is a type on which we can perform bitwise operations.
checkBitT :: MonadTc m => Type -> m ()
checkBitT (BoolT {})       = return ()
checkBitT (FixT _ U _ _ _) = return ()
checkBitT tau =
    faildoc $ nest 2 $ group $
    text "Expected a bit type, e.g., bool or uint, but got:" <+/> ppr tau

-- | Check that a type is an integer type.
checkIntT :: MonadTc m => Type -> m ()
checkIntT (FixT {}) = return ()
checkIntT tau =
    faildoc $ nest 2 $ group $
    text "Expected integer type but got:" <+/> ppr tau

-- | Check that a type is a numerical type.
checkNumT :: MonadTc m => Type -> m ()
checkNumT (FixT {})            = return ()
checkNumT (FloatT {})          = return ()
checkNumT tau | isComplexT tau = return ()
checkNumT tau =
    faildoc $ nest 2 $ group $
    text "Expected numerical type but got:" <+/> ppr tau

-- | Check that a type is an @arr \iota \alpha@ type, returning @\iota@ and
-- @\alpha@.
checkArrT :: MonadTc m => Type -> m (Iota, Type)
checkArrT (ArrT iota alpha _) =
    return (iota, alpha)

checkArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

-- | Check that the argument is either an array or a reference to an array and
-- return the array's size and the type of its elements.
checkArrOrRefArrT :: Monad m => Type -> m (Iota, Type)
checkArrOrRefArrT (ArrT iota tau _)          = return (iota, tau)
checkArrOrRefArrT (RefT (ArrT iota tau _) _) = return (iota, tau)
checkArrOrRefArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

-- | Check that a type is a struct type, returning the name of the struct.
checkStructT :: MonadTc m => Type -> m Struct
checkStructT (StructT s _) =
    return s

checkStructT tau =
    faildoc $ nest 2 $
    text "Expected struct type, but got:" <+/> ppr tau

checkStructFieldT :: MonadTc m => StructDef -> Field -> m Type
checkStructFieldT (StructDef s flds _) f =
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

checkFunT :: MonadTc m => Type -> m ([IVar], [Type], Type)
checkFunT (FunT iotas taus tau_ret _) =
    return (iotas, taus, tau_ret)

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
context using the function 'appSTScope'.

In the auto language, we differentiate syntactically between expressions, which
may be pure or pureish, and computations that take and emit. In that language,
we /do not/ instantiate ST types immediately in the expression
language. Instead, we must instantiate any ST types when they become part of a
computation.
-}

absSTScope :: MonadTc m => Type -> m Type
absSTScope (ST [] omega s a b l) = do
    (s',a',b') <- askSTIndTypes
    let alphas =  nub [alpha | TyVarT alpha _ <- [s',a',b']]
    return $ ST alphas omega s a b l

absSTScope tau =
    return tau

appSTScope :: MonadTc m => Type -> m Type
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

checkForallSTC :: MonadTc m => Type -> m Type
checkForallSTC (ST _ (C tau) _ _ _ _) =
    return tau

checkForallSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C tau) s a b' but got:" </> ppr tau

checkForallSTCUnit :: MonadTc m => Type -> m ()
checkForallSTCUnit (ST _ (C (UnitT _)) _ _ _ _) =
    return ()

checkForallSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C ()) s a b' but got:" <+/> ppr tau

checkST :: MonadTc m => Type -> m (Omega, Type, Type, Type)
checkST (ST [] omega s a b _) =
    return (omega, s, a, b)

checkST tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST omega s a b' but got:" <+/> ppr tau

checkSTC :: MonadTc m => Type -> m (Type, Type, Type, Type)
checkSTC (ST [] (C tau) s a b _) =
    return (tau, s, a, b)

checkSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C tau) s a b' but got:" </> ppr tau

checkSTCUnit :: MonadTc m => Type -> m (Type, Type, Type)
checkSTCUnit (ST [] (C (UnitT _)) s a b _) =
    return (s, a, b)

checkSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'ST (C ()) s a b' but got:" <+/> ppr tau

checkPure :: MonadTc m => Type -> m ()
checkPure tau@(ST {}) =
    faildoc $ nest 2 $ group $
    text "Expected pure type got:" <+/> ppr tau

checkPure _ =
    return ()

checkPureish :: MonadTc m => Type -> m ()
checkPureish tau@(ST {}) = void $ checkPureishST tau
checkPureish _           = return ()

checkPureishST :: MonadTc m => Type -> m ([TyVar], Omega, Type, Type, Type)
checkPureishST tau@(ST alphas omega s a b _) | isPureishT tau =
    return (alphas, omega, s, a, b)

checkPureishST tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST omega s a b' but got:" <+/> ppr tau

checkPureishSTC :: MonadTc m => Type -> m ([TyVar], Type, Type, Type, Type)
checkPureishSTC tau0@(ST alphas (C tau) s a b _) | isPureishT tau0 =
    return (alphas, tau, s, a, b)

checkPureishSTC tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST (C tau) s a b' but got:" </> ppr tau

checkPureishSTCUnit :: MonadTc m => Type -> m ([TyVar], Type, Type, Type)
checkPureishSTCUnit tau@(ST alphas (C (UnitT _)) s a b _) | isPureishT tau =
    return (alphas, s, a, b)

checkPureishSTCUnit tau =
    faildoc $ nest 2 $ group $
    text "Expected type of the form 'forall s a b . ST (C ()) s a b' but got:" <+/> ppr tau
