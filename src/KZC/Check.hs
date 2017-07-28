{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check (
    liftTi,

    Expected,
    readExpected,

    checkProgram,

    tcExp,
    checkExp,
    inferExp,

    refPath
  ) where

import Control.Monad (filterM,
                      replicateM,
                      unless,
                      void,
                      when,
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

import qualified Language.Ziria.Syntax as Z

import KZC.Check.Monad
import KZC.Check.Path
import KZC.Check.Smart
import KZC.Check.Types
import KZC.Config
import qualified KZC.Expr.Smart as E
import qualified KZC.Expr.Syntax as E
import KZC.Util.Error
import KZC.Util.Pretty
import KZC.Util.SetLike
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

type CoDecl = Ti E.Decl -> Ti E.Decl

type Co = Ti E.Exp -> Ti E.Exp

data Expected a = Infer (IORef a)
                | Check a
  deriving (Show)

readExpected :: MonadRef IORef m => Expected a -> m a
readExpected (Infer r)   = readRef r
readExpected (Check tau) = return tau

checkProgram :: Z.Program -> (E.Program -> Ti a) -> Ti a
checkProgram (Z.Program zimports zdecls) k =
    checkDecls zdecls $ \mdecls -> do
    decls       <- sequence mdecls
    let imports =  [E.Import m | Z.Import m <- zimports]
    k $ E.Program imports decls

{- Note [Value Contexts]

The core language is a monadic pure language, so it treats assignments and
dereferences as monadic actions. The surface language does not, so "pure" Zira
expressions may involve (implicit) dereferences. We "collect" these implicit
actions in a /value context/ and sequence them so they take place before the
expression in which their results are used.

Where do we have value contexts?

1) The right-hand-side of any binding is a value context if it is not pure, for
example, in a Ziria @let comp@ construct. The body of a @let fun@ is also a
value context, since any Ziria function results in a Core term that is monadic,
that is, the Core term to which it is elaborated has an @ST@ type to the right
of the arrow. The body of any @let comp@ variation is also a value context.

2) The branches of an @if@ expression are value contexts if the @if@ expression
is not pure.

3) The body of a @while@, @until@, @times@, or @for@ expression is a value
context.

4) The body of a @let comp@ variation is a value context.

5) Any statement or command is a value context.
-}

-- | Perform the type checking action @k@ in a value context of type @tau@ and
-- collect the resulting actions. Note that @tau@ has the form @ST (C _) _ _@
-- because value contexts are all monadic.
collectCheckValCtx :: Type -> Ti (Ti E.Exp) -> Ti (Ti E.Exp)
collectCheckValCtx tau k = do
    mce <- localValCtxType tau k
    return $ withValCtx mce

-- | Perform the type inference action @k@ in a value context and
-- collect the resulting actions. Note that @tau@ has the form @ST (C _) _ _@
-- because value contexts are all monadic.
collectInferValCtx :: Ti (Type, Ti E.Exp) -> Ti (Type, Ti E.Exp)
collectInferValCtx k = do
    tau         <- newMetaTvT MuK NoLoc
    (tau', mce) <- localValCtxType tau k
    tau''       <- compress tau'
    if isPureT tau''
      then return (tau'', mce)
      else do unifyTypes tau tau''
              return (tau'', mce)

checkLet :: Z.Var
         -> Maybe Z.Type
         -> Z.Exp
         -> SrcLoc
         -> Ti (Type, Ti E.Decl)
checkLet v ztau e l =
    withExpContext e $ do
    tau <- fromZ (ztau, tauK)
    mce <- castVal tau e
    let mcdecl = do checkUnresolvedMtvs v tau
                    cv   <- trans v
                    ctau <- trans tau
                    ce   <- mce
                    return $ E.LetD cv ctau ce l
    return (tau, mcdecl)

checkLetComp :: Z.Var
             -> Maybe Z.Type
             -> Z.Exp
             -> SrcLoc
             -> Ti (Type, Ti E.Decl)
checkLetComp v ztau e l =
    withExpContext e $ do
    tau <- fromZ (ztau, MuK)
    mce <- collectCheckValCtx tau $
           checkExp e tau
    (tau_gen, co) <- generalize tau
    let mcdecl = co $ do cv   <- trans v
                         ctau <- trans tau_gen
                         ce   <- mce
                         return $ E.LetD cv ctau ce l
    return (tau_gen, mcdecl)

checkLetRef :: Z.Var
            -> Maybe Z.Type
            -> Maybe Z.Exp
            -> SrcLoc
            -> Ti (Type, Ti E.Decl)
checkLetRef v ztau e_init l =
    withMaybeExpContext e_init $ do
    tau <- fromZ (ztau, tauK)
    extendVars [(v, refT tau)] $ do
      mce <- mkRhs tau e_init
      let mcdecl = do checkUnresolvedMtvs v tau
                      cv   <- trans v
                      ctau <- trans tau
                      ce   <- mce
                      return $ E.LetRefD cv ctau ce l
      return (tau, mcdecl)
  where
    withMaybeExpContext :: Maybe Z.Exp -> Ti a -> Ti a
    withMaybeExpContext Nothing  m = m
    withMaybeExpContext (Just e) m = withExpContext e m

    mkRhs :: Type -> Maybe Z.Exp -> Ti (Ti (Maybe E.Exp))
    mkRhs tau (Just e) = do
        mce <- castVal tau e
        return $ Just <$> mce

    mkRhs _ Nothing =
        return $ return Nothing

-- | Check the body of a let expression. The let expression must be translated
-- to a pure core expression.
checkLetBody :: Z.Exp
             -> Expected Type
             -> Ti E.Decl
             -> SrcLoc
             -> Ti (Ti E.Exp)
checkLetBody e exp_ty mcdecl l = do
    mce <- tcExp e exp_ty
    tau <- readExpected exp_ty >>= compress
    go tau mce
  where
    go :: Type -> Ti E.Exp -> Ti (Ti E.Exp)
    go (RefT tau _) mce = do
        instType tau exp_ty
        return $ do
          cdecl <- mcdecl
          cx    <- gensym "x"
          ctau  <- trans tau
          ce    <- withValCtx $ E.derefE <$> mce
          tellValCtx $ \ce2 -> E.bindE cx ctau (E.LetE cdecl ce l) ce2
          return $ E.varE cx

    go _tau mce =
        return $ E.LetE <$> mcdecl <*> mce <*> pure l

checkLetFun :: Z.Var
            -> [(Z.TyVar, Maybe Z.Kind)]
            -> [Z.VarBind]
            -> Maybe Z.Type
            -> Z.Exp
            -> SrcLoc
            -> Ti (Type, Ti E.Decl)
checkLetFun f ztvks ps ztau_ret e l = do
    tau  <- newMetaTvT PhiK f
    tvks <- traverse fromZ ztvks
    extendTyVars tvks $ do
      ptaus   <- fromZ ps
      tau_ret <- instantiateFunRetType ztau_ret
      (tau_ret_gen, mce) <-
          extendVars ((f,tau) : ptaus) $ do
          mce               <- collectCheckValCtx tau_ret $
                               checkExp e tau_ret
          (tau_ret_gen, _)  <- generalize tau_ret
          unifyTypes (funT [] (map snd ptaus) tau_ret_gen l) tau
          return (tau_ret_gen, mce)
      (tau_gen, co) <- generalize tau
      mapM_ zonkTvk tvks
      let tau_gen' = forallT tvks tau_gen
      traceVar f tau_gen'
      let mkLetFun = co $ do cf       <- trans f
                             ctvks    <- traverse trans tvks
                             cptaus   <- mapM trans ptaus
                             ctau_ret <- trans tau_ret_gen
                             ce       <- withSummaryContext e mce
                             return $ E.LetFunD cf ctvks cptaus ctau_ret ce l
      return (tau_gen', mkLetFun)
  where
    -- Coerce a user-annotated function return type to a "real" function return
    -- type and instantiate it so we can check it. For example, we convert the
    -- user-annotated return type 'int' to 'forall s a b . ST (C int) s a b'.
    instantiateFunRetType :: Maybe Z.Type -> Ti Type
    instantiateFunRetType Nothing =
        newMetaTvT MuK l

    instantiateFunRetType (Just ztau@Z.ST{}) =
        fromZ ztau

    -- If we are givne a base type, turn it into an ST type.
    instantiateFunRetType (Just ztau) = do
        tau         <- fromZ ztau
        [s,a,b]     <- freshenVars ["s", "a", "b"] (fvs tau)
        (tau', _cp) <- instantiate $ forallST [s,a,b] (C tau l) (tyVarT s) (tyVarT a) (tyVarT b) l
        return tau'
      where
        l :: SrcLoc
        l = srclocOf ztau

{- Note [External Functions]

We assume that a Ziria external function with return type unit is
impure. Otherwise, we assume an external function is pure /unless/ it is marked
with the impure keyword.

Really we should mark pure functions as such, but that would require more
substantial changes to externals.blk, so we go for the minimal change.
-}

checkLetExtFun :: Z.Var -> [Z.VarBind] -> Z.Type -> Bool -> SrcLoc
               -> Ti (Type, Ti E.Decl)
checkLetExtFun f ps ztau_ret isPure l = do
    ptaus         <- fromZ ps
    -- Note that the output type may depend on the parameters because of array
    -- lengths
    tau_ret       <- extendVars ptaus $
                     checkRetType ztau_ret
    let tau       =  funT [] (map snd ptaus) tau_ret l
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    let mkLetExtFun = co $ do cf       <- trans f
                              cptaus   <- mapM trans ptaus
                              ctau_ret <- trans tau_ret
                              return $ E.LetExtFunD cf [] cptaus ctau_ret l
    return (tau_gen, mkLetExtFun)
  where
    checkRetType :: Z.Type -> Ti Type
    checkRetType Z.UnitT{} = do
        s <- newMetaTvT tauK l
        a <- newMetaTvT tauK l
        b <- newMetaTvT tauK l
        fst <$> generalize (ST (C (UnitT l) l) s a b l)

    checkRetType ztau | not isPure = do
        s   <- newMetaTvT tauK l
        a   <- newMetaTvT tauK l
        b   <- newMetaTvT tauK l
        tau <- fromZ ztau
        fst <$> generalize (ST (C tau l) s a b l)

    checkRetType ztau =
        fromZ ztau

checkDecl :: Z.Decl
          -> ([Ti E.Decl] -> Ti a)
          -> Ti a
checkDecl decl@(Z.StructD zs ztvks zflds l) k = do
    (tvks, taus_fields) <-
        alwaysWithSummaryContext decl $ do
        checkStructNotRedefined zs
        checkDuplicates "field names" zfields
        tvks <- mapM fromZ ztvks
        extendTyVars tvks $ do
          taus_fields <- mapM fromZ ztaus_fields
          mapM_ (`checkKind` tauK) taus_fields
          -- XXX for some reason we don't need this here, even though we need it
          -- in.
          mapM_ zonkTvk tvks
          return (tvks, taus_fields)
    let mcdecl = alwaysWithSummaryContext decl $ do
                 cs           <- trans zs
                 ctvks        <- mapM trans tvks
                 cfields      <- mapM trans zfields
                 ctaus_fields <- mapM trans taus_fields
                 return $ E.StructD cs ctvks (cfields `zip` ctaus_fields) l
    extendStructs [StructDef zs tvks (zfields `zip` taus_fields) l] $ k [mcdecl]
  where
    (zfields, ztaus_fields) = unzip zflds

checkDecl decl@(Z.TypeD zs ztvks ztau l) k = do
    (tvks, tau) <-
        alwaysWithSummaryContext decl $ do
        checkStructNotRedefined zs
        tvks <- mapM fromZ ztvks
        tau  <- extendTyVars tvks $
                fromZ ztau
        mapM_ zonkTvk tvks
        return (tvks, tau)
    extendStructs [TypeDef zs tvks tau l] $ k []

checkDecl decl@(Z.LetD v ztau e l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLet v ztau e l
    extendVars [(v, tau)] $ k [alwaysWithSummaryContext decl mcdecl]

checkDecl decl@(Z.LetRefD v ztau e_init l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLetRef v ztau e_init l
    extendVars [(v, refT tau)] $ k [mcdecl]

checkDecl decl@(Z.LetFunD f tvks ps tau e l) k = do
    (tau, mkLetFun) <- alwaysWithSummaryContext decl $
                       checkLetFun f tvks ps tau e l
    let mcdecl = alwaysWithSummaryContext decl mkLetFun
    extendVars [(f,tau)] $ k [mcdecl]

checkDecl decl@(Z.LetFunExternalD f ps ztau_ret isPure l) k = do
    (tau, mkLetExtFun) <- alwaysWithSummaryContext decl $
                          checkLetExtFun f ps ztau_ret isPure l
    let mcdecl = alwaysWithSummaryContext decl mkLetExtFun
    extendVars [(f,tau)] $ k [mcdecl]

checkDecl decl@(Z.LetCompD v ztau _ e l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLetComp v ztau e l
    extendVars [(v, tau)] $ k [alwaysWithSummaryContext decl mcdecl]

checkDecl decl@(Z.LetFunCompD f _range tvks ps tau e l) k = do
    (tau, mkLetFun) <- alwaysWithSummaryContext decl $
                       checkLetFun f tvks ps tau e l
    let mcdecl = alwaysWithSummaryContext decl mkLetFun
    extendVars [(f,tau)] $ k [mcdecl]

checkDecls :: [Z.Decl]
           -> ([Ti E.Decl] -> Ti a)
           -> Ti a
checkDecls [] k =
    k []

checkDecls (decl:decls) k =
    checkDecl  decl  $ \mcdecl  ->
    checkDecls decls $ \mcdecls ->
    k (mcdecl ++ mcdecls)

mkSigned :: Monad m => Type -> m Type
mkSigned (IntT UDefault l)     = return $ IntT IDefault l
mkSigned (IntT (U w) l)        = return $ IntT (I w) l
mkSigned tau@(IntT IDefault _) = return tau
mkSigned tau@(IntT I{} _)      = return tau
mkSigned tau =
    faildoc $ text "Cannot cast type" <+> enquote (ppr tau) <+> text "to unsigned."

mkUnsigned :: Monad m => Type -> m Type
mkUnsigned (IntT IDefault l)     = return $ IntT UDefault l
mkUnsigned (IntT (I w) l)        = return $ IntT (U w) l
mkUnsigned tau@(IntT UDefault _) = return tau
mkUnsigned tau@(IntT U{} _)      = return tau
mkUnsigned tau =
    faildoc $ text "Cannot cast type" <+> enquote (ppr tau) <+> text "to signed."

tcExp :: Z.Exp -> Expected Type -> Ti (Ti E.Exp)
tcExp (Z.ConstE zc l) exp_ty = do
    cc <- tcConst zc
    return $ return $ E.ConstE cc l
  where
    tcConst :: Z.Const -> Ti E.Const
    tcConst Z.UnitC = do
        instType (UnitT l) exp_ty
        return E.UnitC

    tcConst (Z.BoolC b) = do
        instType (BoolT l) exp_ty
        return $ E.BoolC b

    tcConst (Z.IntC zip x) = do
        ip  <- fromZ zip
        cip <- trans ip
        instType (IntT ip l) exp_ty
        return $ E.IntC cip x

    tcConst (Z.FixC zqp x) = do
        qp  <- fromZ zqp
        cqp <- trans qp
        instType (FixT qp l) exp_ty
        return $ E.FixC cqp x

    tcConst (Z.FloatC zw f) = do
        w  <- fromZ zw
        cw <- trans w
        instType (FloatT w l) exp_ty
        return $ E.FloatC cw f

    tcConst (Z.StringC s)  = do
        instType (StringT l) exp_ty
        return $ E.StringC s

tcExp (Z.VarE v _) exp_ty = do
    (tau, co) <- lookupVar v >>= instantiate
    instType tau exp_ty
    return $ co $ E.varE <$> trans v

tcExp (Z.UnopE op e l) exp_ty =
    withExpContext e $
    unop op
  where
    unop :: Z.Unop -> Ti (Ti E.Exp)
    unop Z.Lnot   = checkBoolUnop E.Lnot
    unop Z.Bnot   = checkBitsUnop E.Bnot
    unop Z.Neg    = checkSignedNumUnop E.Neg
    unop Z.Abs    = checkNumUnop E.Abs
    unop Z.Exp    = checkFracUnop E.Exp
    unop Z.Exp2   = checkFracUnop E.Exp2
    unop Z.Expm1  = checkFracUnop E.Expm1
    unop Z.Log    = checkFracUnop E.Log
    unop Z.Log2   = checkFracUnop E.Log2
    unop Z.Log1p  = checkFracUnop E.Log1p
    unop Z.Sqrt   = checkFracUnop E.Sqrt
    unop Z.Sin    = checkFracUnop E.Sin
    unop Z.Cos    = checkFracUnop E.Cos
    unop Z.Tan    = checkFracUnop E.Tan
    unop Z.Asin   = checkFracUnop E.Asin
    unop Z.Acos   = checkFracUnop E.Acos
    unop Z.Atan   = checkFracUnop E.Atan
    unop Z.Sinh   = checkFracUnop E.Sinh
    unop Z.Cosh   = checkFracUnop E.Cosh
    unop Z.Tanh   = checkFracUnop E.Tanh
    unop Z.Asinh  = checkFracUnop E.Asinh
    unop Z.Acosh  = checkFracUnop E.Acosh
    unop Z.Atanh  = checkFracUnop E.Atanh

    unop Z.Len = do
        (tau, mce) <- inferExp e
        _          <- checkArrT tau
        instType idxT exp_ty
        return $ E.UnopE E.Len <$> mce <*> pure l

    checkBoolUnop :: E.Unop -> Ti (Ti E.Exp)
    checkBoolUnop cop = do
        (tau, mce) <- inferVal e
        checkKind tau boolK
        instType tau exp_ty
        return $ E.UnopE cop <$> mce <*> pure l

    checkBitsUnop :: E.Unop -> Ti (Ti E.Exp)
    checkBitsUnop cop = do
        (tau, mce) <- inferVal e
        (tau', co) <- mkBits e tau
        checkKind tau' bitsK
        instType tau' exp_ty
        return $ E.UnopE cop <$> co mce <*> pure l

    checkNumUnop :: E.Unop -> Ti (Ti E.Exp)
    checkNumUnop cop = do
        (tau, mce) <- inferVal e
        checkKind tau numK
        instType tau exp_ty
        return $ E.UnopE cop <$> mce <*> pure l

    checkSignedNumUnop :: E.Unop -> Ti (Ti E.Exp)
    checkSignedNumUnop cop = do
        (tau, mce) <- inferVal e
        checkKind tau numK
        tau' <- mkSigned tau
        instType tau' exp_ty
        return $ E.UnopE cop <$> mce <*> pure l

    checkFracUnop :: E.Unop -> Ti (Ti E.Exp)
    checkFracUnop cop = do
        (tau, mce) <- inferVal e
        checkKind tau fracK
        instType tau exp_ty
        return $ E.UnopE cop <$> mce <*> pure l

tcExp e@(Z.BinopE op e1 e2 l) exp_ty =
    withExpContext e $
    binop op
  where
    binop :: Z.Binop -> Ti (Ti E.Exp)
    binop Z.Eq   = checkEqBinop E.Eq
    binop Z.Ne   = checkEqBinop E.Ne
    binop Z.Lt   = checkOrdBinop E.Lt
    binop Z.Le   = checkOrdBinop E.Le
    binop Z.Ge   = checkOrdBinop E.Ge
    binop Z.Gt   = checkOrdBinop E.Gt
    binop Z.Land = checkBoolBinop E.Land
    binop Z.Lor  = checkBoolBinop E.Lor
    binop Z.Band = checkBitBinop E.Band
    binop Z.Bor  = checkBitBinop E.Bor
    binop Z.Bxor = checkBitBinop E.Bxor
    binop Z.LshL = checkBitShiftBinop E.LshL
    binop Z.LshR = checkBitShiftBinop E.LshR
    binop Z.AshR = checkBitShiftBinop E.AshR
    binop Z.Add  = checkNumBinop E.Add
    binop Z.Sub  = checkNumBinop E.Sub
    binop Z.Mul  = checkNumBinop E.Mul
    binop Z.Div  = checkNumBinop E.Div
    binop Z.Rem  = checkNumBinop E.Rem
    binop Z.Pow  = checkNumBinop E.Pow

    checkEqBinop :: E.Binop -> Ti (Ti E.Exp)
    checkEqBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkKind tau eqK
        instType boolT exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkOrdBinop :: E.Binop -> Ti (Ti E.Exp)
    checkOrdBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkKind tau ordK
        instType boolT exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBoolBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBoolBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkKind tau boolK
        instType tau exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkNumBinop :: E.Binop -> Ti (Ti E.Exp)
    checkNumBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkKind tau numK
        instType tau exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBitBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBitBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        (tau', co)        <- mkBits e1 tau
        checkKind tau' bitsK
        instType tau' exp_ty
        return $ E.BinopE cop <$> co mce1 <*> co mce2 <*> pure l

    checkBitShiftBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBitShiftBinop cop = do
        (tau1, mce1) <- inferVal e1
        (tau1', co1) <- mkBits e1 tau1
        checkKind tau1' bitsK
        (tau2, mce2) <- inferVal e2
        co2          <- mkCheckedSafeCast e2 tau2 uintT
        instType tau1' exp_ty
        return $ E.BinopE cop <$> co1 mce1 <*> co2 mce2 <*> pure l

tcExp (Z.IfE e1 e2 Nothing l) exp_ty = do
    mce1        <- checkVal e1 (BoolT l)
    (tau, mce2) <- collectInferValCtx $ inferExp e2
    void $ checkSTCUnit tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ E.IfE ce1 ce2 (E.returnE E.unitE) l

tcExp (Z.IfE e1 e2 (Just e3) l) exp_ty = do
    mce1              <- checkVal e1 (BoolT l)
    (tau, mce2, mce3) <- do (tau2, mce2) <- collectInferValCtx $ inferExp e2
                            (tau3, mce3) <- collectInferValCtx $ inferExp e3
                            unifyCompiledExpTypes tau2 e2 mce2 tau3 e3 mce3
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                ce3 <- mce3
                return $ E.IfE ce1 ce2 ce3 l

tcExp (Z.LetE v ztau e1 e2 l) exp_ty = do
    (tau, mcdecl) <- checkLet v ztau e1 l
    withExpContext e2 $
      extendVars [(v, tau)] $
      checkLetBody e2 exp_ty mcdecl l

tcExp (Z.LetRefE v ztau e1 e2 l) exp_ty = do
    (tau, mcdecl) <- checkLetRef v ztau e1 l
    withExpContext e2 $
      extendVars [(v, refT tau)] $
      checkLetBody e2 exp_ty mcdecl l

tcExp (Z.LetDeclE decl e l) exp_ty =
    checkDecl decl $ \[mcdecl] -> do
    tau <- newMetaTvT MuK l
    instType tau exp_ty
    mce <- collectCheckValCtx tau $ checkExp e tau
    return $ E.LetE <$> mcdecl <*> mce <*> pure l

tcExp e@(Z.CallE f maybe_ztaus es l) exp_ty =
    withCallContext f e $ do
    maybe_taus <- traverse (mapM fromZ) maybe_ztaus
    (taus_args, tau_ret, co1) <- lookupVar f >>= checkFunT f maybe_taus nargs
    checkNumArgs (length taus_args) nargs
    (tau_ret', co2) <- instantiate tau_ret
    instType tau_ret' exp_ty
    mces <- zipWithM checkArg es taus_args
    unless (isPureishT tau_ret) $
        checkNoAliasing (es `zip` taus_args)
    return $ co2 $ co1 $ do
        cf    <- trans f
        ctaus <- case maybe_taus of
                   Nothing   -> return []
                   Just taus -> mapM trans taus
        ces   <- sequence mces
        return $ E.CallE cf ctaus ces l
  where
    nargs :: Int
    nargs = length es

    checkNumArgs :: Int -> Int -> Ti ()
    checkNumArgs n nexp =
        when (n /= nexp) $
            faildoc $
            text "Expected" <+> ppr nexp <+>
            text "arguments but got" <+> ppr n

    -- If a parameter is a ref type, then we do not want to implicitly
    -- dereference the corresponding argument, since it should be passed by
    -- reference. Similarly, if a parameter is an ST type, we do not want to
    -- implicitly run the corresponding argument. Otherwise, we assume we are in
    -- an r-value context.
    checkArg :: Z.Exp -> Type -> Ti (Ti E.Exp)
    checkArg e tau =
        withArgContext e $
        compress tau >>= go
      where
        go :: Type -> Ti (Ti E.Exp)
        go RefT{} = checkExp e tau
        go ST{}   = checkExp e tau
        go _      = castVal tau e

    withCallContext :: MonadErr m
                    => Z.Var
                    -> Z.Exp
                    -> m b
                    -> m b
    withCallContext f e =
        alwaysWithLocContext e doc
      where
        doc = text "In call to" <+> ppr f

    withArgContext :: MonadErr m
                   => Z.Exp
                   -> m b
                   -> m b
    withArgContext e =
        alwaysWithLocContext e doc
      where
        doc = text "In argument:" <+> ppr e

tcExp (Z.AssignE e1 e2 l) exp_ty = do
    (gamma, mce1) <-
        withSummaryContext e1 $ do
        (tau, mce1) <- inferExp e1
        gamma       <- checkRefT tau
        return (gamma, mce1)
    tau <- mkSTC (UnitT l)
    instType tau exp_ty
    mce2  <- withSummaryContext e2 $
             castVal gamma e2
    return $ do
        ce1   <- mce1
        ce2   <- mce2
        return $ E.AssignE ce1 ce2 l

tcExp (Z.WhileE e1 e2 l) exp_ty = do
    tau  <- mkSTC (UnitT l)
    mce1 <- collectCheckValCtx boolT $
            checkBoolVal e1
    mce2 <- collectCheckValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do ce1 <- mce1
                ce2 <- mce2
                return $ E.WhileE ce1 ce2 l

tcExp (Z.UntilE e1 e2 l) exp_ty = do
    tau  <- mkSTC (UnitT l)
    mce1 <- collectCheckValCtx boolT $
            checkBoolVal e1
    mce2 <- collectCheckValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do ce1       <- mce1
                cx        <- gensymAt "x" l
                ce2       <- mce2
                let ctest =  E.bindE cx E.boolT ce1 (E.returnE (E.notE (E.varE cx)))
                return $ E.WhileE ctest ce2 l

tcExp (Z.TimesE ann e1 e2 l) exp_ty = do
    (tau1, mce1) <- inferVal e1
    checkLoopIndexVarT tau1
    tau  <- mkSTC (UnitT l)
    mce2 <- collectCheckValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do cann <- trans ann
                cx   <- gensymAt "x" l
                ce1  <- mce1
                ce2  <- mce2
                return $ E.ForE cann cx E.intT (E.StartLen (E.intE (1 :: Int)) ce1 (srclocOf e1)) ce2 l

tcExp (Z.ForE ann i ztau_i gint e l) exp_ty = do
    tau_i <- fromZ (ztau_i, tauK)
    checkLoopIndexVarT tau_i
    mcgint <- tcGenInterval tau_i gint
    tau    <- mkSTC (UnitT l)
    mce    <- extendVars [(i, tau_i)] $
              collectCheckValCtx tau $
              checkExp e tau
    instType tau exp_ty
    return $ do cann   <- trans ann
                ci     <- trans i
                ctau_i <- trans tau_i
                cgint  <- mcgint
                ce     <- mce
                return $ E.ForE cann ci ctau_i cgint ce l
  where
    tcGenInterval :: Type -> Z.GenInterval -> Ti (Ti (E.GenInterval E.Exp))
    tcGenInterval tau = go
      where
        go :: Z.GenInterval -> Ti (Ti (E.GenInterval E.Exp))
        go (Z.FromToInclusive e1 e2 l) = do
            mce1 <- castVal tau e1
            mce2 <- castVal tau e2
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ E.FromToInclusive ce1 ce2 l

        go (Z.FromToExclusive e1 e2 l) = do
            mce1 <- castVal tau e1
            mce2 <- castVal tau e2
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ E.FromToExclusive ce1 ce2 l

        go (Z.StartLen e1 e2 l) = do
            mce1 <- castVal tau e1
            mce2 <- castVal tau e2
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ E.StartLen ce1 ce2 l

tcExp (Z.ArrayE es l) exp_ty = do
    tau  <- newMetaTvT tauK l
    instType (ArrT (NatT (length es) l) tau l) exp_ty
    mces <- mapM (`checkExp` tau) es
    return $ do ces <- sequence mces
                return $ E.ArrayE ces l

tcExp (Z.IdxE e1 e2 len l) exp_ty = do
    (tau, mce1) <- withSummaryContext e1 $
                   inferExp e1
    mce2        <- withSummaryContext e2 $ do
                   (tau2, mce2) <- inferVal e2
                   co <- mkCast tau2 idxT
                   return $ co mce2
    checkLen len
    checkIdxE tau mce1 mce2
  where
    checkLen :: Maybe Int -> Ti ()
    checkLen Nothing =
        return ()

    checkLen (Just len) =
        unless (len >= 0) $
        faildoc $ text "Slice length must be non-negative."

    checkIdxE :: Type
              -> Ti E.Exp
              -> Ti E.Exp
              -> Ti (Ti E.Exp)
    checkIdxE tau mce1 mce2 =
        compress tau >>= go
      where
        go :: Type -> Ti (Ti E.Exp)
        -- Indexing into a reference to an array returns a reference to an
        -- element of the array.
        go (RefT (ArrT _ tau _) _) = do
            instType (RefT (mkArrSlice tau len) l) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ E.IdxE ce1 ce2 len l

        -- A plain old array gets indexed as one would expect.
        go (ArrT _ tau _) = do
            instType (mkArrSlice tau len) exp_ty
            return $ do ce1 <- mce1
                        ce2 <- mce2
                        return $ E.IdxE ce1 ce2 len l

        -- Otherwise we assert that the type of @e1@ should be an array type.
        go tau = do
            i     <- newMetaTvT NatK l
            alpha <- newMetaTvT tauK l
            unifyTypes tau (ArrT i alpha l)
            compress tau >>= go

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (NatT i l) tau l

tcExp e0@(Z.StructE s ztaus zflds l) exp_ty =
    withSummaryContext e0 $ do
    sdef           <- lookupStruct s
    taus           <- mapM fromZ ztaus
    (tau, fldDefs) <- tyAppStruct sdef taus
    checkTyApp (structDefTvks sdef) taus
    checkMissingFields zflds fldDefs
    checkExtraFields zflds fldDefs
    (s', taus') <- checkStructT tau
    (fs, mces)  <- unzip <$> mapM (checkField fldDefs) zflds
    instType tau exp_ty
    return $ do cs    <- trans s'
                ctaus <- mapM trans taus'
                cfs   <- mapM trans fs
                ces   <- sequence mces
                return $ E.StructE cs ctaus (cfs `zip` ces) l
  where
    checkField :: [(Z.Field, Type)] -> (Z.Field, Z.Exp) -> Ti (Z.Field, Ti E.Exp)
    checkField fldDefs (f, e) = do
      tau <- case lookup f fldDefs of
               Nothing  -> panicdoc "checkField: missing field!"
               Just tau -> return tau
      mce <- castVal tau e
      return (f, mce)

    checkMissingFields :: [(Z.Field, Z.Exp)] -> [(Z.Field, Type)] -> Ti ()
    checkMissingFields flds fldDefs =
        unless (Set.null missing) $
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
        unless (Set.null extra) $
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
               -> Ti E.Exp
               -> Ti (Ti E.Exp)
    checkProjE tau mce =
        compress tau >>= go
      where
        go :: Type -> Ti (Ti E.Exp)
        go (RefT tau _) = do
            (s, taus) <- checkStructT tau
            sdef      <- lookupStruct s
            tau_f     <- checkStructFieldT sdef taus f
            instType (RefT tau_f l) exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ E.ProjE ce cf l

        go tau = do
            (s, taus) <- checkStructT tau
            sdef      <- lookupStruct s
            tau_f     <- checkStructFieldT sdef taus f
            instType tau_f exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ E.ProjE ce cf l

tcExp (Z.CastE ztau2 e _) exp_ty = do
    (tau1, mce) <- inferVal e
    tau2        <- fromZ ztau2
    co          <- mkCast tau1 tau2
    instType tau2 exp_ty
    return $ co mce

tcExp (Z.BitcastE ztau2 e l) exp_ty = do
    (tau1, mce) <- inferVal e
    tau2        <- fromZ ztau2
    checkLegalBitcast tau1 tau2
    instType tau2 exp_ty
    return $ do ce    <- mce
                ctau2 <- trans tau2
                return $ E.BitcastE ctau2 ce l

tcExp (Z.PrintE newline es l) exp_ty = do
    tau <- mkSTC (UnitT l)
    instType tau exp_ty
    mces <- mapM checkArg es
    return $ do
        ces <- sequence mces
        return $ E.PrintE newline ces l
  where
    checkArg :: Z.Exp -> Ti (Ti E.Exp)
    checkArg e = do
        (tau, mce) <- inferVal e
        checkKind tau tauK
        return mce

tcExp (Z.ErrorE s l) exp_ty = do
    nu  <- newMetaTvT tauK l
    tau <- mkSTC nu
    instType tau exp_ty
    return $ do
        cnu <- trans nu
        return $ E.ErrorE cnu s l

tcExp (Z.ReturnE ann e l) exp_ty = do
    tau     <- newMetaTvT tauK l
    tau_ret <- mkSTC tau
    instType tau_ret exp_ty
    (tau', mce) <- inferVal e
    unifyTypes tau' tau
    return $ do
        cann <- trans ann
        ce   <- mce
        return $ E.ReturnE cann ce l

tcExp (Z.TakeE l) exp_ty = do
    a <- newMetaTvT tauK l
    b <- newMetaTvT tauK l
    instType (stT (C a l) a a b) exp_ty
    return $ do ca <- trans a
                return $ E.takeE ca

tcExp (Z.TakesE i l) exp_ty = do
    a <- newMetaTvT tauK l
    b <- newMetaTvT tauK l
    instType (stT (C (ArrT (NatT i l) a l) l) a a b) exp_ty
    return $ do ca <- trans a
                return $ E.takesE (fromIntegral i) ca

tcExp (Z.EmitE e l) exp_ty = do
    s       <- newMetaTvT tauK l
    a       <- newMetaTvT tauK l
    b       <- newMetaTvT tauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    mce <- checkVal e b
    return $ E.EmitE <$> mce <*> pure l

tcExp (Z.EmitsE e l) exp_ty = do
    n       <- newMetaTvT NatK l
    s       <- newMetaTvT tauK l
    a       <- newMetaTvT tauK l
    b       <- newMetaTvT tauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    mce <- checkVal e (arrT n b)
    return $ E.EmitsE <$> mce <*> pure l

tcExp (Z.RepeatE ann e l) exp_ty = do
    (sigma, alpha, beta, mce) <-
        withSummaryContext e $ do
        (tau, mce)           <- inferExp e
        (sigma, alpha, beta) <- checkSTCUnit tau
        return (sigma, alpha, beta, mce)
    instType (stT (T l) sigma alpha beta) exp_ty
    return $ do cann <- trans ann
                ce   <- mce
                return $ E.RepeatE cann ce l

tcExp (Z.ParE _ (Z.ReadE zalpha _) (Z.WriteE zbeta _) l) exp_ty = do
    tau  <- fromZ (zalpha, tauK)
    tau' <- fromZ (zbeta, tauK)
    unifyTypes tau' tau
    instType (stT (T l) tau tau tau) exp_ty
    return $ do ctau <- trans tau
                cx   <- gensymAt "x" l
                return $ E.repeatE $
                         E.bindE cx ctau (E.takeE ctau) $
                         E.emitE (E.varE cx)

tcExp (Z.ParE _ (Z.ReadE ztau l) e _) tau_exp = do
    omega   <- newMetaTvT OmegaK l
    a       <- fromZ (ztau, tauK)
    b       <- newMetaTvT tauK l
    let tau =  ST omega a a b l
    instType tau tau_exp
    checkExp e tau

tcExp (Z.ParE _ e (Z.WriteE ztau l) _) tau_exp = do
    omega    <- newMetaTvT OmegaK l
    s        <- newMetaTvT tauK l
    a        <- newMetaTvT tauK l
    b        <- newMetaTvT tauK l
    b'       <- fromZ (ztau, tauK)
    let tau  =  ST omega s a b l
    let tau' =  ST omega s a b' l
    instType tau' tau_exp
    ce <- checkExp e tau
    co <- mkCastT b b'
    return $ co ce

tcExp e@(Z.ParE ann e1 e2 l) tau_exp = do
    omega1   <- newMetaTvT OmegaK l
    omega2   <- newMetaTvT OmegaK l
    a        <- newMetaTvT tauK l
    b        <- newMetaTvT tauK l
    b'       <- newMetaTvT tauK l
    c        <- newMetaTvT tauK l
    let tau1 =  ST omega1 a  a  b l
    let tau2 =  ST omega2 b' b' c l
    mce1     <- withSummaryContext e1 $
                checkExp e1 tau1
    mce2     <- withSummaryContext e2 $
                checkExp e2 tau2
    co       <- withSTContext tau1 tau2 $
                withSummaryContext e $
                mkCastT b b'
    omega  <- joinOmega omega1 omega2
    instType (ST omega a a c l) tau_exp
    checkForSplitContext
    return $ do
        cann <- trans ann
        cb'  <- trans b'
        ce1  <- co mce1
        ce2  <- mce2
        return $ E.ParE cann cb' ce1 ce2 l
  where
    checkForSplitContext :: Ti ()
    checkForSplitContext = do
        common_refs <- filterM isRefVar (Set.toList common_fvs)
        unless (null common_refs) $
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
        withLocContext (tau1 <--> tau2) doc m

tcExp e@Z.ReadE{} _ =
    withSummaryContext e $
        faildoc $
        text "Naked read. That's odd!"

tcExp e@Z.WriteE{} _ =
    withSummaryContext e $
        faildoc $
        text "Naked write. That's odd!"

tcExp (Z.StandaloneE e _) exp_ty =
    tcExp e exp_ty

tcExp (Z.MapE ann f ztau l) exp_ty = do
    tau  <- fromZ (ztau, PhiK)
    tau' <- lookupVar f
    unifyTypes tau' tau
    (a, b, co) <- checkMapFunT f tau
    instType (stT (T l) a a b) exp_ty
    return $ do cx     <- gensymAt "x" l
                cy     <- gensymAt "y" l
                ccalle <- co $ return $ E.varE cx
                ca     <- trans a
                cb     <- trans b
                cann   <- trans ann
                return $ E.repeatAnnE cann $
                         E.bindE cx ca (E.takeE ca) $
                         E.bindE cy cb ccalle $
                         E.emitE (E.varE cy)

tcExp (Z.StmE stms _) exp_ty =
    tcStms stms exp_ty

tcExp e _ = faildoc $ text "tcExp: can't type check:" <+> ppr e

checkExp :: Z.Exp -> Type -> Ti (Ti E.Exp)
checkExp e tau = tcExp e (Check tau)

inferExp :: Z.Exp -> Ti (Type, Ti E.Exp)
inferExp e = do
    ref <- newRef (error "inferExp: empty result")
    mce <- tcExp e (Infer ref)
    tau <- readRef ref
    return (tau, mce)

-- | Construct a let expression given an expression, its type, and a
-- continuation. The continuation is called with the new binding.
mkLetE :: Type -> E.Exp -> (E.Exp -> Ti E.Exp) -> Ti E.Exp
mkLetE _tau ce1@E.ConstE{} k =
    k ce1

mkLetE _tau ce1@E.VarE{} k =
    k ce1

mkLetE tau ce1 k = do
    cx   <- gensym "x"
    ctau <- trans tau
    ce2  <- k (E.varE cx)
    return $ E.letE cx ctau ce1 ce2

-- | Check that there is no aliasing between function arguments.
checkNoAliasing :: [(Z.Exp, Type)] -> Ti ()
checkNoAliasing etaus = do
    rpaths <- concat <$> mapM root etaus
    checkNoPathAliasing rpaths
  where
    root :: (Z.Exp, Type) -> Ti [RefPath Z.Var Z.Field]
    root (e, tau) | isRefT tau = do
        path <- refPath e
        return [path]

    root _ =
        return []

refPath :: forall m . Monad m => Z.Exp -> m (RefPath Z.Var Z.Field)
refPath e =
    go e []
  where
    go :: Z.Exp -> [Path Z.Field] -> m (RefPath Z.Var Z.Field)
    go (Z.VarE v _) path =
        return $ RefP v (reverse path)

    go (Z.IdxE e (Z.ConstE (Z.IntC _ i) _) Nothing _) path =
        go e (IdxP i 1 : path)

    go (Z.IdxE e (Z.ConstE (Z.IntC _ i) _) (Just len) _) path =
        go e (IdxP i len : path)

    go (Z.IdxE e _ _ _) _ =
        go e []

    go (Z.ProjE e f _) path =
        go e (ProjP f : path)

    go e _ =
        faildoc $ text "refPath: Not a reference:" <+> ppr e

-- | Check that a struct is not being re-defined.
checkStructNotRedefined :: Z.Struct -> Ti ()
checkStructNotRedefined s = do
    maybe_sdef <- maybeLookupStruct s
    case maybe_sdef of
      Nothing   -> return ()
      Just sdef -> faildoc $ text "Struct" <+> enquote (ppr s) <+> text "redefined" <+>
                   parens (text "original definition at" <+> ppr (locOf sdef))

tcStms :: [Z.Stm] -> Expected Type -> Ti (Ti E.Exp)
tcStms [stm@Z.LetS{}] _ =
    withSummaryContext stm $
    faildoc $ text "Last command in command sequence must be an expression"

tcStms (Z.LetS decl l : stms) exp_ty = do
    tau <- mkSTOmega
    instType tau exp_ty
    collectCheckValCtx tau $
      checkDecl decl $ \[mcdecl] -> do
      mce <- checkStms stms tau
      return $ do
          cdecl <- mcdecl
          ce    <- mce
          return $ E.LetE cdecl ce l

tcStms [stm@Z.BindS{}] _ =
    withSummaryContext stm $
    faildoc $ text "Last command in command sequence must be an expression"

tcStms (stm@(Z.BindS v ztau e l) : stms) exp_ty = do
    nu                  <- fromZ (ztau, tauK)
    tau1@(ST _ s a b _) <- mkSTC nu
    omega2              <- newMetaTvT OmegaK l
    let tau2            =  ST omega2 s a b l
    instType tau2 exp_ty
    mce1 <- withSummaryContext stm $
            collectCheckValCtx tau1 $
            checkExp e tau1
    mce2 <- extendVars [(v, nu)] $
            checkStms stms tau2
    withSummaryContext e checkForUnusedReturn
    return $ do checkUnresolvedMtvs v nu
                cv  <- trans v
                ce1 <- withSummaryContext stm mce1
                cnu <- trans nu
                ce2 <- mce2
                return $ E.BindE (E.TameV cv) cnu ce1 ce2 l
  where
    checkForUnusedReturn :: Ti ()
    checkForUnusedReturn =
        when (isReturn e && Set.notMember v (fvs stms)) $
        faildoc "Result of return is not used"

    isReturn :: Z.Exp -> Bool
    isReturn Z.ReturnE{} = True
    isReturn _              = False

tcStms [stm@(Z.ExpS e _)] exp_ty =
    withSummaryContext stm $ do
    tau <- mkSTOmega
    instType tau exp_ty
    collectCheckValCtx tau $
      checkExp e tau

tcStms (stm@(Z.ExpS e l) : stms) exp_ty = do
    nu                  <- newMetaTvT tauK l
    tau1@(ST _ s a b _) <- mkSTC nu
    omega2              <- newMetaTvT OmegaK l
    let tau2            =  ST omega2 s a b l
    instType tau2 exp_ty
    mce1 <- withSummaryContext stm $
            collectCheckValCtx tau1 $
            checkExp e tau1
    nu' <- compress nu
    unless (isUnitT nu') $
        withSummaryContext stm $
        warndocWhen WarnUnusedCommandBind $
        text "Command discarded a result of type" <+> ppr nu'
    mce2 <- checkStms stms tau2
    return $ do ce1 <- withSummaryContext stm mce1
                cnu <- trans nu
                ce2 <- mce2
                return $ E.seqE cnu ce1 ce2

tcStms [] _ =
    panicdoc $ text "Empty command sequence!"

checkStms :: [Z.Stm] -> Type -> Ti (Ti E.Exp)
checkStms stms tau = tcStms stms (Check tau)

-- | Type check an expression in a context where a value is needed. This will
-- generate extra code to dereference any references and run any actions of type
-- @forall s a b . ST tau s a b@.
tcVal :: Z.Exp -> Expected Type -> Ti (Ti E.Exp)
tcVal e exp_ty = do
    (tau, mce) <- inferExp e
    tau' <- compress tau
    go tau' mce
  where
    go :: Type -> Ti E.Exp -> Ti (Ti E.Exp)
    go (RefT tau _) mce = do
        let mce' = do ce1  <- mce
                      cx   <- gensymAt "x" ce1
                      ctau <- trans tau
                      tellValCtx $ \ce2 -> E.bindE cx ctau (E.derefE ce1) ce2
                      return $ E.varE cx
        instType tau exp_ty
        return mce'

    go (ST (C tau _) s a b l) mce = do
        mu    <- askValCtxType
        omega <- newMetaTvT OmegaK l
        unifyTypes (ST omega s a b l) mu
        instType tau exp_ty
        return $ do
            ce1  <- mce
            cx   <- gensymAt "x" ce1
            ctau <- trans tau
            tellValCtx $ \ce2 -> E.bindE cx ctau ce1 ce2
            return $ E.varE cx

    go tau mce = do
        instType tau exp_ty
        return mce

checkVal :: Z.Exp -> Type -> Ti (Ti E.Exp)
checkVal e tau = tcVal e (Check tau)

inferVal :: Z.Exp -> Ti (Type, Ti E.Exp)
inferVal e = do
    ref <- newRef (error "inferVal: empty result")
    mce <- tcVal e (Infer ref)
    tau <- readRef ref
    return (tau, mce)

checkBoolVal :: Z.Exp -> Ti (Ti E.Exp)
checkBoolVal e = do
    mce <- checkExp e (BoolT l)
    return $ do ce <- mce
                return $ E.returnE ce
  where
    l :: SrcLoc
    l = srclocOf e

-- Must be kept in sync with 'KZC.Expr.Lint.inferKind'
kcType :: Type -> Expected Kind -> Ti ()
kcType tau@UnitT{} kappa_exp =
    instKind tau (qualK [EqR]) kappa_exp

kcType tau@BoolT{} kappa_exp =
    instKind tau (qualK [EqR, OrdR, BoolR]) kappa_exp

kcType tau@(IntT (U 1) _) kappa_exp =
    instKind tau (qualK [EqR, OrdR, BoolR, BitsR]) kappa_exp

kcType tau@(IntT UDefault _) kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, IntegralR, BitsR]) kappa_exp

kcType tau@(IntT U{} _) kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, IntegralR, BitsR]) kappa_exp

kcType tau@(IntT IDefault _) kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, IntegralR]) kappa_exp

kcType tau@(IntT I{} _) kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, IntegralR]) kappa_exp

kcType tau@FixT{} kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, FractionalR]) kappa_exp

kcType tau@FloatT{} kappa_exp =
    instKind tau (qualK [EqR, OrdR, NumR, FractionalR]) kappa_exp

kcType tau@StringT{} kappa_exp =
    instKind tau tauK kappa_exp

kcType tau_struct@(StructT s taus _) kappa_exp = do
    sdef <- lookupStruct s
    checkTyApp (structDefTvks sdef) taus
    maybe_tau <- checkComplexT tau_struct
    kappa'    <- case maybe_tau of
                 -- A struct has traits Eq, Ord, and Num if its elements do.
                 Just tau -> do kappa <- inferKind tau
                                case kappa of
                                  TauK (R ts) -> return $ TauK $ R (ts `intersectTraits` traits [EqR, OrdR, NumR])
                                  _           -> return tauK
                 Nothing  -> return tauK
    instKind tau_struct kappa' kappa_exp

kcType (SynT _tau1 tau2 _) kappa_exp =
    kcType tau2 kappa_exp

kcType (ArrT n tau _) kappa_exp = do
    checkKind n NatK
    checkKind tau tauK
    instKind tau tauK kappa_exp

kcType tau0@(C tau _) kappa_exp = do
    checkKind tau tauK
    instKind tau0 OmegaK kappa_exp

kcType tau@(T _) kappa_exp =
    instKind tau OmegaK kappa_exp

kcType tau0@(ST omega sigma tau1 tau2 _) kappa_exp = do
    checkKind omega OmegaK
    checkKind sigma tauK
    checkKind tau1 tauK
    checkKind tau2 tauK
    instKind tau0 MuK kappa_exp

kcType tau0@(RefT tau _) kappa_exp = do
    checkKind tau tauK
    instKind tau0 RhoK kappa_exp

kcType tau0@(FunT taus tau_ret _) kappa_exp = do
    mapM_ checkArgKind taus
    checkRetKind tau_ret
    instKind tau0 PhiK kappa_exp
  where
    checkArgKind :: Type -> Ti ()
    checkArgKind tau = do
        kappa <- inferKind tau
        case kappa of
          TauK{} -> return ()
          RhoK   -> return ()
          MuK    -> return ()
          _      -> checkKind tau tauK

    checkRetKind :: Type -> Ti ()
    checkRetKind tau = do
        kappa <- inferKind tau
        case kappa of
          TauK{} -> return ()
          MuK    -> return ()
          _      -> checkKind tau MuK

kcType tau0@NatT{} kappa_exp =
    instKind tau0 NatK kappa_exp

kcType (ForallT tvks tau _) kappa_exp =
    extendTyVars tvks $
    kcType tau kappa_exp

kcType tau0@(TyVarT tv _) kappa_exp = do
    kappa <- lookupTyVar tv
    instKind tau0 kappa kappa_exp

kcType tau0@(MetaT (MetaTv _ kappa _) _) kappa_exp =
    instKind tau0 kappa kappa_exp

instKind :: Type -> Kind -> Expected Kind -> Ti ()
instKind _ kappa (Infer ref) =
    writeRef ref kappa

instKind tau1 kappa1 (Check kappa2) =
    unifyKinds tau1 kappa1 kappa2

checkKind :: Type -> Kind -> Ti ()
checkKind tau kappa = kcType tau (Check kappa)

inferKind :: Type -> Ti Kind
inferKind tau = do
    ref <- newRef (error "inferKind: empty result")
    kcType tau (Infer ref)
    readRef ref

-- | Zonk all trait meta-variables to finalize their constituent traits.
zonkTvk :: Tvk -> Ti ()
zonkTvk (_, kappa) = compress kappa >>= go
  where
    go :: Kind -> Ti ()
    go (TauK (MetaR mrv@(MetaRv _ ts _))) = writeRv mrv (R ts)
    go _                                  = return ()

checkTyApp :: [Tvk] -> [Type] -> Ti ()
checkTyApp tvks taus = do
    checkNumTypeArgs (length taus) (length tvks)
    zipWithM_ (\(_alpha, kappa) tau -> checkKind tau kappa) tvks taus
  where
    checkNumTypeArgs :: Int -> Int -> Ti ()
    checkNumTypeArgs ntaus ntvks =
        when (ntaus /= ntvks) $
        faildoc $
        text "Expected" <+> ppr ntvks <+>
        text "type arguments matching" <+> pprForall tvks </>
        text "but got" <+> ppr ntaus <> colon <+>
        commasep (map ppr taus)

generalize :: Type -> Ti (Type, CoDecl)
generalize tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Ti (Type, CoDecl)
    go tau@(ST omega sigma tau1 tau2 l) = do
        tvks   <- gen tau
        tau    <- case tvks of
                    [] -> compress $ ST omega sigma tau1 tau2 l
                    _  -> compress $ ForallT tvks (ST omega sigma tau1 tau2 l) l
        let co =  extendTyVars tvks
        return (tau, co)

    go tau@(FunT taus tau_ret l) = do
        tvks <- gen tau
        tau  <- compress $ funT tvks taus tau_ret l
        let co mcdecl = extendTyVars tvks $ do
                        ctvks <- mapM trans tvks
                        mcdecl >>= checkLetFunE ctvks
        return (tau, co)
      where
        checkLetFunE :: [(E.TyVar, E.Kind)] -> E.Decl -> Ti E.Decl
        checkLetFunE ctvks' (E.LetFunD cf ctvks cvtaus ctau ce l) =
            return $ E.LetFunD cf (ctvks ++ ctvks') cvtaus ctau ce l

        checkLetFunE ctvks' (E.LetExtFunD cf ctvks cvtaus ctau l) =
            return $ E.LetExtFunD cf (ctvks ++ ctvks') cvtaus ctau l

        checkLetFunE _ ce =
            panicdoc $
            text "generalize: expected to coerce a letfun, but got:" <+> ppr ce

    go tau@ForallT{} =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau =
        panicdoc $ text "Asked to generalize non-ST/non-function type:" <+> (text . show) tau

    gen :: Type -> Ti [Tvk]
    gen tau = do
        mtvs     <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        alphas   <- freshVars (length mtvs) ((Set.toList . allVars) tau)
        kappas   <- mapM (inferKind . metaT) mtvs
        kappas'  <- compress kappas
        mapM_ squash (Set.toList (fvs kappas'))
        let tvks =  alphas `zip` kappas'
        extendTyVars tvks $
            zipWithM_ kcWriteTv mtvs (map tyVarT alphas)
        return $ alphas `zip` kappas'
      where
        squash :: MetaRv -> Ti ()
        squash mrv@(MetaRv _ ts _) = writeRv mrv (R ts)

instantiate :: Type -> Ti (Type, Co)
instantiate tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Ti (Type, Co)
    go (ForallT tvks (ST omega sigma tau1 tau2 l) _) = do
        (_, theta, phi) <- instTyVars tvks
        let tau = subst theta phi $ ST omega sigma tau1 tau2 l
        return (tau, id)

    go (ForallT tvks (FunT taus tau_ret l) _) =
        instFunT tvks taus tau_ret l

    go (FunT taus tau_ret l) =
        instFunT [] taus tau_ret l

    go tau =
        return (tau, id)

    instFunT :: [Tvk]
             -> [Type]
             -> Type
             -> SrcLoc
             -> Ti (Type, Co)
    instFunT tvks taus tau_ret l =do
        (mtvs, theta, phi) <- instTyVars tvks
        let tau    = FunT (subst theta phi taus) (subst theta phi tau_ret) l
        let co mce = do
                (cf, ces, l) <- mce >>= checkFunE
                cns          <- compress mtvs >>= mapM trans
                return $ E.CallE cf cns ces l
        return (tau, co)
      where
        checkFunE :: E.Exp -> Ti (E.Var, [E.Exp], SrcLoc)
        checkFunE (E.CallE cf [] ces l) =
            return (cf, ces, l)

        checkFunE ce =
            panicdoc $
            text "instantiate: expected to coerce a call, but got:" <+> ppr ce

    instTyVars :: [Tvk] -> Ti ([Type], Map TyVar Type, Set TyVar)
    instTyVars tvks = do
        mtvs      <- mapM (\(alpha, kappa) -> newMetaTvT kappa alpha) tvks
        let theta =  Map.fromList (alphas `zip` mtvs)
        let phi   =  fvs tau0 <\\> fromList alphas
        return (mtvs, theta, phi)
      where
        alphas :: [TyVar]
        alphas = map fst tvks

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

-- | Check that a type is an integral type, defaulting it to unsigned int if it
-- is not. We use this when inferring the type of a loop index variable.
checkLoopIndexVarT :: Type -> Ti ()
checkLoopIndexVarT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go IntT{} = return ()
    go tau    = unifyTypes tau intT

-- | Check that a type is an @ref \alpha@ type, returning @\alpha@.
checkRefT :: Type -> Ti Type
checkRefT tau =
    compress tau >>= go
  where
    go :: Type -> Ti Type
    go (RefT alpha _) =
        return alpha

    go tau = do
        alpha <- newMetaTvT tauK tau
        unifyTypes tau (refT alpha)
        return alpha

-- | Check that a type is an @arr \iota \alpha@ type or a reference to an @arr
-- \iota \alpha@, returning @\iota@ and @\alpha@.
checkArrT :: Type -> Ti (Type, Type)
checkArrT tau =
    compress tau >>= go
  where
    go :: Type -> Ti (Type, Type)
    go (ArrT iota alpha _) =
        return (iota, alpha)

    go (RefT (ArrT iota alpha _) _) =
        return (iota, alpha)

    go tau = do
        nat   <- newMetaTvT NatK tau
        alpha <- newMetaTvT tauK tau
        unifyTypes tau (arrT nat alpha)
        return (nat, alpha)

-- | Check that a type is a complex type, returning the type of its constituent
-- fields. A complex type has two fields named "re" and "im", in that order, and
-- both fields must have the same type.
checkComplexT :: Type -> Ti (Maybe Type)
checkComplexT (StructT struct taus _) = do
    sdef       <- lookupStruct struct
    (_, zflds) <- tyAppStruct sdef taus
    case zflds of
      [("re", tau), ("im", tau')] | tau' == tau -> return $ Just tau
      _                                         -> return Nothing

checkComplexT _ =
    return Nothing

-- | Check that a type is a struct type, returning the name of the struct.
checkStructT :: Type -> Ti (Z.Struct, [Type])
checkStructT tau =
    compress tau >>= go
  where
    go :: Type -> Ti (Z.Struct, [Type])
    go (StructT s taus _) = return (s, taus)
    go (SynT _ tau' _)    = go tau'

    go tau =
        faildoc $ nest 2 $
        text "Expected struct type, but got" <+/> ppr tau

checkStructFieldT :: StructDef -> [Type] -> Z.Field -> Ti Type
checkStructFieldT sdef taus f = do
    (_, flds) <- tyAppStruct sdef taus
    case lookup f flds of
      Just tau -> return tau
      Nothing  -> faildoc $ text "Unknown field" <+> enquote (ppr f)

-- | Check that a type is an @ST (C ()) \sigma \alpha \beta@ type, returning the
-- three type indices
checkSTCUnit :: Type -> Ti (Type, Type, Type)
checkSTCUnit tau =
    compress tau >>= go
  where
    go :: Type -> Ti (Type, Type, Type)
    go (ST (C (UnitT _) _) sigma alpha beta _) =
        return (sigma, alpha, beta)

    go tau = do
        sigma <- newMetaTvT tauK tau
        alpha <- newMetaTvT tauK tau
        beta  <- newMetaTvT tauK tau
        unifyTypes tau (stT (cT unitT) sigma alpha beta)
        return (sigma, alpha, beta)

checkFunT :: Z.Var -> Maybe [Type] -> Int -> Type
          -> Ti ([Type], Type, Co)
checkFunT f Nothing nargs tau =
    instantiate tau >>= go
  where
    go :: (Type, Co) -> Ti ([Type], Type, Co)
    go (FunT taus tau_ret _, co) =
        return (taus, tau_ret, co)

    go (tau_f, co) = do
        taus    <- replicateM nargs (newMetaTvT tauK tau)
        tau_ret <- newMetaTvT tauK tau
        unifyTypes tau_f (funT [] taus tau_ret (srclocOf f))
        return (taus, tau_ret, co)

checkFunT _f (Just taus) _nargs (ForallT tvks (FunT taus_params tau_ret _) _) = do
    checkTyApp tvks taus
    let theta :: Map TyVar Type
        theta = Map.fromList (map fst tvks `zip` taus)
    return (subst theta mempty taus_params, subst theta mempty tau_ret, id)

checkFunT _f Just{} _ tau =
    faildoc $
    align $ nest 2 $
    text "Illegal explicit type application for unquantified type" <+>
    enquote (ppr tau)

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
          FunT [c] tau_ret@ForallT{} _ -> return (c, tau_ret)
          _ -> err
    -- Check that the return type of the function we are mapping is
    -- @forall s a b . ST tau s a b@.
    checkMapReturnType tau_ret
    -- XXX Instantiate over the return type, which must be an ST type. We should
    -- handle pure functions here too!
    (tau_ret', co2) <- instantiate tau_ret
    (d, s, a, b) <-
        case tau_ret' of
          ST (C d _) s a b _ -> return (d, s, a, b)
          _ -> err
    unifyTypes c a
    unifyTypes s a
    unifyTypes d b
    let co mce = co2 $ co1 $ do cf <- trans f
                                ce <- mce
                                return $ E.callE cf [ce]
    return (a, b, co)
  where
    checkMapReturnType :: Type -> Ti ()
    checkMapReturnType (ForallT [(s,_), (a,_), (b,_)] (ST _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) _)
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
            FunT [tyVarT gamma]
                 (forallST [sigma, alpha, beta]
                     (C (tyVarT delta) l)
                     (tyVarT sigma)
                     (tyVarT alpha)
                     (tyVarT beta)
                     l)
                 l

    l :: SrcLoc
    l = srclocOf tau

-- | Check for unresolved type meta-variables in a binder's type.
checkUnresolvedMtvs :: Z.Var -> Type -> Ti ()
checkUnresolvedMtvs v tau = do
    tau' <- compress tau
    let mtvs :: [MetaTv]
        mtvs = Set.toList $ fvs tau'
    check "Ambiguous array length" (filter isNatMetaTv mtvs)
    check "Ambiguous type" (filter (not . isNatMetaTv) mtvs)
  where
      isNatMetaTv :: MetaTv -> Bool
      isNatMetaTv (MetaTv _ NatK _) = True
      isNatMetaTv _                 = False

      check :: String -> [MetaTv] -> Ti ()
      check _ [] =
          return ()

      check msg mtvs = do
          tau':mtvs' <- sanitizeTypes (tau : map metaT mtvs)
          faildoc $
              text (plural msg mtvs') <> colon <+> commasep (map ppr mtvs') </>
              text "In declaration:" </>
              indent 2 (ppr v <+> colon <+> ppr tau')
        where
          plural :: String -> [a] -> String
          plural s [_] = s
          plural s _   = s ++ "s"

mkSTC :: Type -> Ti Type
mkSTC tau = do
    s <- newMetaTvT tauK l
    a <- newMetaTvT tauK l
    b <- newMetaTvT tauK l
    return $ ST (C tau l) s a b l
  where
    l :: SrcLoc
    l = srclocOf tau

mkSTOmega :: Ti Type
mkSTOmega = do
    omega <- newMetaTvT OmegaK l
    s     <- newMetaTvT tauK l
    a     <- newMetaTvT tauK l
    b     <- newMetaTvT tauK l
    return $ ST omega s a b l
  where
    l :: SrcLoc
    l = noLoc

-- | @castVal tau e@ infers the type of @e@ and, if possible, generates an appropriate
-- cast to the type @tau@. It returns an elaborated value expression. We special
-- case casting array expressions---array expressions are the only time we cast
-- between arrays types. This is all we need for the common case of arrays of
-- integers that need to be represented as arrays on, say, int8's, and it is
-- also the only case where we know we can make casting memory efficient.
castVal :: Type -> Z.Exp -> Ti (Ti E.Exp)
castVal tau2 e0 = do
    (tau1, mce) <- inferVal e
    co <- case (e, tau1, tau2) of
            (Z.ArrayE es _, ArrT iota1 etau1 _, ArrT iota2 etau2 _) -> do
                unifyTypes iota1 iota2
                co <- mkArrayCast etau1 etau2
                mapM_ (\e -> checkSafeCast WarnUnsafeAutoCast (Just e) etau1 etau2) es
                return co
            _ -> mkCheckedSafeCast e tau1 tau2
    return $ co mce
  where
    e :: Z.Exp
    e = constFold e0

    mkArrayCast :: Type -> Type -> Ti Co
    mkArrayCast tau1 tau2 = do
        co <- mkCast tau1 tau2
        return $ \mce -> do
            (ces, l) <- mce >>= checkArrayE
            ces'     <- mapM (co . return) ces
            return $ E.ArrayE ces' l

    checkArrayE :: E.Exp -> Ti ([E.Exp], SrcLoc)
    checkArrayE (E.ArrayE ces l) =
        return (ces, l)

    checkArrayE e =
        faildoc $ nest 2 $
        text "Expected array expression but got:" <+/> ppr e

-- | Construct a coercion from @tau1@ to @tau2@.
mkCast :: Type -> Type -> Ti Co
mkCast tau1 tau2 = do
    checkLegalCast tau1 tau2
    return $ \mce -> do
        tau1' <- compress tau1
        tau2' <- compress tau2
        go tau1' tau2' mce
  where
    go :: Type -> Type -> Co
    go tau1 tau2 mce | tau1 == tau2 =
        mce

    go (SynT _ tau1 _) tau2 mce =
        go tau1 tau2 mce

    go tau1 (SynT _ tau2 _) mce =
        go tau1 tau2 mce

    go (StructT zs1 taus1 _) (StructT zs2 taus2 _) mce | zs2 == zs1 && length taus2 == length taus1 =
        mkStructCast zs1 taus1 taus2 mce

    go _ tau2 mce = do
        ctau <- trans tau2
        ce   <- mce
        return $ E.castE ctau ce

-- | Construct a cast between two instantiations of a struct at different types.
mkStructCast :: Z.Struct -> [Type] -> [Type] -> Co
mkStructCast zs taus1 taus2 mce = do
    sdef        <- lookupStruct zs
    (_, zflds1) <- tyAppStruct sdef taus1
    (_, zflds2) <- tyAppStruct sdef taus2
    fs          <- mapM (trans . fst) zflds1
    coercions   <- zipWithM (\(_, tau1) (_, tau2) -> mkCast tau1 tau2) zflds1 zflds2
    cs          <- trans zs
    ctaus2      <- mapM trans taus2
    ce1         <- mce
    mkLetE (structT zs taus1) ce1 $ \cx -> do
        ces <- zipWithM ($) coercions [return $ E.projE cx f | f <- fs]
        return $ E.structE cs ctaus2 (fs `zip` ces)

mkCheckedSafeCast :: Z.Exp -> Type -> Type -> Ti Co
mkCheckedSafeCast e tau1 tau2 = do
    co <- mkCast tau1 tau2
    checkSafeCast WarnUnsafeAutoCast (Just e) tau1 tau2
    return co

-- | Cast an expression of the given type to a type on which we can perform but
-- operations.
mkBits :: Z.Exp -> Type -> Ti (Type, Co)
mkBits e tau = do
    tau' <- mkUnsigned tau
    co   <- mkCheckedSafeCast e tau tau'
    return (tau', co)

-- | @mkCastT tau1 tau2@ generates a computation of type @ST T tau1 tau2@ that
-- casts values from @tau1@ to @tau2@.
mkCastT :: Type -> Type -> Ti Co
mkCastT tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti Co
    -- This is a quick, incomplete check to see if we can avoid a cast.
    go tau1 tau2 | tau1 == tau2 =
        return id

    go (SynT _ tau1 _) tau2 =
        go tau1 tau2

    go tau1 (SynT _ tau2 _) =
        go tau1 tau2

    go tau1 tau2 = do
        checkSafeCast WarnUnsafeParAutoCast Nothing tau1 tau2
        co <- mkCast tau1 tau2
        return $ \mce -> do
            ce    <- mce
            ctau1 <- trans tau1
            ctau2 <- trans tau2
            castComp ctau1 ctau2 co ce
      where
        castComp :: E.Type -> E.Type -> Co -> E.Exp -> Ti E.Exp
        -- @tau1@ and @tau2@ my be unequal due only to differing meta-variables
        -- that are eventually unified, so the check above is incomplete. We
        -- therefore do a second check to see if @ctau2@ and @ctau1@ are
        -- equivalent.
        castComp ctau1 ctau2 co c
            | ctau2 == ctau1 = return c
            | otherwise      = do cpipe <- mkPipe ctau1 co
                                  return $ E.ParE E.AutoPipeline ctau1 c cpipe l
          where
            l :: SrcLoc
            l = srclocOf c

        -- | Given a type tau1 and a coercion from expressions of type tau1 to
        -- expressions of type tau2, return a transformer that reads values of
        -- type tau1 and writes coerced values of type tau2.
        mkPipe :: E.Type -> Co -> Ti E.Exp
        mkPipe ctau1 co = do
            cx    <- gensymAt "x" tau1
            cxe   <- co $ return (E.varE cx)
            return $ E.repeatE $
                     E.bindE cx ctau1 (E.takeE ctau1) $
                     E.emitE cxe

-- | @checkLegalCast tau1 tau2@ checks that a value of type @tau1@ can be
-- legally cast to a value of type @tau2@.
checkLegalCast :: Type -> Type -> Ti ()
checkLegalCast tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti ()
    go tau1 tau2 | tau1 == tau2 =
        return ()

    go (SynT _ tau1 _) tau2 =
        go tau1 tau2

    go tau1 (SynT _ tau2 _) =
        go tau1 tau2

    go IntT{} IntT{} =
        return ()

    go IntT{} FixT{} =
        return ()

    go IntT{} FloatT{} =
        return ()

    go FixT{} IntT{} =
        return ()

    go FixT{} FixT{} =
        return ()

    go FixT{} FloatT{} =
        return ()

    go FloatT{} IntT{} =
        return ()

    go FloatT{} FixT{} =
        return ()

    go FloatT{} FloatT{} =
        return ()

    go (StructT s taus _) (StructT s' taus' _) | s' == s && length taus' == length taus =
        zipWithM_ go taus taus'

    go tau1@IntT{} tau2@TyVarT{} =
        polyCast tau1 tau2

    go tau1@FixT{} tau2@TyVarT{} =
        polyCast tau1 tau2

    go tau1@FloatT{} tau2@TyVarT{} =
        polyCast tau1 tau2

    go tau1@TyVarT{} tau2@IntT{} =
        polyCast tau1 tau2

    go tau1@TyVarT{} tau2@FixT{} =
        polyCast tau1 tau2

    go tau1@TyVarT{} tau2@FloatT{} =
        polyCast tau1 tau2

    go tau1 tau2 =
        unifyTypes tau1 tau2
      `catch` \(_ :: UnificationException) -> cannotCast tau1 tau2

    -- | Polymorphic cast from type @tau1@ to type @tau2@. We use this to cast a
    -- constant to a polymorphic type.
    polyCast :: Type -> Type -> Ti ()
    polyCast tau1 tau2 = do
        kappa <- constKind tau1
        checkKind tau2 kappa `catch` \(_ :: SomeException) -> cannotCast tau1 tau2

    -- | Return the kind of constants of the given type. We use this to cast
    -- constants "polymorphically."
    constKind :: Type -> Ti Kind
    constKind IntT{}   = return numK
    constKind FixT{}   = return fracK
    constKind FloatT{} = return fracK
    constKind tau      = inferKind tau

    cannotCast :: Type -> Type -> Ti ()
    cannotCast tau1 tau2 = do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        faildoc $ text "Cannot cast" <+> enquote (ppr tau1') <+>
                  text "to" <+> enquote (ppr tau2')

checkLegalBitcast :: Type -> Type -> Ti ()
checkLegalBitcast tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti ()
    go tau1 tau2 = do
        checkKind tau1 tauK
        checkKind tau2 tauK
        w1 <- typeSize tau1
        w2 <- typeSize tau2
        when (w2 /= w1) $
            faildoc $
            text "Cannot bitcast between types with differing widths" <+>
            ppr w1 <+> text "and" <+> ppr w2

-- | Check whether casting the given expression from @tau1@ to @tau2@ is safe.
-- If it is definitely unsafe, signal an error; if it may be unsafe, signal a
-- warning if the specified warning flag is set. We assume the cast is legal.
checkSafeCast :: WarnFlag -> Maybe Z.Exp -> Type -> Type -> Ti ()
checkSafeCast _f (Just e@(Z.ConstE (Z.IntC _ x) _)) _tau1 (IntT ip _) =
    withSummaryContext e $ checkSafeIntCast x ip

checkSafeCast f e tau1@(IntT ip1 _) tau2@(IntT ip2 _) =
    maybeWithSummaryContext e $ do
    w1 <- ipBitSize ip1
    w2 <- ipBitSize ip2
    when (w1 > w2) $
        warndocWhen f $ align $
        text "Potentially unsafe auto cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2
    when (ipIsSigned ip2 /= ipIsSigned ip1) $
        warndocWhen f $ align $
        text "Potentially unsafe auto cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2

checkSafeCast _f (Just e@(Z.ConstE (Z.IntC _ x) _)) _tau1 (FixT qp _) =
    withSummaryContext e $ checkSafeFixCast (realToFrac x) qp

checkSafeCast _f (Just e@(Z.ConstE (Z.FixC zqp x) _)) _tau1 (FixT qp' _) = do
    qp <- fromZ zqp
    withSummaryContext e $ checkSafeFixCast (qpToFractional qp x) qp'

checkSafeCast _f (Just e@(Z.ConstE (Z.FloatC _ x) _)) _tau1 (FixT qp _) =
    withSummaryContext e $ checkSafeFixCast x qp

checkSafeCast _f _e _tau1 _tau2 =
    return ()

checkSafeIntCast :: Int -> IP -> Ti ()
checkSafeIntCast x ip = do
    (i_min, i_max) <- ipRange ip
    when (x < i_min || x > i_max) $
      faildoc $ align $
      text "Constant" <+> enquote (ppr x) <+>
      text "cannot be represented as type" <+> enquote (ppr (IntT ip noLoc))

checkSafeFixCast :: Double -> QP -> Ti ()
checkSafeFixCast x qp = do
    when (x < q_min || x > q_max) $
      faildoc $ align $
      text "Constant" <+> enquote (ppr x) <+>
      text "cannot be represented as type" <+> enquote (ppr (FixT qp noLoc)) <>
      comma <+> text "which has range" <+>
      text "[" <> ppr q_min <> comma <+> ppr q_max <> text ")"
  where
    q_min, q_max0, q_max :: Double
    (q_min, q_max0) = qpRange qp
    q_max = q_max0 + qpResolution qp

-- | Perform constant folding. This does a very limited amount of
-- "optimization," mainly so that we can give decent errors during implicit
-- casts regarding integral constants being too large.
constFold :: Z.Exp -> Z.Exp
constFold (Z.ArrayE es l) =
    Z.ArrayE (map constFold es) l

constFold (Z.UnopE Z.Neg (Z.ConstE (Z.IntC ip r) l) _) =
    Z.ConstE (Z.IntC (toSigned ip) (negate r)) l
  where
    toSigned :: Z.IP -> Z.IP
    toSigned Z.UDefault = Z.IDefault
    toSigned (Z.U w)    = Z.I w
    toSigned ip         = ip

constFold (Z.BinopE op e1 e2 l) =
    constFoldBinopE op (constFold e1) (constFold e2)
  where
    constFoldBinopE :: Z.Binop -> Z.Exp -> Z.Exp -> Z.Exp
    constFoldBinopE op (Z.ConstE (Z.IntC ip x) _) (Z.ConstE (Z.IntC ip' y) _)
        | ip' == ip, Just z <- constFoldBinop op x y =
           Z.ConstE (Z.IntC ip z) l

    constFoldBinopE op e1 e2 = Z.BinopE op e1 e2 l

    constFoldBinop :: Z.Binop -> Int -> Int -> Maybe Int
    constFoldBinop Z.Add x y = Just $ x + y
    constFoldBinop Z.Sub x y = Just $ x - y
    constFoldBinop Z.Mul x y = Just $ x * y
    constFoldBinop Z.Pow x y = Just $ x ^ y
    constFoldBinop _     _ _ = Nothing

constFold e = e

-- | Implement the join operation for types of kind omega
joinOmega :: Type -> Type -> Ti Type
joinOmega tau1 tau2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' tau2'
  where
    go :: Type -> Type -> Ti Type
    go tau1@C{} T{}      = return tau1
    go T{}      tau2@C{} = return tau2
    go tau1@T{} T{}      = return tau1

    go tau1 tau2 =
        faildoc $ text "Cannot join" <+> enquote (ppr tau1) <+>
                  text "and" <+> enquote (ppr tau2)

instType :: Type -> Expected Type -> Ti ()
instType tau1 (Infer ref)  = writeRef ref tau1
instType tau1 (Check tau2) = unifyTypes tau1 tau2

-- | Throw a "Expected type.." error. @tau1@ is the type we got, and @tau2@ is
-- the expected type.
expectedTypeErr :: Type -> Type -> Ti a
expectedTypeErr tau1 tau2 = do
    msg            <- relevantBindings
    [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
    faildoc $
      text "Expected type:" <+> enquote (ppr tau2') </>
      text "but got:      " <+> enquote (ppr tau1') </>
      msg

-- | Generic unification exception
data UnificationException = forall a . Exception a => UnificationException a
  deriving Typeable

instance Show UnificationException where
    show (UnificationException e) = show e

instance Exception UnificationException

unificationToException :: Exception a => a -> SomeException
unificationToException = toException . UnificationException

unificationFromException :: Exception a => SomeException -> Maybe a
unificationFromException x = do
    UnificationException a <- fromException x
    cast a

-- | Type unification exception
data TypeUnificationException = TypeUnificationException Type Type Doc
  deriving (Typeable)

instance Show TypeUnificationException where
    show (TypeUnificationException tau1 tau2 msg) =
        pretty 80 $
        text "Expected type:" <+> ppr tau2 </>
        text "but got:      " <+> ppr tau1 </>
        msg

instance Exception TypeUnificationException where
    toException   = unificationToException
    fromException = unificationFromException

-- | Kind unification exception
data KindUnificationException = KindUnificationException Type Kind Kind Doc
  deriving (Typeable)

instance Show KindUnificationException where
    show (KindUnificationException tau1 kappa1 kappa2 msg) =
        pretty 80 $
        text "Expected:" <+> friendly kappa2 </>
        text "but got: " <+> ppr tau1 </>
        text "which is a" <+> friendly kappa1 </>
        msg
      where
        friendly :: Kind -> Doc
        friendly TauK{}  = text "base type"
        friendly OmegaK  = text "'C tau' or 'T'"
        friendly MuK     = text "type of the form 'ST omega tau tau'"
        friendly RhoK    = text "mutable type"
        friendly PhiK    = text "function type"
        friendly NatK    = text "type level natural"
        friendly MetaK{} = error "internal error: failed to unify kind meta-variable"

instance Exception KindUnificationException where
    toException   = unificationToException
    fromException = unificationFromException

-- | Unify two types. The first argument is what we got, and the second is what
-- we expect.
unifyTypes :: Type -> Type -> Ti ()
unifyTypes tau1_0 tau2_0 = do
    tau1' <- compress tau1_0
    tau2' <- compress tau2_0
    unify tau1' tau2'
  where
    -- Not that we must call 'unifyTypes' instead of 'unify' if there is a
    -- chance we have updated a type meta-variable, which means we need to
    -- perform path compression again.
    unify :: Type -> Type -> Ti ()
    unify tau1 tau2 | tau1 == tau2 =
        return ()

    unify tau1@(MetaT mtv@(MetaTv _ kappa1 _) _) tau2@(MetaT (MetaTv _ kappa2 _) _) = do
        unifyKinds tau1 kappa1 kappa2
        updateMetaTv mtv tau1 tau2

    unify tau1@(MetaT mtv@(MetaTv _ kappa1 _) _) tau2 = do
        kappa2 <- inferKind tau2
        unifyKinds tau1 kappa1 kappa2
        updateMetaTv mtv tau1 tau2

    unify tau1 tau2@(MetaT mtv@(MetaTv _ kappa2 _) _) = do
        kappa1 <- inferKind tau1
        unifyKinds tau1 kappa1 kappa2
        updateMetaTv mtv tau2 tau1

    unify (SynT _ tau1 _) tau2 =
        unify tau1 tau2

    unify tau1 (SynT _ tau2 _) =
        unify tau1 tau2

    unify UnitT{} UnitT{} = return ()
    unify BoolT{} BoolT{} = return ()

    unify (IntT ip _)   (IntT ip' _)   | ip' == ip = return ()
    unify (FixT qp _)   (FixT qp' _)   | qp' == qp = return ()
    unify (FloatT fp _) (FloatT fp' _) | fp' == fp = return ()
    unify StringT{}     StringT{}                  = return ()

    unify (StructT s1 taus1 _) (StructT s2 taus2 _) | s1 == s2 && length taus1 == length taus2 =
        zipWithM_ unifyTypes taus1 taus2

    unify (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify tau1a tau1b
        unifyTypes tau2a tau2b

    unify (C tau1 _) (C tau2 _) =
        unify tau1 tau2

    unify T{} T{} =
        return ()

    unify tau1@(ForallT tvks_a tau_a _) (ForallT tvks_b tau_b _) | length tvks_a == length tvks_b = do
        zipWithM_ (unifyKinds tau1) (map snd tvks_a) (map snd tvks_b)
        extendTyVars tvks_b $
          unify tau_a' tau_b
      where
        tau_a' :: Type
        tau_a' = subst theta mempty tau_a

        theta :: Map TyVar Type
        theta = Map.fromList [(alpha, tyVarT beta) | (alpha, beta) <- map fst tvks_a `zip` map fst tvks_b]

    unify (ST omega_a tau_1a tau_2a tau_3a _) (ST omega_b tau_1b tau_2b tau_3b _) = do
        unify omega_a omega_b
        unifyTypes tau_1a tau_1b
        unifyTypes tau_2a tau_2b
        unifyTypes tau_3a tau_3b

    unify (RefT tau1 _) (RefT tau2 _) =
        unify tau1 tau2

    unify (FunT taus_a tau_a _) (FunT taus_b tau_b _) | length taus_a == length taus_b = do
          zipWithM_ unifyTypes taus_a taus_b
          unifyTypes tau_a tau_b

    unify (NatT i1 _) (NatT i2 _) | i1 == i2 =
        return ()

    unify (TyVarT tv1 _) (TyVarT tv2 _) | tv1 == tv2 =
        return ()

    unify tau1 tau2 = do
        msg <- relevantBindings
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        throw $ TypeUnificationException tau1' tau2' msg

    updateMetaTv :: MetaTv -> Type -> Type -> Ti ()
    updateMetaTv mtv tau1 tau2 = do
        mtvs2 <- metaTvs [tau2]
        when (mtv `elem` mtvs2) $ do
            [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
            faildoc $ nest 2 $
              text "Cannot construct the infinite type:" <+/>
              ppr tau1' <+> text "=" <+> ppr tau2'
        kcWriteTv mtv tau2

-- | Unify two types. The first argument is what we got, and the second is what
-- we expect.
unifyKinds :: Type -> Kind -> Kind -> Ti ()
unifyKinds tau1 kappa1 kappa2 = do
    kappa1' <- compress kappa1
    kappa2' <- compress kappa2
    go kappa1' kappa2'
  where
    go :: Kind -> Kind -> Ti ()
    go (MetaK mkv1) (MetaK mkv2) | mkv1 == mkv2 =
        return ()

    go kappa1@(MetaK mkv) kappa2 =
        updateMetaKv mkv kappa1 kappa2

    go kappa1 kappa2@(MetaK mkv) =
        updateMetaKv mkv kappa2 kappa1

    go (TauK r1) (TauK r2) = unifyTraits tau1 r1 r2
    go OmegaK{}  OmegaK{}  = return ()
    go MuK{}     MuK{}     = return ()
    go RhoK{}    RhoK{}    = return ()
    go PhiK{}    PhiK{}    = return ()
    go NatK{}    NatK{}    = return ()

    go kappa1 kappa2 = do
        msg <- relevantBindings
        [tau1'] <- sanitizeTypes [tau1]
        throw $ KindUnificationException tau1' kappa1 kappa2 msg

    updateMetaKv :: MetaKv -> Kind -> Kind -> Ti ()
    updateMetaKv mkv _kappa1 kappa2 =
        writeKv mkv kappa2

-- | Unify two sets of traits. The first argument is what we got, and the second
-- is what we expect.
unifyTraits :: Type -> R -> R -> Ti ()
unifyTraits tau1 r1 r2 = do
    r1' <- compress r1
    r2' <- compress r2
    go r1' r2'
  where
    go :: R -> R -> Ti ()
    go (MetaR mrv1) (MetaR mrv2) | mrv1 == mrv2 =
        return ()

    go r1@(MetaR mrv1@(MetaRv _ ts1 _)) r2@(MetaR mrv2@(MetaRv _ ts2 _))
      | ts1 `impliesTraits` ts2 = writeRv mrv2 r1
      | ts2 `impliesTraits` ts1 = writeRv mrv1 r2
      | otherwise               = do mrv' <- newMetaRv (ts1 <> ts2)
                                     writeRv mrv1 (MetaR mrv')
                                     writeRv mrv2 (MetaR mrv')

    go (MetaR mrv@(MetaRv _ ts1 _)) (R ts2)
      | ts1 `impliesTraits` ts2 = return ()
      | otherwise               = do mrv' <- newMetaRv (ts1 <> ts2)
                                     writeRv mrv (MetaR mrv')

    -- We have to throw an error here if ts1 does not imply ts2 unlike the
    -- previous case where we can always increase teh set of traits associated
    -- with a MetaR variable.
    go (R ts1) (MetaR (MetaRv _ ts2 _))
      | ts1 `impliesTraits` ts2 = return ()
      | otherwise               = traitsError ts1 ts2

    go (R ts1) (R ts2) =
        unless (ts1 `impliesTraits` ts2) $
          traitsError ts1 ts2

    traitsError :: Traits -> Traits -> Ti ()
    traitsError ts1 ts2 = do
        tau1'    <- compress tau1
        [tau1''] <- sanitizeTypes [tau1']
        alwaysWithLocContext tau1'' (text "When considering type:" <+> ppr tau1'') $
          faildoc $ align $
          text "Expected traits:" <+> pprTraits ts2 </>
          text "but got:        " <+> pprTraits ts1
      where
        pprTraits :: Traits -> Doc
        pprTraits ts
          | nullTraits ts = text "no traits"
          | otherwise     = ppr ts

-- | Type check two expressions, treating them as values, and attempt to unify their types. This may
-- requires adding casts.
unifyValTypes :: Z.Exp -> Z.Exp -> Ti (Type, Ti E.Exp, Ti E.Exp)
unifyValTypes e1 e2 = do
    (tau1, mce1) <- inferVal e1
    (tau2, mce2) <- inferVal e2
    unifyCompiledExpTypes tau1 e1 mce1 tau2 e2 mce2

-- | Attempt to unify the types of two Ziria expressions that have already been
-- type checked and elaborated, inserting appropriate coercions into the
-- elaborated terms.
unifyCompiledExpTypes :: Type -> Z.Exp -> Ti E.Exp
                      -> Type -> Z.Exp -> Ti E.Exp
                      -> Ti (Type, Ti E.Exp, Ti E.Exp)
unifyCompiledExpTypes tau1 e1 mce1 tau2 e2 mce2 = do
    tau1' <- compress tau1
    tau2' <- compress tau2
    go tau1' e1 mce1 tau2' e2 mce2
  where
    go :: Type -> Z.Exp -> Ti E.Exp
       -> Type -> Z.Exp -> Ti E.Exp
       -> Ti (Type, Ti E.Exp, Ti E.Exp)
    go (SynT _ tau1 _) e1 mce1 tau2 e2 mce2 =
        go tau1 e1 mce1 tau2 e2 mce2

    go tau1 e1 mce1 (SynT _ tau2 _) e2 mce2 =
        go tau1 e1 mce1 tau2 e2 mce2

    go tau1@MetaT{} _ mce1 tau2 _ mce2 = do
        unifyTypes tau1 tau2
        return (tau2, mce1, mce2)

    go tau1 _ mce1 tau2@MetaT{} _ mce2 = do
        unifyTypes tau2 tau1
        return (tau1, mce1, mce2)

    go tau1 _ mce1 tau2 _ mce2 | tau1 == tau2 =
        return (tau1, mce1, mce2)

    -- Always cast integer constants to whatever the other type is. This lets
    -- us, for example, treat @1@ as an @int8@.
    go tau1@IntT{} e@Z.ConstE{} mce1 tau2 _ mce2 = do
        co <- mkCheckedSafeCast e tau1 tau2
        return (tau2, co mce1, mce2)

    go tau1 _ mce1 tau2@IntT{} e@Z.ConstE{} mce2 = do
        co <- mkCheckedSafeCast e tau2 tau1
        return (tau1, mce1, co mce2)

    -- Always cast floating-point constants to fractional types. This lets us,
    -- for example, treat @1.0@ as a @q1.14@.
    go tau1@FloatT{} e@Z.ConstE{} mce1 tau2 _ mce2 | isFracT tau2 = do
        co <- mkCheckedSafeCast e tau1 tau2
        return (tau2, co mce1, mce2)

    go tau1 _ mce1 tau2@FloatT{} e@Z.ConstE{} mce2 | isFracT tau1 = do
        co <- mkCheckedSafeCast e tau2 tau1
        return (tau1, mce1, co mce2)

    go tau1 e1 mce1 tau2 e2 mce2 = do
        tau <- lubType tau1 tau2
        co1 <- mkCheckedSafeCast e1 tau1 tau
        co2 <- mkCheckedSafeCast e2 tau2 tau
        return (tau, co1 mce1, co2 mce2)

    lubType :: Type -> Type -> Ti Type
    lubType (IntT ip l) (IntT ip' _) = do
        ip'' <- lubIP ip ip'
        return $ IntT ip'' l

    lubType (FixT qp l) (FixT qp' _) = do
        qp'' <- lubQP qp qp'
        return $ FixT qp'' l

    lubType (FloatT fp l) (FloatT fp' _) =
        return $ FloatT (max fp fp') l

    lubType IntT{} tau@FixT{} =
        return tau

    lubType tau@FixT{} IntT{}  =
        return tau

    lubType IntT{} tau@FloatT{} =
        return tau

    lubType tau@FloatT{} IntT{} =
        return tau

    lubType FixT{} tau@FloatT{} =
        return tau

    lubType tau@FloatT{} FixT{} =
        return tau

    lubType (StructT s taus l) (StructT s' taus' _) | s' == s && length taus' == length taus = do
        taus'' <- zipWithM lubType taus taus'
        return $ StructT s taus'' l

    lubType tau1@IntT{} tau2 = do
        unifyTypes tau2 tau1
        return tau1

    lubType tau1@FloatT{} tau2 = do
        unifyTypes tau2 tau1
        return tau1

    lubType tau1 tau2 = do
        unifyTypes tau1 tau2
        return tau1

    lubIP :: IP -> IP -> Ti IP
    lubIP ip ip' = do
        w  <- ipBitSize ip
        w' <- ipBitSize ip'
        if ipIsSigned ip || ipIsSigned ip'
          then return $ I (max w w')
          else return $ U (max w w')

    lubQP :: QP -> QP -> Ti QP
    lubQP qp qp' = do
        if qpIsSigned qp || qpIsSigned qp'
          then return $ Q  (max m m') (max n n')
          else return $ UQ (max m m') (max n n')
      where
        (m, n)   = (qpIntBits qp, qpFracBits qp)
        (m', n') = (qpIntBits qp', qpFracBits qp')

traceVar :: Z.Var -> Type -> Ti ()
traceVar v tau = do
    [tau'] <- sanitizeTypes [tau]
    traceTc $ text "Variable" <+> ppr v <+> colon <+> ppr tau'

class FromZ a b where
    fromZ :: a -> Ti b

instance FromZ Z.TyVar TyVar where
    fromZ (Z.TyVar n) = pure $ TyVar n

instance FromZ Z.IP IP where
    fromZ Z.IDefault = pure IDefault
    fromZ (Z.I w)    = pure $ I w
    fromZ Z.UDefault = pure UDefault
    fromZ (Z.U w)    = pure $ U w

instance FromZ Z.QP QP where
    fromZ (Z.Q i f)  = pure $ Q i f
    fromZ (Z.UQ i f) = pure $ UQ i f

instance FromZ Z.FP FP where
    fromZ Z.FP16 = pure FP16
    fromZ Z.FP32 = pure FP32
    fromZ Z.FP64 = pure FP64

instance FromZ Z.Type Type where
    fromZ (Z.UnitT l)          = pure $ UnitT l
    fromZ (Z.BoolT l)          = pure $ BoolT l
    fromZ (Z.IntT ip l)        = IntT <$> fromZ ip <*> pure l
    fromZ (Z.FixT qp l)        = FixT <$> fromZ qp <*> pure l
    fromZ (Z.FloatT fp l)      = FloatT <$> fromZ fp <*> pure l
    fromZ (Z.ArrT i tau l)     = ArrT <$> fromZ i <*> fromZ tau <*> pure l
    fromZ (Z.C tau l)          = C <$> fromZ tau <*> pure l
    fromZ (Z.T l)              = T <$> pure l
    fromZ (Z.TyVarT alpha l)   = TyVarT <$> fromZ alpha <*> pure l

    fromZ (Z.StructT s ztaus _) = do
        taus     <- mapM fromZ ztaus
        sdef     <- lookupStruct s
        (tau, _) <- tyAppStruct sdef taus
        return tau

    fromZ (Z.ST omega tau1 tau2 l) =
        ST <$> fromZ omega <*> newMetaTvT tauK l <*>
               fromZ tau1 <*> fromZ tau2 <*> pure l

    fromZ (Z.NatT i l) =
        pure $ NatT i l

    fromZ (Z.LenT v _) = do
        (n, _) <- lookupVar v >>= checkArrT
        return n

    fromZ (Z.UnknownT l) =
        newMetaTvT NatK l

    fromZ (Z.ForallT tvks tau l) =
        ForallT <$> mapM fromZ tvks <*> fromZ tau <*> pure l

instance FromZ Z.Kind Kind where
    fromZ (Z.TauK ts) = return $ TauK (R ts)
    fromZ Z.NatK      = return NatK

instance FromZ (Z.TyVar, Maybe Z.Kind) Tvk where
    fromZ (zalpha, Nothing) = do
        alpha <- fromZ zalpha
        kappa <- newMetaKvK NoLoc
        return (alpha, kappa)

    fromZ (zalpha, Just zkappa) = do
        alpha <- fromZ zalpha
        kappa <- fromZ zkappa
        return (alpha, kappa)

instance FromZ (Maybe Z.Type, Kind) Type where
    fromZ (Just tau, _)    = fromZ tau
    fromZ (Nothing, kappa) = newMetaTvT kappa NoLoc

instance FromZ Z.VarBind (Z.Var, Type) where
    fromZ (Z.VarBind v False ztau) = do
          tau <- fromZ (ztau, tauK)
          return (v, tau)

    fromZ (Z.VarBind v True ztau) = do
          tau <- refT <$> fromZ (ztau, tauK)
          return (v, tau)

instance FromZ [Z.VarBind] [(Z.Var, Type)] where
    fromZ [] =
        return []

    fromZ (Z.VarBind v False ztau : vbs) = do
          tau  <- fromZ (ztau, tauK)
          vbs' <- extendVars [(v, tau)] $
                  fromZ vbs
          return $ (v, tau) : vbs'

    fromZ (Z.VarBind v True ztau : vbs) = do
          tau  <- refT <$> fromZ (ztau, tauK)
          vbs' <- extendVars [(v, tau)] $
                  fromZ vbs
          return $ (v, tau) : vbs'

class Trans a b | b -> a where
    trans :: a -> Ti b

instance Trans Z.Var E.Var where
    trans (Z.Var n) = pure $ E.Var n

instance Trans Z.Field E.Field where
    trans (Z.Field n) = pure $ E.Field n

instance Trans Z.Struct E.Struct where
    trans (Z.Struct n) = pure $ E.Struct n

instance Trans TyVar E.TyVar where
    trans (TyVar n) = pure $ E.TyVar n

instance Trans IP E.IP where
    trans = pure

instance Trans QP E.QP where
    trans = pure

instance Trans FP E.FP where
    trans = pure

instance Trans Type E.Type where
    trans tau = compress tau >>= go
      where
        go :: Type -> Ti E.Type
        go (UnitT l)          = E.UnitT <$> pure l
        go (BoolT l)          = E.BoolT <$> pure l
        go (IntT ip l)        = E.IntT <$> trans ip <*> pure l
        go (FixT qp l)        = E.FixT <$> trans qp <*> pure l
        go (FloatT fp l)      = E.FloatT <$> trans fp <*> pure l
        go (StringT l)        = pure $ E.StringT l
        go (SynT _ tau _)     = go tau
        go (StructT s taus l) = E.StructT <$> trans s <*> mapM trans taus <*> pure l
        go (RefT tau l)       = E.RefT <$> go tau <*> pure l
        go (ArrT i tau l)     = E.ArrT <$> trans i <*> go tau <*> pure l

        go (ST omega tau1 tau2 tau3 l) =
            E.ST <$> trans omega <*> go tau1 <*> go tau2 <*> go tau3 <*> pure l

        go (FunT taus tau l) =
            E.FunT <$> mapM go taus <*> go tau <*> pure l

        go (NatT i l) =
            pure $ E.NatT i l

        go (ForallT tvks tau l) =
            E.ForallT <$> mapM trans tvks <*> trans tau <*> pure l

        go (TyVarT alpha l) =
            E.TyVarT <$> trans alpha <*> pure l

        go tau =
            faildoc $ text "Cannot translate" <+> enquote (ppr tau) <+>
                      text "to Core type"

instance Trans Type E.Omega where
    trans (C omega _) = E.C <$> trans omega
    trans (T _)       = pure E.T
    trans tau         = faildoc $ text "Cannot translate" <+>
                                  enquote (ppr tau) <+> text "to Core omega"

instance Trans Kind E.Kind where
    trans tau = compress tau >>= go
      where
        go :: Kind -> Ti E.Kind
        go (TauK r) = E.TauK <$> trans r
        go OmegaK   = pure E.OmegaK
        go MuK      = pure E.MuK
        go RhoK     = pure E.RhoK
        go PhiK     = pure E.PhiK
        go NatK     = pure E.NatK

        go kappa =
            faildoc $ text "Cannot translate" <+> enquote (ppr kappa) <+>
                      text "to Core kind"

instance Trans R E.Traits where
    trans r = compress r >>= go
      where
        go :: R -> Ti E.Traits
        go (R ts)  = pure ts
        go MetaR{} = faildoc $ text "Cannot translate traits meta-variable to Core."

instance Trans (TyVar, Kind) (E.TyVar, E.Kind) where
    trans (alpha, kappa) = (,) <$> trans alpha <*> trans kappa

instance Trans (Z.Var, Type) (E.Var, E.Type) where
    trans (v, tau) = (,) <$> trans v <*> trans tau

instance Trans Z.UnrollAnn E.UnrollAnn where
    trans ann = pure $ (toEnum . fromEnum) ann

instance Trans Z.InlineAnn E.InlineAnn where
    trans ann = pure $ (toEnum . fromEnum) ann

instance Trans Z.PipelineAnn E.PipelineAnn where
    trans ann = pure $ (toEnum . fromEnum) ann

instance Trans Z.VectAnn E.VectAnn where
    trans Z.AutoVect      = pure E.AutoVect
    trans (Z.Rigid f i j) = pure $ E.Rigid f i j
    trans (Z.UpTo f i j)  = pure $ E.UpTo f i j
