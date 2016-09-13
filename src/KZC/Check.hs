{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Check
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Check (
    withTi,

    Expected,
    readExpected,

    checkProgram,

    tcExp,
    checkExp,
    inferExp,

    refPath
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding ((<|>))
#endif /* !MIN_VERSION_base(4,8,0) */
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
import KZC.Platform
import KZC.Util.Error
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

checkProgram :: [Z.Decl] -> Ti [E.Decl]
checkProgram cls = checkDecls cls sequence

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

checkLet :: Z.Var -> Maybe Z.Type -> Kind -> Z.Exp -> SrcLoc
         -> Ti (Type, Ti E.Decl)
checkLet v ztau TauK e l =
    withExpContext e $ do
    tau <- fromZ (ztau, TauK)
    extendVars [(v, tau)] $ do
      mce <- castVal tau e
      let mcdecl = do checkUnresolvedMtvs v tau
                      cv   <- trans v
                      ctau <- trans tau
                      ce   <- mce
                      return $ E.LetD cv ctau ce l
      return (tau, mcdecl)

checkLet f ztau MuK e l =
    withExpContext e $ do
    tau <- fromZ (ztau, MuK)
    mce <- extendVars [(f, tau)] $
           collectCheckValCtx tau $
           checkExp e tau
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    let mcdecl = co $ do cf   <- trans f
                         ctau <- trans tau_gen
                         ce   <- mce
                         return $ E.LetD cf ctau ce l
    return (tau_gen, mcdecl)

checkLet _ _ kappa _ _ =
    panicdoc $
    text "checkLet: expected kind tau or mu, but got:" <+> ppr kappa

checkLetRef :: Z.Var -> Z.Type -> Maybe Z.Exp -> SrcLoc
            -> Ti (Type, Ti E.Decl)
checkLetRef v ztau e_init l =
    withMaybeExpContext e_init $ do
    tau <- fromZ ztau
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

checkLetFun :: Z.Var -> Maybe Z.Type -> [Z.VarBind] -> Z.Exp -> SrcLoc
            -> Ti (Type, Ti E.Decl)
checkLetFun f ztau ps e l = do
    tau   <- fromZ (ztau, PhiK)
    ptaus <- fromZ ps
    (tau_ret, mce) <-
        extendVars ((f,tau) : ptaus) $ do
        tau_ret           <- newMetaTvT MuK l
        mce               <- collectCheckValCtx tau_ret $
                             checkExp e tau_ret
        (tau_ret_gen, _)  <- generalize tau_ret
        unifyTypes (funT (map snd ptaus) tau_ret_gen) tau
        return (tau_ret_gen, mce)
    (tau_gen, co) <- generalize tau
    traceVar f tau_gen
    let mkLetFun = co $ do cf       <- trans f
                           cptaus   <- mapM trans ptaus
                           ctau_ret <- trans tau_ret
                           ce       <- withSummaryContext e mce
                           return $ E.LetFunD cf [] cptaus ctau_ret ce l
    return (tau_gen, mkLetFun)

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
    let tau       =  funT (map snd ptaus) tau_ret
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
        s <- newMetaTvT TauK l
        a <- newMetaTvT TauK l
        b <- newMetaTvT TauK l
        fst <$> generalize (ST [] (C (UnitT l) l) s a b l)

    checkRetType ztau | not isPure = do
        s   <- newMetaTvT TauK l
        a   <- newMetaTvT TauK l
        b   <- newMetaTvT TauK l
        tau <- fromZ ztau
        fst <$> generalize (ST [] (C tau l) s a b l)

    checkRetType ztau =
        fromZ ztau

checkDecl :: Z.Decl
          -> (Ti E.Decl -> Ti a)
          -> Ti a
checkDecl decl@(Z.LetD v ztau e l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLet v ztau TauK e l
    extendVars [(v, tau)] $ k (alwaysWithSummaryContext decl mcdecl)

checkDecl decl@(Z.LetRefD v ztau e_init l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLetRef v ztau e_init l
    extendVars [(v, refT tau)] $ k mcdecl

checkDecl decl@(Z.LetFunD f ztau ps e l) k = do
    (tau, mkLetFun) <- alwaysWithSummaryContext decl $
                       checkLetFun f ztau ps e l
    let mcdecl = alwaysWithSummaryContext decl mkLetFun
    extendVars [(f,tau)] $ k mcdecl

checkDecl decl@(Z.LetFunExternalD f ps ztau_ret isPure l) k = do
    (tau, mkLetExtFun) <- alwaysWithSummaryContext decl $
                          checkLetExtFun f ps ztau_ret isPure l
    let mcdecl = alwaysWithSummaryContext decl mkLetExtFun
    extendVars [(f,tau)] $ k mcdecl

checkDecl decl@(Z.LetStructD (Z.StructDef zs zflds l) _) k = do
    (taus, mkLetStruct) <-
        alwaysWithSummaryContext decl $ do
        checkStructNotRedefined zs
        checkDuplicates "field names" zfnames
        taus <- mapM fromZ ztaus
        mapM_ (`checkKind` TauK) taus
        let mkLetStruct = do cs      <- trans zs
                             cfnames <- mapM trans zfnames
                             ctaus   <- mapM trans taus
                             return $ E.LetStructD cs (cfnames `zip` ctaus) l
        return (taus, mkLetStruct)
    let mcdecl = alwaysWithSummaryContext decl mkLetStruct
    extendStructs [StructDef zs (zfnames `zip` taus) l] $ k mcdecl
  where
    (zfnames, ztaus) = unzip zflds

    checkStructNotRedefined :: Z.Struct -> Ti ()
    checkStructNotRedefined s = do
      maybe_sdef <- maybeLookupStruct zs
      case maybe_sdef of
        Nothing   -> return ()
        Just sdef -> faildoc $ text "Struct" <+> ppr s <+> text "redefined" <+>
                     parens (text "original definition at" <+> ppr (locOf sdef))

checkDecl decl@(Z.LetCompD v ztau _ e l) k = do
    (tau, mcdecl) <- alwaysWithSummaryContext decl $
                     checkLet v ztau MuK e l
    extendVars [(v, tau)] $ k (alwaysWithSummaryContext decl mcdecl)

checkDecl decl@(Z.LetFunCompD f ztau _ ps e l) k = do
    (tau, mkLetFun) <- alwaysWithSummaryContext decl $
                       checkLetFun f ztau ps e l
    let mcdecl = alwaysWithSummaryContext decl mkLetFun
    extendVars [(f,tau)] $ k mcdecl

checkDecls :: [Z.Decl]
           -> ([Ti E.Decl] -> Ti a)
           -> Ti a
checkDecls [] k =
    k []

checkDecls (decl:decls) k =
    checkDecl  decl  $ \mcdecl  ->
    checkDecls decls $ \mcdecls ->
    k (mcdecl:mcdecls)

mkSigned :: Type -> Type
mkSigned (FixT (U w) l) = FixT (I w) l
mkSigned tau            = tau

mkUnsigned :: Type -> Type
mkUnsigned (FixT (I w) l) = FixT (U w) l
mkUnsigned tau            = tau

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

    tcConst (Z.FixC zip x) = do
        ip  <- fromZ zip
        cip <- trans ip
        instType (FixT ip l) exp_ty
        return $ E.FixC cip x

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
    unop Z.Lnot = do
        (tau, mce) <- inferVal e
        checkBoolT tau
        instType tau exp_ty
        return $ E.UnopE E.Lnot <$> mce <*> pure l

    unop Z.Bnot = do
        (tau, mce) <- inferVal e
        (tau', co) <- mkBitCast e tau
        checkBitT tau'
        instType tau' exp_ty
        return $ E.UnopE E.Bnot <$> co mce <*> pure l

    unop Z.Neg = do
        (tau, mce) <- inferVal e
        checkNumT tau
        instType (mkSigned tau) exp_ty
        return $ E.UnopE E.Neg <$> mce <*> pure l

    unop (Z.Cast ztau2) = do
        (tau1, mce) <- inferVal e
        tau2        <- fromZ ztau2
        checkLegalCast tau1 tau2
        instType tau2 exp_ty
        return $ E.UnopE <$> (E.Cast <$> trans tau2) <*> mce <*> pure l

    unop Z.Len = do
        (tau, mce) <- inferExp e
        _          <- checkArrT tau
        instType intT exp_ty
        return $ E.UnopE E.Len <$> mce <*> pure l

tcExp e@(Z.BinopE op e1 e2 l) exp_ty =
    withExpContext e $
    binop op
  where
    binop :: Z.Binop -> Ti (Ti E.Exp)
    binop Z.Lt   = checkOrdBinop E.Lt
    binop Z.Le   = checkOrdBinop E.Le
    binop Z.Eq   = checkEqBinop E.Eq
    binop Z.Ge   = checkOrdBinop E.Ge
    binop Z.Gt   = checkOrdBinop E.Gt
    binop Z.Ne   = checkEqBinop E.Ne
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
        checkEqT tau
        instType boolT exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkOrdBinop :: E.Binop -> Ti (Ti E.Exp)
    checkOrdBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkOrdT tau
        instType boolT exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBoolBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBoolBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkBoolT tau
        instType tau exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkNumBinop :: E.Binop -> Ti (Ti E.Exp)
    checkNumBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        checkNumT tau
        instType tau exp_ty
        return $ E.BinopE cop <$> mce1 <*> mce2 <*> pure l

    checkBitBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBitBinop cop = do
        (tau, mce1, mce2) <- unifyValTypes e1 e2
        (tau', co)        <- mkBitCast e1 tau
        checkBitT tau'
        instType tau' exp_ty
        return $ E.BinopE cop <$> co mce1 <*> co mce2 <*> pure l

    checkBitShiftBinop :: E.Binop -> Ti (Ti E.Exp)
    checkBitShiftBinop cop = do
        (tau1, mce1) <- inferVal e1
        (tau1', co)  <- mkBitCast e1 tau1
        checkBitT tau1'
        (tau2, mce2) <- inferVal e2
        checkIntT tau2
        instType tau1' exp_ty
        return $ E.BinopE cop <$> co mce1 <*> mce2 <*> pure l

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
    (tau, mcdecl) <- checkLet v ztau TauK e1 l
    withExpContext e2 $
      extendVars [(v, tau)] $
      checkLetBody e2 exp_ty mcdecl l

tcExp (Z.LetRefE v ztau e1 e2 l) exp_ty = do
    (tau, mcdecl) <- checkLetRef v ztau e1 l
    withExpContext e2 $
      extendVars [(v, refT tau)] $
      checkLetBody e2 exp_ty mcdecl l

tcExp (Z.LetDeclE decl e l) exp_ty =
    checkDecl decl $ \mcdecl -> do
    tau <- newMetaTvT MuK l
    instType tau exp_ty
    mce <- collectCheckValCtx tau $ checkExp e tau
    return $ E.LetE <$> mcdecl <*> mce <*> pure l

tcExp e@(Z.CallE f es l) exp_ty =
    withCallContext f e $ do
    (taus, tau_ret, co1) <- lookupVar f >>= checkFunT f nargs
    when (length taus /= nargs) $
        faildoc $
          text "Expected" <+> ppr (length taus) <+>
          text "arguments but got" <+> ppr nargs
    (tau_ret', co2) <- instantiate tau_ret
    instType tau_ret' exp_ty
    mces <- zipWithM checkArg es taus
    unless (isPureishT tau_ret) $
        checkNoAliasing (es `zip` taus)
    return $ co2 $ co1 $ do
        cf  <- trans f
        ces <- sequence mces
        return $ E.CallE cf [] ces l
  where
    nargs :: Int
    nargs = length es

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
    checkIntT tau1
    tau  <- mkSTC (UnitT l)
    mce2 <- collectCheckValCtx tau $
            checkExp e2 tau
    instType tau exp_ty
    return $ do cann <- trans ann
                cx   <- gensymAt "x" l
                ce1  <- mce1
                ce2  <- mce2
                return $ E.ForE cann cx E.intT (E.intE 1) ce1 ce2 l

tcExp (Z.ForE ann i ztau_i e1 e2 e3 l) exp_ty = do
    tau_i <- fromZ (ztau_i, TauK)
    checkIntT tau_i
    mce1 <- castVal tau_i e1
    mce2 <- castVal tau_i e2
    tau  <- mkSTC (UnitT l)
    mce3 <- extendVars [(i, tau_i)] $
            collectCheckValCtx tau $
            checkExp e3 tau
    instType tau exp_ty
    return $ do cann   <- trans ann
                ci     <- trans i
                ctau_i <- trans tau_i
                ce1    <- mce1
                ce2    <- mce2
                ce3    <- mce3
                return $ E.ForE cann ci ctau_i ce1 ce2 ce3 l

tcExp (Z.ArrayE es l) exp_ty = do
    tau  <- newMetaTvT TauK l
    instType (ArrT (ConstI (length es) l) tau l) exp_ty
    mces <- mapM (`checkExp` tau) es
    return $ do ces <- sequence mces
                return $ E.ArrayE ces l

tcExp (Z.IdxE e1 e2 len l) exp_ty = do
    (tau, mce1) <- withSummaryContext e1 $
                   inferExp e1
    mce2        <- withSummaryContext e2 $ do
                   (tau2, mce2) <- inferVal e2
                   checkIntT tau2
                   co <- mkCast tau2 intT
                   return $ co mce2
    checkIdxE tau mce1 mce2
  where
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
                return $ E.StructE cs (cfs `zip` ces) l
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
            sdef  <- checkStructT tau >>= lookupStruct
            tau_f <- checkStructFieldT sdef f
            instType (RefT tau_f l) exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ E.ProjE ce cf l

        go tau = do
            sdef  <- checkStructT tau >>= lookupStruct
            tau_f <- checkStructFieldT sdef f
            instType tau_f exp_ty
            return $ do ce <- mce
                        cf <- trans f
                        return $ E.ProjE ce cf l

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
        checkKind tau TauK
        return mce

tcExp (Z.ErrorE s l) exp_ty = do
    nu  <- newMetaTvT TauK l
    tau <- mkSTC nu
    instType tau exp_ty
    return $ do
        cnu <- trans nu
        return $ E.ErrorE cnu s l

tcExp (Z.ReturnE ann e l) exp_ty = do
    tau     <- newMetaTvT TauK l
    tau_ret <- mkSTC tau
    instType tau_ret exp_ty
    (tau', mce) <- inferVal e
    unifyTypes tau' tau
    return $ do
        cann <- trans ann
        ce   <- mce
        return $ E.ReturnE cann ce l

tcExp (Z.TakeE l) exp_ty = do
    a <- newMetaTvT TauK l
    b <- newMetaTvT TauK l
    instType (stT (C a l) a a b) exp_ty
    return $ do ca <- trans a
                return $ E.takeE ca

tcExp (Z.TakesE i l) exp_ty = do
    a <- newMetaTvT TauK l
    b <- newMetaTvT TauK l
    instType (stT (C (ArrT (ConstI i l) a l) l) a a b) exp_ty
    return $ do ca <- trans a
                return $ E.takesE (fromIntegral i) ca

tcExp (Z.EmitE e l) exp_ty = do
    s       <- newMetaTvT TauK l
    a       <- newMetaTvT TauK l
    b       <- newMetaTvT TauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    mce <- checkVal e b
    return $ E.EmitE <$> mce <*> pure l

tcExp (Z.EmitsE e l) exp_ty = do
    iota    <- newMetaTvT IotaK l
    s       <- newMetaTvT TauK l
    a       <- newMetaTvT TauK l
    b       <- newMetaTvT TauK l
    let tau =  stT (C (UnitT l) l) s a b
    instType tau exp_ty
    mce <- checkVal e (arrT iota b)
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
    tau  <- fromZ (zalpha, TauK)
    tau' <- fromZ (zbeta, TauK)
    unifyTypes tau' tau
    instType (stT (T l) tau tau tau) exp_ty
    return $ do ctau <- trans tau
                cx   <- gensymAt "x" l
                return $ E.repeatE $
                         E.bindE cx ctau (E.takeE ctau) $
                         E.emitE (E.varE cx)

tcExp (Z.ParE _ (Z.ReadE ztau l) e _) tau_exp = do
    omega   <- newMetaTvT OmegaK l
    a       <- fromZ (ztau, TauK)
    b       <- newMetaTvT TauK l
    let tau =  ST [] omega a a b l
    instType tau tau_exp
    checkExp e tau

tcExp (Z.ParE _ e (Z.WriteE ztau l) _) tau_exp = do
    omega    <- newMetaTvT OmegaK l
    s        <- newMetaTvT TauK l
    a        <- newMetaTvT TauK l
    b        <- newMetaTvT TauK l
    b'       <- fromZ (ztau, TauK)
    let tau  =  ST [] omega s a b l
    let tau' =  ST [] omega s a b' l
    instType tau' tau_exp
    ce <- checkExp e tau
    co <- mkCastT b b'
    return $ co ce

tcExp e@(Z.ParE ann e1 e2 l) tau_exp = do
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
                withSummaryContext e $
                mkCastT b b'
    omega  <- joinOmega omega1 omega2
    instType (ST [] omega a a c l) tau_exp
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

    go (Z.IdxE e (Z.ConstE (Z.FixC _ i) _) Nothing _) path =
        go e (IdxP i 1 : path)

    go (Z.IdxE e (Z.ConstE (Z.FixC _ i) _) (Just len) _) path =
        go e (IdxP i len : path)

    go (Z.IdxE e _ _ _) _ =
        go e []

    go (Z.ProjE e f _) path =
        go e (ProjP f : path)

    go e _ =
        faildoc $ text "refPath: Not a reference:" <+> ppr e

tcStms :: [Z.Stm] -> Expected Type -> Ti (Ti E.Exp)
tcStms [stm@Z.LetS{}] _ =
    withSummaryContext stm $
    faildoc $ text "Last command in command sequence must be an expression"

tcStms (Z.LetS decl l : stms) exp_ty = do
    tau <- mkSTOmega
    instType tau exp_ty
    collectCheckValCtx tau $
      checkDecl decl $ \mcdecl -> do
      mce <- checkStms stms tau
      return $ do
          cdecl <- mcdecl
          ce    <- mce
          return $ E.LetE cdecl ce l

tcStms [stm@Z.BindS{}] _ =
    withSummaryContext stm $
    faildoc $ text "Last command in command sequence must be an expression"

tcStms (stm@(Z.BindS v ztau e l) : stms) exp_ty = do
    nu                     <- fromZ (ztau, TauK)
    tau1@(ST [] _ s a b _) <- mkSTC nu
    omega2                 <- newMetaTvT OmegaK l
    let tau2               =  ST [] omega2 s a b l
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
    nu                     <- newMetaTvT TauK l
    tau1@(ST [] _ s a b _) <- mkSTC nu
    omega2                 <- newMetaTvT OmegaK l
    let tau2               =  ST [] omega2 s a b l
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

    go (ST [] (C tau _) s a b l) mce = do
        mu    <- askValCtxType
        omega <- newMetaTvT OmegaK l
        unifyTypes (ST [] omega s a b l) mu
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

kcType :: Type -> Expected Kind -> Ti ()
kcType tau@UnitT{}    kappa_exp = instKind tau TauK kappa_exp
kcType tau@BoolT{}    kappa_exp = instKind tau TauK kappa_exp
kcType tau@FixT{}     kappa_exp = instKind tau TauK kappa_exp
kcType tau@FloatT{}   kappa_exp = instKind tau TauK kappa_exp
kcType tau@StringT{}  kappa_exp = instKind tau TauK kappa_exp
kcType tau@StructT{}  kappa_exp = instKind tau TauK kappa_exp
kcType tau@ArrT{}     kappa_exp = instKind tau TauK kappa_exp

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

kcType tau0@ConstI{} kappa_exp =
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

generalize :: Type -> Ti (Type, CoDecl)
generalize tau0 =
    compress tau0 >>= go
  where
    go :: Type -> Ti (Type, CoDecl)
    go tau@(ST [] omega sigma tau1 tau2 l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let alphaMtvs =  filter (isKind TauK) mtvs
        alphas        <- freshVars (length alphaMtvs) ((Set.toList . fvs) tau)
        extendTyVars (alphas `zip` repeat TauK) $
            zipWithM_ kcWriteTv alphaMtvs [TyVarT alpha noLoc | alpha <- alphas]
        tau <- compress $ ST alphas omega sigma tau1 tau2 l
        let co = extendTyVars (alphas `zip` repeat TauK)
        return (tau, co)

    go tau@ST{} =
        panicdoc $ text "Asked to generalize quantified type:" <+> ppr tau

    go tau@(FunT [] taus tau_ret l) = do
        mtvs          <- (<\\>) <$> metaTvs tau <*> askEnvMtvs
        let iotaMtvs  =  filter (isKind IotaK) mtvs
        iotas         <- freshVars (length iotaMtvs) ((Set.toList . fvs) tau)
        extendIVars (iotas `zip` repeat IotaK) $
            zipWithM_ kcWriteTv iotaMtvs [VarI iota noLoc | iota <- iotas]
        tau <- compress $ FunT iotas taus tau_ret l
        let co mcdecl = extendIVars (iotas `zip` repeat IotaK) $ do
                        ciotas <- mapM trans iotas
                        mcdecl >>= checkLetFunE ciotas
        return (tau, co)
      where
        checkLetFunE :: [E.IVar] -> E.Decl -> Ti E.Decl
        checkLetFunE ciotas (E.LetFunD cf [] cvtaus ctau ce l) =
            return $ E.LetFunD cf ciotas cvtaus ctau ce l

        checkLetFunE ciotas (E.LetExtFunD cf [] cvtaus ctau l) =
            return $ E.LetExtFunD cf ciotas cvtaus ctau l

        checkLetFunE _ ce =
            panicdoc $
            text "generalize: expected to coerce a letfun, but got:" <+> ppr ce

    go tau@FunT{} =
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
                return $ E.CallE cf ciotas ces l
        return (tau, co)
      where
        checkFunE :: E.Exp -> Ti (E.Var, [E.Exp], SrcLoc)
        checkFunE (E.CallE cf [] ces l) =
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
    go FixT{}                 = return ()
    go FloatT{}               = return ()
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
    go BoolT{} = return ()
    go FixT{}  = return ()
    go tau     = unifyTypes tau intT `catch`
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
    go (FixT U{} _) = return ()
    go tau          = unifyTypes tau intT `catch`
                        \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected a bit type, e.g., bit or uint, but got:" <+> ppr tau'

-- | Check that a type is an integral type
checkIntT :: Type -> Ti ()
checkIntT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go FixT{} = return ()
    go tau    = unifyTypes tau intT

-- | Check that a type is a numerical type.
checkNumT :: Type -> Ti ()
checkNumT tau =
    compress tau >>= go
  where
    go :: Type -> Ti ()
    go FixT{}                 = return ()
    go FloatT{}               = return ()
    go (StructT s _)
        | Z.isComplexStruct s = return ()
    go tau                    = unifyTypes tau intT `catch`
                                    \(_ :: UnificationException) -> err

    err :: Ti a
    err = do
        [tau'] <- sanitizeTypes [tau]
        faildoc $ text "Expected integral type, but got:" <+> ppr tau'

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
          FunT [] [c] tau_ret@ST{} _ -> return (c, tau_ret)
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
    let co mce = co2 $ co1 $ do cf <- trans f
                                ce <- mce
                                return $ E.callE cf [ce]
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

-- | Check for unresolved type meta-variables in a binder's type.
checkUnresolvedMtvs :: Z.Var -> Type -> Ti ()
checkUnresolvedMtvs v tau = do
    tau' <- compress tau
    let mtvs :: [MetaTv]
        mtvs = Set.toList $ fvs tau'
    check "Ambiguous array length" (filter isIotaMetaTv mtvs)
    check "Ambiguous type" (filter (not . isIotaMetaTv) mtvs)
  where
      isIotaMetaTv :: MetaTv -> Bool
      isIotaMetaTv (MetaTv _ IotaK _) = True
      isIotaMetaTv _                  = False

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
castVal :: Type -> Z.Exp -> Ti (Ti E.Exp)
castVal tau2 e0 = do
    (tau1, mce) <- inferVal e
    co <- case (e, tau1, tau2) of
            (Z.ArrayE es _, ArrT iota1 etau1 _, ArrT iota2 etau2 _) -> do
                unifyTypes iota1 iota2
                mapM_ (\e -> checkSafeCast WarnUnsafeAutoCast (Just e) etau1 etau2) es
                mkArrayCast etau1 etau2
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

    go _ tau2 mce = do
        ctau <- trans tau2
        ce   <- mce
        return $ E.UnopE (E.Cast ctau) ce (srclocOf ce)

mkCheckedSafeCast :: Z.Exp -> Type -> Type -> Ti Co
mkCheckedSafeCast e tau1 tau2 = do
    co <- mkCast tau1 tau2
    checkSafeCast WarnUnsafeAutoCast (Just e) tau1 tau2
    return co

mkBitCast :: Z.Exp -> Type -> Ti (Type, Co)
mkBitCast e tau = do
    co <- mkCheckedSafeCast e tau tau'
    return (tau', co)
  where
    tau' :: Type
    tau' = mkUnsigned tau

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

    go FixT{} FixT{} =
        return ()

    go FixT{} FloatT{} =
        return ()

    go FloatT{} FixT{} =
        return ()

    go FloatT{} FloatT{} =
        return ()

    go (StructT s1 _) (StructT s2 _) | Z.isComplexStruct s1 && Z.isComplexStruct s2 =
        return ()

    go tau1 tau2 =
        unifyTypes tau1 tau2
      `catch` \(_ :: UnificationException) -> do
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        faildoc $ text "Cannot cast" <+> ppr tau1' <+> text "to" <+> ppr tau2'

-- | Check whether casting the given expression from @tau1@ to @tau2@ is
-- safe. If it is definitely unsafe, signal an error; if it may be unsafe,
-- signal a warning if the specified warning flag is set.
checkSafeCast :: WarnFlag -> Maybe Z.Exp -> Type -> Type -> Ti ()
checkSafeCast _f (Just e@(Z.ConstE (Z.FixC ip x) l)) tau1 tau2 =
    withSummaryContext e $ do
    tau1' <- fromZ $ Z.FixT ip l
    when (tau1' /= tau1) $
        withSummaryContext e $
        faildoc $ align $
        text "Expected type:" <+> ppr tau1' </>
        text "     Got type:" <+> ppr tau1
    go tau2
  where
    go :: Type -> Ti ()
    go (FixT U{} _) | x < 0 =
        faildoc $ align $
        text "Integer constant" <+> ppr x <+>
        text "cannot be represented as type" <+> ppr tau2

    go (FixT (U w) _) | x > 2^w-1 =
        faildoc $ align $
        text "Integer constant" <+> ppr x <+>
        text "cannot be represented as type" <+> ppr tau2

    go (FixT (I w) _) | x > 2^(w-1)-1 =
        faildoc $ align $
        text "Integer constant" <+> ppr x <+>
        text "cannot be represented as type" <+> ppr tau2

    go (FixT (I w) _) | x < -2^(w-1) =
        faildoc $ align $
        text "Integer constant" <+> ppr x <+>
        text "cannot be represented as type" <+> ppr tau2

    go _ =
        return ()

checkSafeCast f e tau1@(FixT ip1 _) tau2@(FixT ip2 _) | ipWidth ip2 < ipWidth ip1 =
    maybeWithSummaryContext e $
    warndocWhen f $ align $
    text "Potentially unsafe auto cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2

checkSafeCast f e tau1@(FixT ip1 _) tau2@(FixT ip2 _) | ipIsSigned ip2 /= ipIsSigned ip1 =
    maybeWithSummaryContext e $
    warndocWhen f $ align $
    text "Potentially unsafe auto cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2

checkSafeCast _f _e _tau1 _tau2 =
    return ()

-- | Perform constant folding. This does a very limited amount of
-- "optimization," mainly so that we can give decent errors during implicit
-- casts regarding integral constants being too large.
constFold :: Z.Exp -> Z.Exp
constFold (Z.ArrayE es l) =
    Z.ArrayE (map constFold es) l

constFold (Z.UnopE Z.Neg (Z.ConstE (Z.FixC ip r) l) _) =
    Z.ConstE (Z.FixC (Z.I (Z.ipWidth ip)) (negate r)) l

constFold (Z.BinopE op e1 e2 l) =
    constFoldBinopE op (constFold e1) (constFold e2)
  where
    constFoldBinopE :: Z.Binop -> Z.Exp -> Z.Exp -> Z.Exp
    constFoldBinopE op (Z.ConstE (Z.FixC ip x) _) (Z.ConstE (Z.FixC ip' y) _)
        | ip' == ip, Just z <- constFoldBinop op x y =
           Z.ConstE (Z.FixC ip z) l

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
        faildoc $ text "Cannot join" <+> ppr tau1 <+> text "and" <+> ppr tau2

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
      text "Expected type:" <+> ppr tau2' </>
      text "but got:      " <+> ppr tau1' <>
      msg

data UnificationException = UnificationException Type Type Doc
  deriving (Typeable)

instance Show UnificationException where
    show (UnificationException tau1 tau2 msg) =
        pretty 80 $
        text "Expected type:" <+> ppr tau2 </>
        text "but got:      " <+> ppr tau1 <>
        msg

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

    go _ _ UnitT{} UnitT{} = return ()
    go _ _ BoolT{} BoolT{} = return ()

    go _ _ (FixT ip _)    (FixT ip' _)   | ip' == ip = return ()
    go _ _ (FloatT fp _)  (FloatT fp' _) | fp' == fp = return ()
    go _ _ StringT{}      StringT{}                  = return ()
    go _ _ (StructT s1 _) (StructT s2 _) | s1 == s2  = return ()

    go theta phi (ArrT tau1a tau2a _) (ArrT tau1b tau2b _) = do
        unify theta phi tau1a tau1b
        unify theta phi tau2a tau2b

    go theta phi (C tau1 _) (C tau2 _) =
        unify theta phi tau1 tau2

    go _ _ T{} T{} =
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
                                             , tv1 == tv2' =
        return ()

    go _ _ _ _ = do
        msg <- relevantBindings
        [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
        throw $ UnificationException tau1' tau2' msg

    updateMetaTv :: MetaTv -> Type -> Type -> Ti ()
    updateMetaTv mtv tau1 tau2 = do
        mtvs2 <- metaTvs [tau2]
        when (mtv `elem` mtvs2) $ do
            [tau1', tau2'] <- sanitizeTypes [tau1, tau2]
            faildoc $ nest 2 $
              text "Cannot construct the infinite type:" <+/>
              ppr tau1' <+> text "=" <+> ppr tau2'
        kcWriteTv mtv tau2

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
    go tau1@MetaT{} _ mce1 tau2 _ mce2 = do
        unifyTypes tau1 tau2
        return (tau2, mce1, mce2)

    go tau1 _ mce1 tau2@MetaT{} _ mce2 = do
        unifyTypes tau2 tau1
        return (tau1, mce1, mce2)

    go tau1 _ mce1 tau2 _ mce2 | tau1 == tau2 =
        return (tau1, mce1, mce2)

    -- Always cast integer constants /down/. This lets us, for example, treat
    -- @1@ as an @int8@.
    go tau1@FixT{} e@Z.ConstE{} mce1 tau2@FixT{} _ mce2 = do
        co <- mkCheckedSafeCast e tau1 tau2
        return (tau2, co mce1, mce2)

    go tau1@FixT{} _ mce1 tau2@FixT{} e@Z.ConstE{} mce2 = do
        co <- mkCheckedSafeCast e tau2 tau1
        return (tau1, mce1, co mce2)

    go tau1 e1 mce1 tau2 e2 mce2 = do
        tau <- lubType tau1 tau2
        co1 <- mkCheckedSafeCast e1 tau1 tau
        co2 <- mkCheckedSafeCast e2 tau2 tau
        return (tau, co1 mce1, co2 mce2)

    lubType :: Type -> Type -> Ti Type
    lubType (FixT ip l) (FixT ip' _) =
        return $ FixT (lubIP ip ip') l

    lubType (FloatT fp l) (FloatT fp' _) =
        return $ FloatT (max fp fp') l

    lubType (FixT _ l) (FloatT w _) =
        return $ FloatT w l

    lubType (FloatT w _) (FixT _ l) =
        return $ FloatT w l

    lubType (StructT s1 l) (StructT s2 _) | Z.isComplexStruct s1 && Z.isComplexStruct s2 = do
        s <- lubComplex s1 s2
        return $ StructT s l

    lubType tau1@FixT{} tau2 = do
        unifyTypes tau2 tau1
        return tau1

    lubType tau1@FloatT{} tau2 = do
        unifyTypes tau2 tau1
        return tau1

    lubType tau1 tau2 = do
        unifyTypes tau1 tau2
        return tau1

    lubIP :: IP -> IP -> IP
    lubIP (I w) (I w') = I (max w w')
    lubIP (I w) (U w') = I (max w w')
    lubIP (U w) (I w') = I (max w w')
    lubIP (U w) (U w') = U (max w w')

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

class FromZ a b where
    fromZ :: a -> Ti b

instance FromZ Z.IP IP where
    fromZ (Z.I Nothing)  = pure $ I dEFAULT_INT_WIDTH
    fromZ (Z.I (Just w)) = pure $ I w
    fromZ (Z.U Nothing)  = pure $ U dEFAULT_INT_WIDTH
    fromZ (Z.U (Just w)) = pure $ U w

instance FromZ Z.FP FP where
    fromZ Z.FP16 = pure FP16
    fromZ Z.FP32 = pure FP32
    fromZ Z.FP64 = pure FP64

instance FromZ Z.Type Type where
    fromZ (Z.UnitT l)      = pure $ UnitT l
    fromZ (Z.BoolT l)      = pure $ BoolT l
    fromZ (Z.FixT ip l)    = FixT <$> fromZ ip <*> pure l
    fromZ (Z.FloatT fp l)  = FloatT <$> fromZ fp <*> pure l
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

instance Trans Z.Var E.Var where
    trans (Z.Var n) = pure $ E.Var n

instance Trans Z.Field E.Field where
    trans (Z.Field n) = pure $ E.Field n

instance Trans Z.Struct E.Struct where
    trans (Z.Struct n) = pure $ E.Struct n

instance Trans TyVar E.TyVar where
    trans (TyVar n) = pure $ E.TyVar n

instance Trans IVar E.IVar where
    trans (IVar n) = pure $ E.IVar n

instance Trans IP E.IP where
    trans = pure

instance Trans FP E.FP where
    trans = pure

instance Trans Type E.Type where
    trans tau = compress tau >>= go
      where
        go :: Type -> Ti E.Type
        go (UnitT l)     = E.UnitT <$> pure l
        go (BoolT l)     = E.BoolT <$> pure l
        go (FixT ip l)   = E.FixT <$> trans ip <*> pure l
        go (FloatT fp l) = E.FloatT <$> trans fp <*> pure l
        go (StringT l)   = pure $ E.StringT l
        go (StructT s l) = E.StructT <$> trans s <*> pure l
        go (RefT tau l)  = E.RefT <$> go tau <*> pure l
        go (ArrT i tau l)= E.ArrT <$> trans i <*> go tau <*> pure l

        go (ST alphas omega tau1 tau2 tau3 l) =
            extendTyVars (alphas `zip` repeat TauK) $
            E.ST <$> mapM trans alphas <*>  trans omega <*>
             go tau1 <*> go tau2 <*> go tau3 <*> pure l

        go (FunT iotas taus tau l) =
            E.FunT <$> mapM trans iotas <*> mapM go taus <*> go tau <*> pure l

        go (TyVarT alpha l) =
            E.TyVarT <$> trans alpha <*> pure l

        go tau =
            faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core type"

instance Trans Type E.Omega where
    trans (C omega _) = E.C <$> trans omega
    trans (T _)       = pure E.T
    trans tau         = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core omega"

instance Trans Type E.Iota where
    trans (ConstI i l)      = pure $ E.ConstI i l
    trans (VarI (IVar n) l) = pure $ E.VarI (E.IVar n) l
    trans tau               = faildoc $ text "Cannot translate" <+> ppr tau <+> text "to Core iota"

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
