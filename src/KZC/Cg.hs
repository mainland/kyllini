{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg (
    evalCg,

    compileProgram
  ) where

import Prelude

import Control.Applicative ((<$>))
import Control.Monad (forM_,
                      liftM,
                      void,
                      when)
import Control.Monad.Free (Free(..))
import Data.Bits
import Data.Char (ord)
import Data.Foldable (toList)
import Data.String (IsString(..))
import Data.Loc
import Data.Monoid (mempty)
import qualified Language.C.Syntax as C
import Numeric (showHex)
import Text.PrettyPrint.Mainland

import KZC.Cg.Monad
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Lint
import KZC.Lint.Monad
import KZC.Name
import KZC.Platform
import KZC.Quote.C
import KZC.Staged
import KZC.Summary

compileProgram :: [Decl] -> Cg ()
compileProgram decls = do
    appendTopDef [cedecl|$esc:("#include <kz.h>")|]
    (cinit_items, citems) <-
        inNewBlock $ do
        cgDecls decls $ do
        tau@(ST _ _ _ a b _) <- lookupVar "main"
        comp <- cgExp (varE "main") >>= unCComp
        inNewBlock_ $ do
        cgInitInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgInitOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
        -- Keep track of the current continuation. This is only used when
        -- we do not have first class labels.
        lbl  <- ccompLabel comp
        cres <- cgTemp "main_res" (resultType tau)
        appendDecl [cdecl|typename KONT $id:cUR_KONT = LABELADDR($id:lbl);|]
        -- Generate code for the computation
        cgThread $ cgCComp take emit (done (resultType tau) cres) comp
        cgCleanupInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgCleanupOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
    cgLabels
    appendTopDef [cedecl|
void kz_main(const typename kz_params_t* $id:params)
{
    typename kz_buf_t $id:in_buf;
    typename kz_buf_t $id:out_buf;

    $items:(filter isBlockDecl cinit_items)
    $items:(filter isBlockDecl citems)
    $items:(filter isBlockStm cinit_items)
    $items:(filter isBlockStm citems)
}|]
  where
    in_buf, out_buf, params :: C.Id
    in_buf  = "in"
    out_buf = "out"
    params = "params"

    isBlockDecl :: C.BlockItem -> Bool
    isBlockDecl (C.BlockDecl {}) = True
    isBlockDecl _                = False

    isBlockStm :: C.BlockItem -> Bool
    isBlockStm (C.BlockStm {}) = True
    isBlockStm _               = False

    take :: TakeK
    take l n tau k1 k2 = do
        -- Generate a pointer to the current element in the buffer.
        ctau <- cgType tau
        cbuf <- cgCTemp tau "take_bufp" [cty|const $ty:ctau*|] (Just [cinit|NULL|])
        cgWithLabel l $ do
        cinput <- cgInput tau (CExp [cexp|$id:in_buf|]) (fromIntegral n)
        appendStm [cstm|$cbuf = (const $ty:ctau*) $cinput;|]
        appendStm [cstm|if($cbuf == NULL) { BREAK; }|]
        k2 $ k1 $ case (tau, n) of
                    (BitT {}, 1) -> CExp [cexp|*$cbuf & 1|]
                    (_, 1)       -> CExp [cexp|*$cbuf|]
                    _            -> CExp [cexp|$cbuf|]

    emit :: EmitK
    emit l tau@(ArrT {}) ce ccomp k =
        cgWithLabel l $ do
        ceAddr <- cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceAddr
        k ccomp

    emit l tau ce ccomp k =
        cgWithLabel l $ do
        ceAddr <- cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceAddr
        k ccomp

    done :: Type -> CExp -> DoneK
    done tau cv ce =
        cgAssign tau cv ce

    cUR_KONT :: C.Id
    cUR_KONT = "curk"

    cgInitInput :: Type -> CExp -> CExp -> Cg ()
    cgInitInput tau cp cbuf = go tau
      where
        go :: Type -> Cg ()
        go (ArrT _ tau _)          = go tau
        go (BitT {})               = appendStm [cstm|kz_init_input_bit($cp, &$cbuf);|]
        go (IntT W8  Signed _)     = appendStm [cstm|kz_init_input_int8($cp, &$cbuf);|]
        go (IntT W16 Signed _)     = appendStm [cstm|kz_init_input_int16($cp, &$cbuf);|]
        go (IntT W32 Signed _)     = appendStm [cstm|kz_init_input_int32($cp, &$cbuf);|]
        go (IntT W8  Unsigned _)   = appendStm [cstm|kz_init_input_uint8($cp, &$cbuf);|]
        go (IntT W16 Unsigned _)   = appendStm [cstm|kz_init_input_uint16($cp, &$cbuf);|]
        go (IntT W32 Unsigned _)   = appendStm [cstm|kz_init_input_uint32($cp, &$cbuf);|]
        go (FloatT W8  _)          = appendStm [cstm|kz_init_input_float($cp, &$cbuf);|]
        go (FloatT W16 _)          = appendStm [cstm|kz_init_input_float($cp, &$cbuf);|]
        go (FloatT W32 _)          = appendStm [cstm|kz_init_input_float($cp, &$cbuf);|]
        go (FloatT W64 _)          = appendStm [cstm|kz_init_input_double($cp, &$cbuf);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_init_input_complex16($cp, &$cbuf);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_init_input_complex32($cp, &$cbuf);|]
        go _                       = appendStm [cstm|kz_init_input_bytes($cp, &$cbuf);|]

    cgInitOutput :: Type -> CExp -> CExp -> Cg ()
    cgInitOutput tau cp cbuf = go tau
      where
        go :: Type -> Cg ()
        go (ArrT _ tau _)          = go tau
        go (BitT {})               = appendStm [cstm|kz_init_output_bit($cp, &$cbuf);|]
        go (IntT W8  Signed _)     = appendStm [cstm|kz_init_output_int8($cp, &$cbuf);|]
        go (IntT W16 Signed _)     = appendStm [cstm|kz_init_output_int16($cp, &$cbuf);|]
        go (IntT W32 Signed _)     = appendStm [cstm|kz_init_output_int32($cp, &$cbuf);|]
        go (IntT W8  Unsigned _)   = appendStm [cstm|kz_init_output_uint8($cp, &$cbuf);|]
        go (IntT W16 Unsigned _)   = appendStm [cstm|kz_init_output_uint16($cp, &$cbuf);|]
        go (IntT W32 Unsigned _)   = appendStm [cstm|kz_init_output_uint32($cp, &$cbuf);|]
        go (FloatT W8  _)          = appendStm [cstm|kz_init_output_float($cp, &$cbuf);|]
        go (FloatT W16 _)          = appendStm [cstm|kz_init_output_float($cp, &$cbuf);|]
        go (FloatT W32 _)          = appendStm [cstm|kz_init_output_float($cp, &$cbuf);|]
        go (FloatT W64 _)          = appendStm [cstm|kz_init_output_double($cp, &$cbuf);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_init_output_complex16($cp, &$cbuf);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_init_output_complex32($cp, &$cbuf);|]
        go _                       = appendStm [cstm|kz_init_output_bytes($cp, &$cbuf);|]

    cgCleanupInput :: Type -> CExp -> CExp -> Cg ()
    cgCleanupInput tau cp cbuf = go tau
      where
        go :: Type -> Cg ()
        go (ArrT _ tau _)          = go tau
        go (BitT {})               = appendStm [cstm|kz_cleanup_input_bit($cp, &$cbuf);|]
        go (IntT W8  Signed _)     = appendStm [cstm|kz_cleanup_input_int8($cp, &$cbuf);|]
        go (IntT W16 Signed _)     = appendStm [cstm|kz_cleanup_input_int16($cp, &$cbuf);|]
        go (IntT W32 Signed _)     = appendStm [cstm|kz_cleanup_input_int32($cp, &$cbuf);|]
        go (IntT W8  Unsigned _)   = appendStm [cstm|kz_cleanup_input_uint8($cp, &$cbuf);|]
        go (IntT W16 Unsigned _)   = appendStm [cstm|kz_cleanup_input_uint16($cp, &$cbuf);|]
        go (IntT W32 Unsigned _)   = appendStm [cstm|kz_cleanup_input_uint32($cp, &$cbuf);|]
        go (FloatT W8  _)          = appendStm [cstm|kz_cleanup_input_float($cp, &$cbuf);|]
        go (FloatT W16 _)          = appendStm [cstm|kz_cleanup_input_float($cp, &$cbuf);|]
        go (FloatT W32 _)          = appendStm [cstm|kz_cleanup_input_float($cp, &$cbuf);|]
        go (FloatT W64 _)          = appendStm [cstm|kz_cleanup_input_double($cp, &$cbuf);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_cleanup_input_complex16($cp, &$cbuf);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_cleanup_input_complex32($cp, &$cbuf);|]
        go _                       = appendStm [cstm|kz_cleanup_input_bytes($cp, &$cbuf);|]

    cgCleanupOutput :: Type -> CExp -> CExp -> Cg ()
    cgCleanupOutput tau cp cbuf = go tau
      where
        go :: Type -> Cg ()
        go (ArrT _ tau _)          = go tau
        go (BitT {})               = appendStm [cstm|kz_cleanup_output_bit($cp, &$cbuf);|]
        go (IntT W8  Signed _)     = appendStm [cstm|kz_cleanup_output_int8($cp, &$cbuf);|]
        go (IntT W16 Signed _)     = appendStm [cstm|kz_cleanup_output_int16($cp, &$cbuf);|]
        go (IntT W32 Signed _)     = appendStm [cstm|kz_cleanup_output_int32($cp, &$cbuf);|]
        go (IntT W8  Unsigned _)   = appendStm [cstm|kz_cleanup_output_uint8($cp, &$cbuf);|]
        go (IntT W16 Unsigned _)   = appendStm [cstm|kz_cleanup_output_uint16($cp, &$cbuf);|]
        go (IntT W32 Unsigned _)   = appendStm [cstm|kz_cleanup_output_uint32($cp, &$cbuf);|]
        go (FloatT W8  _)          = appendStm [cstm|kz_cleanup_output_float($cp, &$cbuf);|]
        go (FloatT W16 _)          = appendStm [cstm|kz_cleanup_output_float($cp, &$cbuf);|]
        go (FloatT W32 _)          = appendStm [cstm|kz_cleanup_output_float($cp, &$cbuf);|]
        go (FloatT W64 _)          = appendStm [cstm|kz_cleanup_output_double($cp, &$cbuf);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_cleanup_output_complex16($cp, &$cbuf);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_cleanup_output_complex32($cp, &$cbuf);|]
        go _                       = appendStm [cstm|kz_cleanup_output_bytes($cp, &$cbuf);|]

    cgInput :: Type -> CExp -> CExp -> Cg CExp
    cgInput tau cbuf cn = go tau
      where
        go :: Type -> Cg CExp
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgInput tau cbuf (cn*ci)
        go (BitT {})               = return $ CExp [cexp|kz_input_bit(&$cbuf, $cn)|]
        go (IntT W8  Signed _)     = return $ CExp [cexp|kz_input_int8(&$cbuf, $cn)|]
        go (IntT W16 Signed _)     = return $ CExp [cexp|kz_input_int16(&$cbuf, $cn)|]
        go (IntT W32 Signed _)     = return $ CExp [cexp|kz_input_int32(&$cbuf, $cn)|]
        go (IntT W8  Unsigned _)   = return $ CExp [cexp|kz_input_uint8(&$cbuf, $cn)|]
        go (IntT W16 Unsigned _)   = return $ CExp [cexp|kz_input_uint16(&$cbuf, $cn)|]
        go (IntT W32 Unsigned _)   = return $ CExp [cexp|kz_input_uint32(&$cbuf, $cn)|]
        go (FloatT W8  _)          = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT W16 _)          = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT W32 _)          = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT W64 _)          = return $ CExp [cexp|kz_input_double(&$cbuf, $cn)|]
        go (StructT "complex16" _) = return $ CExp [cexp|kz_input_complex16(&$cbuf, $cn)|]
        go (StructT "complex32" _) = return $ CExp [cexp|kz_input_complex32(&$cbuf, $cn)|]
        go tau                     = do ctau <- cgType tau
                                        return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

    cgOutput :: Type -> CExp -> CExp -> CExp -> Cg ()
    cgOutput tau cbuf cn cval = go tau
      where
        go :: Type -> Cg ()
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgOutput tau cbuf (cn*ci) cval
        go (BitT {})               = appendStm [cstm|kz_output_bit(&$cbuf, $cval, $cn);|]
        go (IntT W8  Signed _)     = appendStm [cstm|kz_output_int8(&$cbuf, $cval, $cn);|]
        go (IntT W16 Signed _)     = appendStm [cstm|kz_output_int16(&$cbuf, $cval, $cn);|]
        go (IntT W32 Signed _)     = appendStm [cstm|kz_output_int32(&$cbuf, $cval, $cn);|]
        go (IntT W8  Unsigned _)   = appendStm [cstm|kz_output_uint8(&$cbuf, $cval, $cn);|]
        go (IntT W16 Unsigned _)   = appendStm [cstm|kz_output_uint16(&$cbuf, $cval, $cn);|]
        go (IntT W32 Unsigned _)   = appendStm [cstm|kz_output_uint32(&$cbuf, $cval, $cn);|]
        go (FloatT W8  _)          = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT W16 _)          = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT W32 _)          = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT W64 _)          = appendStm [cstm|kz_output_double(&$cbuf, $cval, $cn);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_output_complex16(&$cbuf, $cval, $cn);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_output_complex32(&$cbuf, $cval, $cn);|]
        go tau                     = do ctau <- cgType tau
                                        appendStm [cstm|kz_output_bytes(&$cbuf, $cval, $cn*sizeof($ty:ctau));|]

cgLabels :: Cg ()
cgLabels = do
    l:ls    <- getLabels
    let cl  =  [cenum|$id:l = 0|]
        cls =  [ [cenum|$id:l|] | l <- ls]
    appendTopDef [cedecl|$esc:("#if !defined(FIRSTCLASSLABELS)")|]
    appendTopDef [cedecl|enum { $enums:(cl:cls) };|]
    appendTopDef [cedecl|$esc:("#endif /* !defined(FIRSTCLASSLABELS) */")|]

cgThread :: Cg a -> Cg a
cgThread k = do
    (x, code) <- collect k
    tell code { codeDecls = mempty, codeStms = mempty }
    let cds   =  (toList . codeDecls) code
    let css   =  (toList . codeStms) code
    appendDecls cds
    appendStms [cstms|BEGIN_DISPATCH; $stms:css END_DISPATCH;|]
    return x

cgDecls :: [Decl] -> Cg a -> Cg a
cgDecls [] k =
    k

cgDecls (decl:decls) k =
    cgDecl decl $ cgDecls decls k

-- | Compile an expression that is going to be bound. The expression could be
-- bound either to a variable via a let binding or to an argument via a function
-- call. A computation must be delayed until its use, when we will know how to
-- hook it up so it can take and emit.
cgBoundExp :: Type -> Exp -> Cg CExp
cgBoundExp tau e =
    if isCompT tau
    then return ce_delayed
    else inSTScope tau $ cgExp e
  where
    ce_delayed :: CExp
    ce_delayed = CDelay [] [] $
        liftM CComp $
        collectComp $
        withSummaryContext e $
        inSTScope tau $
        inLocalScope $
        cgExp e >>= unCComp

cgDecl :: forall a . Decl -> Cg a -> Cg a
cgDecl decl@(LetD v tau e _) k = do
    cv <- withSummaryContext decl $ do
          ce <- cgBoundExp tau e
          cgLet v ce tau
    extendVars [(v, tau)] $ do
    extendVarCExps [(v, cv)] $ do
    k
  where
    -- | @'cgLet' v ce tau@ generates code to assign the compiled expression @ce@,
    -- of type @tau@, to the core variable @v@. If @ce@ is a computation or a
    -- delayed compiled expression, then we don't need to generate code. Otherwise
    -- we create a declaration to hold the value.
    cgLet :: Var -> CExp -> Type -> Cg CExp
    cgLet _ ce@(CComp {}) _ =
        return ce

    cgLet _ ce@(CDelay {}) _ =
        return ce

    cgLet v ce tau = do
        isTopLevel <- isInTopScope
        cve        <- cgBinder isTopLevel v tau
        cgAssign tau cve ce
        return cve

cgDecl decl@(LetFunD f iotas vbs tau_ret e l) k = do
    if isPureishT tau_ret
      then cgPureishLetFun
      else cgImpureLetFun
  where
    -- A function that doesn't take or emit can be compiled directly to a C
    -- function. The body of the function may be a @CComp@ since it could still
    -- use references, so we must compile it using 'cgPureishCComp'.
    cgPureishLetFun :: Cg a
    cgPureishLetFun = do
        cf <- cvar f
        extendVars [(f, tau)] $ do
        extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
        appendTopComment (ppr f <+> colon <+> align (ppr tau))
        withSummaryContext decl $ do
            inSTScope tau_ret $ do
            extendIVars (iotas `zip` repeat IotaK) $ do
            extendVars vbs $ do
            (ciotas, cparams1) <- unzip <$> mapM cgIVar iotas
            (cvbs,   cparams2) <- unzip <$> mapM cgVarBind vbs
            cres_ident         <- gensym "let_res"
            citems <- inNewBlock_ $
                      extendIVarCExps (iotas `zip` ciotas) $
                      extendVarCExps  (map fst vbs `zip` cvbs) $
                      inLocalScope $ do
                      cres <- if isReturnedByRef tau_res
                              then return $ CExp [cexp|$id:cres_ident|]
                              else cgTemp "let_res" tau_res
                      cgExp e >>= unCComp >>= cgPureishCComp tau_res cres
                      when (not (isUnitT tau_res) && not (isReturnedByRef tau_res)) $
                          appendStm $ rl l [cstm|return $cres;|]
            if isReturnedByRef tau_res
             then do cretparam <- cgRetParam tau_res (Just cres_ident)
                     appendTopDef $ rl l [cedecl|void $id:cf($params:(cparams1 ++ cparams2 ++ [cretparam])) { $items:citems }|]
             else do ctau_res <- cgType tau_res
                     appendTopDef $ rl l [cedecl|$ty:ctau_res $id:cf($params:(cparams1 ++ cparams2)) { $items:citems }|]
        k
      where
        tau_res :: Type
        ST _ (C tau_res) _ _ _ _ = tau_ret

    -- We can't yet generate code for a function that uses take and/or emit
    -- because we don't know where it will be taking or emitting when it is
    -- called. Therefore we wrap the body of the function in a 'CDelay'
    -- constructor which causes compilation to be delayed until the function is
    -- actually called. This effectively inlines the function at every call
    -- site, but we can't do much better because 1) we don't have a good way to
    -- abstract over queues, and, more importantly, 2) we compile computations
    -- to a state machine, so we need all code to be in the same block so we can
    -- freely jump between states.
    cgImpureLetFun :: Cg a
    cgImpureLetFun =
        extendVars [(f, tau)] $ do
        extendVarCExps [(f, ce_delayed)] $ do
        k
      where
        ce_delayed :: CExp
        ce_delayed = CDelay iotas vbs $
            liftM CComp $
            withSummaryContext decl $
            inSTScope tau_ret $
            collectComp $
            cgExp e >>= unCComp

    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

cgDecl decl@(LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $
    extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
    appendTopComment (ppr f <+> colon <+> align (ppr tau))
    withSummaryContext decl $ do
        (_, cparams1) <- unzip <$> mapM cgIVar iotas
        (_, cparams2) <- unzip <$> mapM cgVarBind vbs
        if isReturnedByRef tau_res
          then do cretparam <- cgRetParam tau_res Nothing
                  appendTopDef $ rl l [cedecl|void $id:cf($params:(cparams1 ++ cparams2 ++ [cretparam]));|]
          else do ctau_ret <- cgType tau_res
                  appendTopDef $ rl l [cedecl|$ty:ctau_ret $id:cf($params:(cparams1 ++ cparams2));|]
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

    tau_res :: Type
    tau_res = resultType tau_ret

    cf :: C.Id
    cf = C.Id ("__kz_" ++ namedString f) l

cgDecl decl@(LetRefD v tau maybe_e _) k = do
    cve <- withSummaryContext decl $ do
           isTopLevel <- isInTopScope
           cgBinder isTopLevel v tau
    withSummaryContext decl $
        case maybe_e of
          Nothing -> cgDefaultValue tau cve
          Just e  -> do ce <- inLocalScope $ cgExp e
                        cgAssign tau cve ce
    extendVars [(v, refT tau)] $ do
    extendVarCExps [(v, cve)] $ do
    k

cgDecl decl@(LetStructD s flds l) k = do
    withSummaryContext decl $ do
        cflds <- mapM cgField flds
        appendTopDecl $ rl l [cdecl|typedef struct $id:(cstruct s l) { $sdecls:cflds } $id:(cstruct s l);|]
    extendStructs [StructDef s flds l] k
  where
    cgField :: (Field, Type) -> Cg C.FieldGroup
    cgField (fld, tau) = do
        let cfld =  zencode (namedString fld)
        ctau     <- cgType tau
        return [csdecl|$ty:ctau $id:cfld;|]

cgConstArray :: Type -> [CExp] -> Cg CExp
cgConstArray (BitT {}) ces = do
    cv <- gensym "__const_arr"
    appendTopDecl [cdecl|const $ty:bIT_ARRAY_ELEM_TYPE $id:cv[$int:(bitArrayLen (length ces))] = { $inits:cinits };|]
    return $ CExp [cexp|$id:cv|]
  where
    cinits :: [C.Initializer]
    cinits = finalizeBits $ foldl mkBits (0,0,[]) ces

    mkBits :: (CExp, Int, [C.Initializer]) -> CExp -> (CExp, Int, [C.Initializer])
    mkBits (cconst, i, cinits) ce
        | i == bIT_ARRAY_ELEM_BITS - 1 = (0,         0, const cconst' : cinits)
        | otherwise                    = (cconst', i+1, cinits)
      where
        cconst' :: CExp
        cconst' = cconst .|. (fromBits ce `shiftL` i)

        fromBits :: CExp -> CExp
        fromBits (CBit True)  = CInt 1
        fromBits (CBit False) = CInt 0
        fromBits ce           = ce

    finalizeBits :: (CExp, Int, [C.Initializer]) -> [C.Initializer]
    finalizeBits (_,      0, cinits) = reverse cinits
    finalizeBits (cconst, _, cinits) = reverse $ const cconst : cinits

    const :: CExp -> C.Initializer
    const (CInt i) = [cinit|$(chexconst i)|]
    const ce       = [cinit|$ce|]

cgConstArray tau ces = do
    cv   <- gensym "__const_arr"
    ctau <- cgType tau
    appendTopDecl [cdecl|const $ty:ctau $id:cv[$int:(length ces)] = { $inits:cinits };|]
    return $ CExp [cexp|$id:cv|]
  where
    cinits :: [C.Initializer]
    cinits =  [[cinit|$ce|] | ce <- ces]

cgDefaultValue :: Type -> CExp -> Cg ()
cgDefaultValue tau cv = go tau
  where
    go :: Type -> Cg ()
    go (BoolT {})  = cgAssign tau cv (CExp [cexp|0|])
    go (BitT {})   = cgAssign tau cv (CExp [cexp|0|])
    go (IntT {})   = cgAssign tau cv (CExp [cexp|0|])
    go (FloatT {}) = cgAssign tau cv (CExp [cexp|0.0|])

    go (ArrT iota (BitT {}) _) = do
        cn <- cgIota iota
        appendStm [cstm|memset($cv, 0, $(bitArrayLen cn)*sizeof($ty:ctau));|]
      where
        ctau :: C.Type
        ctau = bIT_ARRAY_ELEM_TYPE

    go (ArrT iota tau _) = do
        cn    <- cgIota iota
        ctau  <- cgType tau
        appendStm [cstm|memset($cv, 0, $cn*sizeof($ty:ctau));|]

    go tau = do
        ctau  <- cgType tau
        caddr <- cgAddrOf tau cv
        appendStm [cstm|memset($caddr, 0, sizeof($ty:ctau));|]

cgExp :: Exp -> Cg CExp
cgExp e@(ConstE c _) =
    cgConst c
  where
    cgConst :: Const -> Cg CExp
    cgConst UnitC        = return CVoid
    cgConst (BoolC b)    = return $ CBool b
    cgConst (BitC b)     = return $ CBit b
    cgConst (IntC _ _ i) = return $ CInt i
    cgConst (FloatC _ r) = return $ CFloat r
    cgConst (StringC s)  = return $ CExp [cexp|$string:s|]

    cgConst (ArrayC cs) = do
        ArrT _ tau _ <- inferExp e
        ces          <- mapM cgConst cs
        cgConstArray tau ces

cgExp (VarE v _) =
    lookupVarCExp v

cgExp (UnopE op e l) = do
    tau <- inferExp e
    ce  <- cgExp e
    cgUnop tau ce op
  where
    cgUnop :: Type -> CExp -> Unop -> Cg CExp
    cgUnop tau_from ce (Cast tau_to) =
        cgCast ce tau_from tau_to

    cgUnop (ArrT iota _ _) _ Len =
        cgIota iota

    cgUnop _ _ Len =
        panicdoc $
        text "cgUnop: tried to take the length of a non-array type!"

    cgUnop tau ce op | isComplexT tau =
        go op
      where
        go :: Unop -> Cg CExp
        go Neg = do
            let a,b :: CExp
                (a, b) = unComplex ce
            cv <- cgTemp "binop_complex" tau
            appendStm $ rl l [cstm|$cv.re = $(-a);|]
            appendStm $ rl l [cstm|$cv.im = $(-b);|]
            return cv

        go op =
            panicdoc $ text "Illegal operation on complex values:" <+> ppr op

    cgUnop _         ce Lnot = return $ CExp [cexp|!$ce|]
    cgUnop (BitT {}) ce Bnot = return $ CExp [cexp|!$ce|]
    cgUnop _         ce Bnot = return $ CExp [cexp|~$ce|]
    cgUnop _         ce Neg  = return $ CExp [cexp|-$ce|]

    cgCast :: CExp -> Type -> Type -> Cg CExp
    cgCast ce tau_from tau_to | isComplexT tau_from && isComplexT tau_to = do
        ctemp <- cgTemp "cast_complex" tau_to
        appendStm $ rl l [cstm|$ctemp.re = $ce.re;|]
        appendStm $ rl l [cstm|$ctemp.im = $ce.im;|]
        return ctemp

    cgCast ce _ tau_to | isComplexT tau_to = do
        ctemp <- cgTemp "cast_complex" tau_to
        appendStm $ rl l [cstm|$ctemp.re = $ce;|]
        appendStm $ rl l [cstm|$ctemp.im = $ce;|]
        return ctemp

    cgCast ce _ tau_to = do
        ctau_to <- cgType tau_to
        return $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

cgExp (BinopE op e1 e2 l) = do
    tau <- inferExp e1
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    cgBinop tau ce1 ce2 op
  where
    cgBinop :: Type -> CExp -> CExp -> Binop -> Cg CExp
    cgBinop tau ce1 ce2 op | isComplexT tau =
        go op
      where
        go :: Binop -> Cg CExp
        go Eq =
            return $ CExp $ rl l [cexp|$ce1.re == $ce2.re && $ce1.im == $ce2.im|]

        go Ne =
            return $ CExp $ rl l [cexp|$ce1.re != $ce2.re || $ce1.im != $ce2.im|]

        go Add = do
            let a,b,c,d :: CExp
                (a, b) = unComplex ce1
                (c, d) = unComplex ce2
            cv <- cgTemp "binop_complex" tau
            appendStm $ rl l [cstm|$cv.re = $(a+c);|]
            appendStm $ rl l [cstm|$cv.im = $(b+d);|]
            return cv

        go Sub = do
            let a,b,c,d :: CExp
                (a, b) = unComplex ce1
                (c, d) = unComplex ce2
            cv <- cgTemp "binop_complex" tau
            appendStm [cstm|$cv.re = $(a-c);|]
            appendStm [cstm|$cv.im = $(b-d);|]
            return cv

        go Mul = do
            let a,b,c,d :: CExp
                (a, b) = unComplex ce1
                (c, d) = unComplex ce2
            cv <- cgTemp "binop_complex" tau
            appendStm $ rl l [cstm|$cv.re = $(a*c - b*d);|]
            appendStm $ rl l [cstm|$cv.im = $(b*c + a*d);|]
            return cv

        go Div = do
            let a,b,c,d :: CExp
                (a, b) = unComplex ce1
                (c, d) = unComplex ce2
            cv <- cgTemp "binop_complex" tau
            appendStm $ rl l [cstm|$cv.re = $((a*c + b*d)/(c*c + d*d));|]
            appendStm $ rl l [cstm|$cv.im = $((b*c - a*d)/(c*c + d*d));|]
            return cv

        go op =
            panicdoc $ text "Illegal operation on complex values:" <+> ppr op

    cgBinop _ ce1 ce2 Lt   = return $ CExp $ rl l [cexp|$ce1 <  $ce2|]
    cgBinop _ ce1 ce2 Le   = return $ CExp $ rl l [cexp|$ce1 <= $ce2|]
    cgBinop _ ce1 ce2 Eq   = return $ CExp $ rl l [cexp|$ce1 == $ce2|]
    cgBinop _ ce1 ce2 Ge   = return $ CExp $ rl l [cexp|$ce1 >= $ce2|]
    cgBinop _ ce1 ce2 Gt   = return $ CExp $ rl l [cexp|$ce1 >  $ce2|]
    cgBinop _ ce1 ce2 Ne   = return $ CExp $ rl l [cexp|$ce1 != $ce2|]
    cgBinop _ ce1 ce2 Land = return $ CExp $ rl l [cexp|$ce1 && $ce2|]
    cgBinop _ ce1 ce2 Lor  = return $ CExp $ rl l [cexp|$ce1 || $ce2|]
    cgBinop _ ce1 ce2 Band = return $ CExp $ rl l [cexp|$ce1 &  $ce2|]
    cgBinop _ ce1 ce2 Bor  = return $ CExp $ rl l [cexp|$ce1 |  $ce2|]
    cgBinop _ ce1 ce2 Bxor = return $ CExp $ rl l [cexp|$ce1 ^  $ce2|]
    cgBinop _ ce1 ce2 LshL = return $ CExp $ rl l [cexp|$ce1 << $ce2|]
    cgBinop _ ce1 ce2 LshR = return $ CExp $ rl l [cexp|$ce1 >> $ce2|]
    cgBinop _ ce1 ce2 AshR = return $ CExp $ rl l [cexp|((unsigned int) $ce1) >> $ce2|]
    cgBinop _ ce1 ce2 Add  = return $ CExp $ rl l [cexp|$ce1 + $ce2|]
    cgBinop _ ce1 ce2 Sub  = return $ CExp $ rl l [cexp|$ce1 - $ce2|]
    cgBinop _ ce1 ce2 Mul  = return $ CExp $ rl l [cexp|$ce1 * $ce2|]
    cgBinop _ ce1 ce2 Div  = return $ CExp $ rl l [cexp|$ce1 / $ce2|]
    cgBinop _ ce1 ce2 Rem  = return $ CExp $ rl l [cexp|$ce1 % $ce2|]
    cgBinop _ ce1 ce2 Pow  = return $ CExp $ rl l [cexp|pow($ce1, $ce2)|]

cgExp e@(IfE e1 e2 e3 _) = do
    inferExp e >>= go
  where
    go :: Type -> Cg CExp
    go tau | isPureishT tau = do
        cres <- cgTemp "if_res" tau_res
        cgIf (cgCond "if_cond" e1)
             (cgExp e2 >>= cgAssign tau_res cres)
             (cgExp e3 >>= cgAssign tau_res cres)
        return cres
      where
        tau_res :: Type
        tau_res = resultType tau

    go tau = do
        ccond     <- cgCond "if_cond" e1
        comp2     <- collectComp $ cgExp e2 >>= unCComp
        comp3     <- collectComp $ cgExp e3 >>= unCComp
        theta     <- askTyVarTypeSubst
        cres      <- cgTemp "if_res" (theta tau_res)
        ifl       <- genLabel "ifk"
        bindthl   <- genLabel "then_bindk"
        endthl    <- genLabel "then_endk"
        bindell   <- genLabel "else_bindk"
        endell    <- genLabel "else_endk"
        return $ CComp $
            ifC ifl cres ccond
                (comp2 >>= bindC bindthl (theta tau_res) cres >> endC endthl)
                (comp3 >>= bindC bindell (theta tau_res) cres >> endC endell)
      where
        tau_res :: Type
        tau_res = resultType tau

cgExp (LetE decl e _) =
    cgDecl decl $ cgExp e

cgExp e0@(CallE f iotas es l) = do
    FunT _ _ tau_ret _ <- lookupVar f
    if isPureishT tau_ret
      then cgPureCall (resultType tau_ret)
      else cgImpureCall (resultType tau_ret)
  where
    cgPureCall :: Type -> Cg CExp
    cgPureCall tau_res = do
        cf     <- lookupVarCExp f
        FunT ivs _ _ _ <- lookupVar f
        ciotas <- mapM cgIota iotas
        extendIVarCExps (ivs `zip` ciotas) $ do
        ces    <- mapM cgArg es
        if isReturnedByRef tau_res
          then do cres <- cgTemp "call_res" tau_res
                  appendStm $ rl l [cstm|$cf($args:ciotas, $args:(ces ++ [cres]));|]
                  return cres
          else do cres <- cgTemp "call_res" tau_res
                  cgAssign tau_res cres $ CExp [cexp|$cf($args:ciotas, $args:ces)|]
                  return cres
      where
        cgArg :: Exp -> Cg CExp
        cgArg e = do
            tau <- inferExp e
            go tau
          where
            go :: Type -> Cg CExp
            go tau@(ArrT {}) =
                cgExp e >>= cgAddrOf tau

            go tau | isPassByRef tau =
                cgExp e >>= cgAddrOf tau

            go _ =
                cgExp e

    cgImpureCall :: Type -> Cg CExp
    cgImpureCall _ = do
        (ivs, vbs, m) <- lookupVarCExp f >>= unCDelay
        ciotas        <- mapM cgIota iotas
        ces           <- mapM cgArg es
        extendIVars (ivs `zip` repeat IotaK) $ do
        extendVars  vbs $ do
        extendIVarCExps (ivs `zip` ciotas) $ do
        extendVarCExps  (map fst vbs `zip` ces) $ do
        instantiateSTScope $ do
        m
      where
        cgArg :: Exp -> Cg CExp
        cgArg e = do
            tau <- inferExp e
            cgBoundExp tau e

    instantiateSTScope :: Cg a -> Cg a
    instantiateSTScope m = do
        FunT _ _ (ST _ _ s a b _) _ <- lookupVar f
        ST _ _ s' a' b' _           <- inferExp e0
        extendTyVarTypes [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']] m

cgExp (DerefE e _) = do
    ce <- cgExp e
    return $ unPtr ce

cgExp (AssignE e1 e2 _) = do
    tau <- inferExp e1
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    cgAssign tau ce1 ce2
    return CVoid

cgExp e0@(WhileE e_test e_body l) = do
    inferExp e0 >>= go
  where
    go :: Type -> Cg CExp
    -- This case will only be invoked when the surrounding computation is
    -- pureish since @tau@ is always instantiated with the surrounding
    -- function's ST index variables.
    go tau | isPureishT tau = do
        ce_test <- cgCond "while_cond" e_test
        ce_body <- cgExp e_body
        appendStm $ rl l [cstm|while ($ce_test) { $ce_body; }|]
        return CVoid

    go _ = do
        (ce_test, testc) <- collectCodeAsComp $
                            cgCond "while_test" e_test
        bodyc            <- collectComp $
                            cgExp e_body >>= unCComp
        testl            <- ccompLabel testc
        condl            <- genLabel "while_cond"
        endl             <- genLabel "while_end"
        return $ CComp $
            testc >>
            ifC condl CVoid ce_test
                (bodyc >> gotoC testl)
                (endC endl)

cgExp e0@(ForE _ v v_tau e_start e_len e_body l) =
    inferExp e0 >>= go
  where
    go :: Type -> Cg CExp
    go tau | isPureishT tau = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendDecl $ rl l [cdecl|$ty:cv_tau $id:cv;|]
        ce_start <- cgExp e_start
        ce_len   <- cgExp e_len
        citems   <- inNewBlock_ $ cgExp e_body
        appendStm $ rl l [cstm|for ($id:cv = $ce_start; $id:cv < $(ce_start + ce_len); $id:cv++) { $items:citems }|]
        return CVoid

    go _ = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendDecl $ rl l [cdecl|$ty:cv_tau $id:cv;|]
        ce_start <- cgExp e_start
        ce_len   <- cgExp e_len
        initc    <- collectCodeAsComp_ $ do
                    appendStm [cstm|$id:cv = $ce_start;|]
        updatec  <- collectCodeAsComp_ $
                    appendStm $ rl l [cstm|$id:cv++;|]
        bodyc    <- collectComp $ cgExp e_body >>= unCComp
        forl     <- genLabel "fork"
        endl     <- genLabel "for_end"
        void $ useLabel forl
        return $ CComp $
            initc >>
            ifC forl CVoid (CExp [cexp|$id:cv < $(ce_start + ce_len)|])
                (bodyc >> updatec >> gotoC forl)
                (endC endl)

cgExp e@(ArrayE es _) | all isConstE es = do
    ArrT _ tau _ <- inferExp e
    ces          <- mapM cgExp es
    cgConstArray tau ces

cgExp e@(ArrayE es l) = do
    ArrT _ tau _ <- inferExp e
    cv           <- gensym "__arr"
    ctau         <- cgType tau
    appendDecl $ rl l [cdecl|$ty:ctau $id:cv[$int:(length es)];|]
    forM_ (es `zip` [(0::Integer)..]) $ \(e,i) -> do
        ce <- cgExp e
        appendStm $ rl l [cstm|$id:cv[$int:i] = $ce;|]
    return $ CExp [cexp|$id:cv|]

cgExp (IdxE e1 e2 maybe_len _) = do
    (_, tau) <- inferExp e1 >>= checkArrOrRefArrT
    ce1      <- cgExp e1
    ce2      <- cgExp e2
    case maybe_len of
      Nothing  -> cgIdx tau ce1 ce2
      Just len -> cgSlice tau ce1 ce2 len

cgExp (StructE s flds l) = do
    cv <- cgTemp "struct" (StructT s l)
    mapM_ (cgField cv) flds
    return cv
  where
    cgField :: CExp -> (Field, Exp) -> Cg ()
    cgField cv (fld, e) = do
        let cfld =  zencode (namedString fld)
        ce       <- cgExp e
        appendStm $ rl l [cstm|$cv.$id:cfld = $ce;|]

cgExp (ProjE e fld l) = do
    ce <- cgExp e
    return $ CExp $ rl l [cexp|$ce.$id:cfld|]
  where
    cfld :: C.Id
    cfld = C.Id (zencode (namedString fld)) l

cgExp (PrintE nl es l) = do
    mapM_ cgPrint es
    when nl $
        appendStm $ rl l [cstm|printf("\n");|]
    return CVoid
  where
    cgPrint :: Exp -> Cg ()
    cgPrint e = do
        tau <- inferExp e
        ce  <- cgExp e
        cgPrintScalar tau ce

    cgPrintScalar :: Type -> CExp -> Cg ()
    cgPrintScalar (UnitT {})            _  = appendStm $ rl l [cstm|printf("()");|]
    cgPrintScalar (BoolT {})            ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "true" : "false");|]
    cgPrintScalar (BitT  {})            ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "1" : "0");|]
    cgPrintScalar (IntT W64 Signed _)   ce = appendStm $ rl l [cstm|printf("%lld", (long long) $ce);|]
    cgPrintScalar (IntT W64 Unsigned _) ce = appendStm $ rl l [cstm|printf("%llu", (unsigned long long) $ce);|]
    cgPrintScalar (IntT _ Signed _)     ce = appendStm $ rl l [cstm|printf("%ld", (long) $ce);|]
    cgPrintScalar (IntT _ Unsigned _)   ce = appendStm $ rl l [cstm|printf("%lu", (unsigned long) $ce);|]
    cgPrintScalar (FloatT {})           ce = appendStm $ rl l [cstm|printf("%f",  (double) $ce);|]
    cgPrintScalar (StringT {})          ce = appendStm $ rl l [cstm|printf("%s",  $ce);|]
    cgPrintScalar (ArrT iota tau _)     ce = cgPrintArray iota tau ce

    cgPrintScalar (StructT s _) ce | isComplexStruct s =
        appendStm $ rl l [cstm|printf("(%ld,%ld)", (long) $ce.re, (long) $ce.im);|]

    cgPrintScalar tau _ =
        faildoc $ text "Cannot print type:" <+> ppr tau

    cgPrintArray :: Iota -> Type -> CExp -> Cg ()
    cgPrintArray iota tau@(BitT {}) ce = do
        cn    <- cgIota iota
        caddr <- cgAddrOf (ArrT iota tau noLoc) ce
        appendStm $ rl l [cstm|kz_bitarray_print($caddr, $cn);|]

    cgPrintArray iota tau ce = do
        cn    <- cgIota iota
        caddr <- cgAddrOf (ArrT iota tau noLoc) ce
        cgFor 0 cn $ \ci -> do
            cgPrintScalar tau (CExp [cexp|$caddr[$ci]|])
            if cn .==. ci
              then return ()
              else appendStm $ rl l [cstm|printf(",");|]

cgExp (ErrorE _ s l) = do
    appendStm $ rl l [cstm|kz_error($string:s);|]
    return CVoid

cgExp (ReturnE _ e _) = do
    ce <- cgExp e
    return $ CComp $ return ce

cgExp (BindE bv@(BindV v tau) e1 e2 _) = do
    comp1 <- collectComp (cgExp e1 >>= unCComp)
    cve   <- cgBinder False v tau
    -- We create a CComp containing all the C code needed to define and bind @v@
    -- and then execute @e2@.
    comp2 <- collectCompBind $
             extendBindVars [bv] $
             extendVarCExps [(v, cve)] $ do
             theta <- askTyVarTypeSubst
             bindl <- genLabel "bindk"
             comp2 <- collectComp (cgExp e2 >>= unCComp)
             return $ \ce -> bindC bindl (theta tau) cve ce >> comp2
    return $ CComp $ comp1 >>= comp2

cgExp (BindE WildV e1 e2 _) = do
    comp1 <- collectComp (cgExp e1 >>= unCComp)
    comp2 <- collectComp (cgExp e2 >>= unCComp)
    return $ CComp $ comp1 >> comp2

cgExp (TakeE tau _) = do
    l     <- genLabel "takek"
    theta <- askTyVarTypeSubst
    return $ CComp $ takeC l (theta tau)

cgExp (TakesE i tau _) = do
    l     <- genLabel "takesk"
    theta <- askTyVarTypeSubst
    return $ CComp $ takesC l i (theta tau)

cgExp (EmitE e _) = liftM CComp $ collectComp $ do
    tau   <- inferExp e
    ce    <- cgExp e
    theta <- askTyVarTypeSubst
    emitC (theta tau) ce

cgExp (EmitsE e _) = liftM CComp $ collectComp $ do
    tau   <- inferExp e
    ce    <- cgExp e
    theta <- askTyVarTypeSubst
    emitC (theta tau) ce

cgExp (RepeatE _ e _) = do
    ccomp  <- cgExp e >>= unCComp
    -- Ensure we have a starting label; @ccomp@ could be a @Pure@ action!
    startl <- genLabel "repeatk"
    void $ useLabel startl
    return $ CComp $ labelC startl >> ccomp >> gotoC startl

cgExp e0@(ParE _ b e1 e2 _) = do
    tau_res   <- resultType <$> inferExp e0
    cres      <- cgTemp "par_res" tau_res
    (s, a, c) <- askSTIndTypes
    donell    <- genLabel "done_left"
    donerl    <- genLabel "done_right"
    comp1     <- localSTIndTypes (Just (s, a, b)) $
                 cgExp e1 >>= unCComp
    comp2     <- localSTIndTypes (Just (b, b, c)) $
                 cgExp e2 >>= unCComp
    theta     <- askTyVarTypeSubst
    return $ CComp $
      parC (theta b) (theta tau_res) cres
           (comp1 >>= doneC donell)
           (comp2 >>= doneC donerl)

cgCond :: String -> Exp -> Cg CExp
cgCond s e = do
    ccond <- cgTemp s boolT
    cgExp e >>= unCComp >>= cgPureishCComp boolT ccond
    return ccond

-- | @'isConstE' e@ returns 'True' only if @e@ compiles to a constant C
-- expression.
isConstE :: Exp -> Bool
isConstE (ConstE {})        = True
isConstE (UnopE _ e _)      = isConstE e
isConstE (BinopE _ e1 e2 _) = isConstE e1 && isConstE e2
isConstE _                  = False

collectCodeAsComp :: Cg a -> Cg (a, CComp)
collectCodeAsComp m = do
    l         <- genLabel "codek"
    (x, code) <- collect m
    return (x, codeC l code)

collectCodeAsComp_ :: Cg a -> Cg CComp
collectCodeAsComp_ m =
    snd <$> collectCodeAsComp m

collectComp :: Cg CComp -> Cg CComp
collectComp m = do
    l            <- genLabel "codek"
    (comp, code) <- collect m
    tell code { codeDecls = mempty, codeStms = mempty }
    return $ codeC l code { codeDefs = mempty } >> comp

collectCompBind :: Cg (CExp -> CComp) -> Cg (CExp -> CComp)
collectCompBind m = do
    l             <- genLabel "codek"
    (compf, code) <- collect m
    return $ \ce -> codeC l code >> compf ce

cgIVar :: IVar -> Cg (CExp, C.Param)
cgIVar iv = do
    civ <- cvar iv
    return (CExp [cexp|$id:civ|], [cparam|int $id:civ|])

-- | Compile a function variable binding. When the variable is a ref type, it is
-- represented as a pointer, so we use the 'CPtr' constructor to ensure that
-- dereferencing occurs.
cgVarBind :: (Var, Type) -> Cg (CExp, C.Param)
cgVarBind (v, tau) = do
    cv     <- cvar v
    cparam <- cgParam tau (Just cv)
    if isPassByRef tau
      then return (CPtr (CExp $ rl l [cexp|$id:cv|]), cparam)
      else return (CExp $ rl l [cexp|$id:cv|], cparam)
  where
    l :: Loc
    l = locOf v <--> locOf tau

cgIota :: Iota -> Cg CExp
cgIota (ConstI i _) = return $ CInt (fromIntegral i)
cgIota (VarI iv _)  = lookupIVarCExp iv

-- | Destruct a 'CExp' representing a complex number into its constituent real
-- and imaginary parts.
unComplex :: CExp -> (CExp, CExp)
unComplex ce = (CExp [cexp|$ce.re|], CExp [cexp|$ce.im|])

-- | Dereference a ref type, which may or may not be represented as a pointer.
unPtr :: CExp -> CExp
unPtr (CPtr ce) = CExp [cexp|*$ce|]
unPtr ce        = ce

-- | Check that the argument is either an array or a reference to an array and
-- return the array's size and the type of its elements.
checkArrOrRefArrT :: Monad m => Type -> m (Iota, Type)
checkArrOrRefArrT (ArrT iota tau _)          = return (iota, tau)
checkArrOrRefArrT (RefT (ArrT iota tau _) _) = return (iota, tau)
checkArrOrRefArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

unCComp :: CExp -> Cg CComp
unCComp (CComp comp) =
    return comp

unCComp (CDelay [] [] m) =
    m >>= unCComp

unCComp (CDelay {}) =
    panicdoc $ text "unCComp: CDelay with arguments"

unCComp ce =
    return $ return ce

unCDelay :: CExp -> Cg ([IVar], [(Var, Type)], Cg CExp)
unCDelay (CDelay ivs vbs m) =
    return (ivs, vbs, m)

unCDelay _ =
    panicdoc $ text "unCDelay: not a CDelay"

cgType :: Type -> Cg C.Type
cgType (UnitT {}) =
    return [cty|void|]

cgType (BoolT {}) =
    return [cty|typename uint8_t|]

cgType (BitT {}) =
    return bIT_ARRAY_ELEM_TYPE

cgType (IntT W8 Signed _) =
    return [cty|typename int8_t|]

cgType (IntT W16 Signed _) =
    return [cty|typename int16_t|]

cgType (IntT W32 Signed _) =
    return [cty|typename int32_t|]

cgType (IntT W64 Signed _) =
    return [cty|typename int64_t|]

cgType (IntT W8 Unsigned _) =
    return [cty|typename uint8_t|]

cgType (IntT W16 Unsigned _) =
    return [cty|typename uint16_t|]

cgType (IntT W32 Unsigned _) =
    return [cty|typename uint32_t|]

cgType (IntT W64 Unsigned _) =
    return [cty|typename uint64_t|]

cgType (FloatT W8 _) =
    return [cty|float|]

cgType (FloatT W16 _) =
    return [cty|float|]

cgType (FloatT W32 _) =
    return [cty|float|]

cgType (FloatT W64 _) =
    return [cty|double|]

cgType (StringT {}) =
    return [cty|char*|]

cgType (StructT s l) =
    return [cty|typename $id:(cstruct s l)|]

cgType (ArrT (ConstI n _) (BitT _) _) =
    return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$int:(bitArrayLen n)]|]

cgType (ArrT (ConstI n _) tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau[$int:n]|]

cgType tau@(ArrT (VarI {}) _ _) =
    panicdoc $ text "cgType: cannot translate array of unknown size:" <+> ppr tau

cgType tau@(ST {}) =
    panicdoc $ text "cgType: cannot translate ST types:" <+> ppr tau

cgType (RefT (ArrT _ tau _) _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (RefT tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (FunT ivs args ret _) = do
    let ivTys =  replicate (length ivs) [cparam|int|]
    argTys    <- mapM (\tau -> cgParam tau Nothing) args
    if isReturnedByRef ret
      then do retTy <- cgParam ret Nothing
              return [cty|void (*)($params:(ivTys ++ argTys ++ [retTy]))|]
      else do retTy <- cgType ret
              return [cty|$ty:retTy (*)($params:(ivTys ++ argTys))|]

cgType (TyVarT alpha _) =
    lookupTyVarType alpha >>= cgType

-- | Compile a function parameter.
cgParam :: Type -> Maybe C.Id -> Cg C.Param
cgParam tau maybe_cv = do
    ctau <- cgParamType tau
    case maybe_cv of
      Nothing -> return [cparam|$ty:ctau|]
      Just cv -> return [cparam|$ty:ctau $id:cv|]
  where
    cgParamType :: Type -> Cg C.Type
    cgParamType (ArrT (ConstI n _) (BitT _) _) =
        return [cty|const $ty:bIT_ARRAY_ELEM_TYPE[$int:(bitArrayLen n)]|]

    cgParamType (ArrT (ConstI n _) tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau[$int:n]|]

    cgParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgParamType tau = cgType tau

-- | Compile a function parameter that is used to return a result.
cgRetParam :: Type -> Maybe C.Id -> Cg C.Param
cgRetParam tau maybe_cv = do
    ctau <- cgRetParamType tau
    case maybe_cv of
      Nothing -> return [cparam|$ty:ctau|]
      Just cv -> return [cparam|$ty:ctau $id:cv|]
  where
    cgRetParamType :: Type -> Cg C.Type
    cgRetParamType (ArrT (ConstI n _) (BitT _) _) =
        return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$int:(bitArrayLen n)]|]

    cgRetParamType (ArrT (ConstI n _) tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau[$int:n]|]

    cgRetParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau*|]

    cgRetParamType tau = cgType tau

-- | Allocate storage for a temporary of the given core type. The name of the
-- temporary is gensym'd using @s@ with a prefix of @__@.
cgTemp :: String -> Type -> Cg CExp
cgTemp s tau = do
    cv <- gensym ("__" ++ s)
    cgStorage False cv tau

-- | Allocate storage for a binder with the given core type. The first
-- argument is a boolean flag that is 'True' if this binding corresponds to a
-- top-level core binding and 'False' otherwise.
cgBinder :: Bool -> Var -> Type -> Cg CExp
cgBinder isTopLevel v tau = do
    cv <- cvar v
    cgStorage isTopLevel cv tau

-- | Allocate storage for a C identifier with the given core type. The first
-- argument is a boolean flag that is 'True' if this binding corresponds to a
-- top-level core binding and 'False' otherwise.
cgStorage :: Bool -> C.Id -> Type -> Cg CExp
cgStorage isTopLevel cv tau =
    go tau
  where
    go :: Type -> Cg CExp
    go (UnitT {}) =
        return CVoid

    go (ArrT iota (BitT {}) _) = do
        cn <- cgIota iota
        case cn of
          CInt n -> appendLetDecl $ rl cv [cdecl|$ty:ctau $id:cv[$int:(bitArrayLen n)];|]
          _      -> appendLetDecl $ rl cv [cdecl|$ty:ctau* $id:cv = ($ty:ctau*) alloca($(bitArrayLen cn) * sizeof($ty:ctau));|]
        return $ CExp $ rl cv [cexp|$id:cv|]
      where
        ctau :: C.Type
        ctau = bIT_ARRAY_ELEM_TYPE

    go (ArrT iota tau _) = do
        ctau <- cgType tau
        cn <- cgIota iota
        case cn of
          CInt n -> appendLetDecl $ rl cv [cdecl|$ty:ctau $id:cv[$int:n];|]
          _      -> appendLetDecl $ rl cv [cdecl|$ty:ctau* $id:cv = ($ty:ctau*) alloca($cn * sizeof($ty:ctau));|]
        return $ CExp $ rl cv [cexp|$id:cv|]

    go tau = do
        ctau <- cgType tau
        appendLetDecl $ rl cv [cdecl|$ty:ctau $id:cv;|]
        return $ CExp $ rl cv [cexp|$id:cv|]

    -- Append a C declaration. If we are at top-level, make this a top-level C
    -- declaration; otherwise, make it a local C declaration.
    appendLetDecl :: C.InitGroup -> Cg ()
    appendLetDecl decl | isTopLevel = appendTopDecl decl
                       | otherwise  = appendDecl decl

-- | Generate code for a C temporary with a gensym'd name, based on @s@ and
-- prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgCTemp :: Located a => a -> String -> C.Type -> Maybe C.Initializer -> Cg CExp
cgCTemp l s ctau maybe_cinit = do
    cv <- gensym ("__" ++ s)
    case maybe_cinit of
      Nothing    -> appendDecl $ rl l [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendDecl $ rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp $ rl l [cexp|$id:cv|]

-- | Label the statements generated by the continuation @k@ with the specified
-- label. We only generate a C label when the label is actually used, as
-- determined by @isLabelUsed@.
cgWithLabel :: Label -> Cg a -> Cg a
cgWithLabel lbl k = do
    required <- isLabelUsed lbl
    if required
      then do (stms, x) <- collectStms k
              case stms of
                []     -> appendStm [cstm|$id:lblMacro:;|]
                [s]    -> appendStm [cstm|$id:lblMacro: $stm:s|]
                (s:ss) -> appendStms [cstms|$id:lblMacro: $stm:s $stms:ss|]
              return x
      else k
  where
    -- We need to use the @LABEL@ macro on the label. Gross, but what can ya
    -- do...
    lblMacro :: Label
    lblMacro = C.Id ("LABEL(" ++ ident ++ ")") l

    ident :: String
    l :: SrcLoc
    C.Id ident l = lbl

-- | A 'TakeK' continuation takes a label, the number of elements to take, the
-- type of the elements, a continuation that computes a 'CComp' from the 'CExp'
-- representing the taken elements, and a continuation that generates code
-- corresponding to the 'CComp' returned by the first continuation. Why not one
-- continuation of type @CExp -> Cg ()@ instead of two that we have to manually
-- chain together?  In general, we may want look inside the 'CComp' to see what
-- it does with the taken values. In particular, we need to see the label of the
-- 'CComp' so that we can save it as a continuation.
type TakeK = Label -> Int -> Type -> (CExp -> CComp) -> (CComp -> Cg ()) -> Cg ()

-- | A 'EmitK' continuation takes a label, the type of the value being emitted,
-- a 'CExp' representing the elements to emit, a 'CComp' representing the emit's
-- continuation, and a continuation that generates code corresponding to the
-- 'CComp'. We split the continuation into two parts just as we did for 'TakeK'
-- for exactly the same reason.
type EmitK = Label -> Type -> CExp -> CComp -> (CComp -> Cg ()) -> Cg ()

-- | A 'DoneK' continuation takes a 'CExp' representing the returned value and
-- generates the appropriate code.
type DoneK = CExp -> Cg ()

-- | Compile a 'CComp' that doesn't take or emit, and generate code that places
-- the result of the computation @ccomp@, which has 'Type' @tau_res@, in @cres'.
cgPureishCComp :: Type -> CExp -> CComp -> Cg ()
cgPureishCComp tau_res cres ccomp =
    cgCComp takek emitk donek ccomp
  where
    takek :: TakeK
    takek _ _ _ _ _ =
        panicdoc $ text "Pure computation tried to take!"

    emitk :: EmitK
    emitk _ _ _ _ _ =
        panicdoc $ text "Pure computation tried to emit!"

    donek :: DoneK
    donek ce =
        cgAssign tau_res cres ce

cgCComp :: TakeK
        -> EmitK
        -> DoneK
        -> CComp
        -> Cg ()
cgCComp takek emitk donek ccomp =
    cgFree ccomp
  where
    cgFree :: CComp -> Cg ()
    cgFree (Pure ce) = donek ce
    cgFree (Free x)  = cgComp x

    cgComp :: Comp Label CComp -> Cg ()
    cgComp (CodeC l c k) = cgWithLabel l $ do
        tell c
        cgFree k

    cgComp (TakeC l tau k) =
        takek l 1 tau k cgFree

    cgComp (TakesC l n tau k) =
        takek l n tau k cgFree

    cgComp (EmitC l tau ce k) =
        emitk l tau ce k cgFree

    cgComp (IfC l cv ce thenk elsek k) = cgWithLabel l $ do
        cgIf (return ce) (cgFree thenk) (cgFree elsek)
        cgFree (k cv)

    cgComp (ParC tau tau_res cres left right k) = do
        cgParSingleThreaded tau tau_res cres left right k

    cgComp (BindC l tau cv ce k) = cgWithLabel l $ do
        cgAssign tau cv ce
        cgFree k

    cgComp (EndC {}) =
        return ()

    cgComp (DoneC l ce) = cgWithLabel l $ do
        donek ce

    cgComp (LabelC l k) = cgWithLabel l $ do
        cgFree k

    cgComp (GotoC l) =
        appendStm [cstm|JUMP($id:l);|]

    cgParSingleThreaded :: Type -> Type -> CExp -> CComp -> CComp -> (CExp -> CComp) -> Cg ()
    cgParSingleThreaded tau_internal tau_res cres left right k = do
        -- Create the computation that follows the par. We ensure that it has a
        -- label so that we can jump to it when we are done. Note that @kl@ /may
        -- not/ be equal to @parl@, in particular if the computation returned by
        -- @k res@ itself has a label!
        parl      <- genLabel "park"
        let kcomp =  labelC parl >> k cres
        kl        <- ccompLabel kcomp
        void $ useLabel kl
        -- Generate variables to hold the left and right computations'
        -- continuations.
        leftl   <- ccompLabel left
        rightl  <- ccompLabel right
        cleftk  <- cgCTemp tau_internal "par_leftk"  [cty|typename KONT|] (Just [cinit|LABELADDR($id:leftl)|])
        crightk <- cgCTemp tau_internal "par_rightk" [cty|typename KONT|] (Just [cinit|LABELADDR($id:rightl)|])
        -- Generate a pointer to the current element in the buffer.
        ctau  <- cgType tau_internal
        cbuf  <- cgCTemp tau_internal "par_buf"  [cty|$ty:ctau|]  Nothing
        cbufp <- cgCTemp tau_internal "par_bufp" [cty|const $ty:ctau*|] Nothing
        -- Generate code for the left and right computations.
        cgCComp (takek' cleftk crightk cbuf cbufp)
                emitk
                (donek' kl)
                right
        cgCComp takek
                (emitk' cleftk crightk cbuf cbufp)
                (donek' kl)
                left
        -- Generate code for our continuation
        cgFree kcomp
      where
        takek' :: CExp -> CExp -> CExp -> CExp -> TakeK
        -- The one element take is easy. We know the element will be in @cbufp@,
        -- so we call @k1@ with @cbufp@ as the argument, which generates a
        -- 'CComp', @ccomp@ that represents the continuation that consumes the
        -- taken value. We then set the right computation's continuation to the
        -- label of @ccomp@, since it is the continuation, generate code to jump
        -- to the left computation's continuation, and then call @k2@ with
        -- @ccomp@ suitably modified to have a required label.
        takek' cleftk crightk _ cbufp l 1 _tau k1 k2 =
            cgWithLabel l $ do
            let ccomp =  k1 $ CExp [cexp|*$cbufp|]
            lbl       <- ccompLabel ccomp
            appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
            appendStm [cstm|INDJUMP($cleftk);|]
            k2 ccomp

        -- The multi-element take is a bit tricker. We allocate a buffer to hold
        -- all the elements, and then loop, jumping to the left computation's
        -- continuation repeatedly, until the buffer is full. Then we fall
        -- through to the next action, which is why we call @k2@ with @ccomp@
        -- without forcing its label to be required---we don't need the label!
        takek' cleftk crightk _ cbufp l n tau@(BitT {}) k1 k2 =
            cgWithLabel l $ do
            ctau      <- cgType tau
            carr      <- cgCTemp tau "par_takes_xs" [cty|$ty:ctau[$int:(bitArrayLen n)]|] Nothing
            lbl       <- genLabel "inner_takesk"
            void $ useLabel lbl
            let ccomp =  k1 carr
            appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
            cgFor 0 (fromIntegral n) $ \ci -> do
                appendStm [cstm|INDJUMP($cleftk);|]
                cgWithLabel lbl $
                    cgBitArrayWrite carr ci (CExp [cexp|*$cbufp|])
            k2 ccomp

        takek' cleftk crightk _ cbufp l n tau k1 k2 =
            cgWithLabel l $ do
            ctau      <- cgType tau
            carr      <- cgCTemp tau "par_takes_xs" [cty|$ty:ctau[$int:n]|] Nothing
            lbl       <- genLabel "inner_takesk"
            void $ useLabel lbl
            let ccomp =  k1 carr
            appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
            cgFor 0 (fromIntegral n) $ \ci -> do
                appendStm [cstm|INDJUMP($cleftk);|]
                cgWithLabel lbl $
                    appendStm [cstm|$carr[$ci] = *$cbufp;|]
            k2 ccomp

        emitk' :: CExp -> CExp -> CExp -> CExp -> EmitK
        emitk' cleftk crightk cbuf cbufp l (ArrT (ConstI 1 _) tau _) ce ccomp k =
            cgWithLabel l $ do
            lbl <- ccompLabel ccomp
            appendStm [cstm|$cleftk = LABELADDR($id:lbl);|]
            cidx <- cgIdx tau ce 0
            cgAssignBufp tau cbuf cbufp cidx
            appendStm [cstm|INDJUMP($crightk);|]
            k ccomp

        emitk' cleftk crightk cbuf cbufp l (ArrT iota tau _) ce ccomp k = do
            cn    <- cgIota iota
            loopl <- genLabel "emitsk_next"
            void $ useLabel l
            void $ useLabel loopl
            cgWithLabel l $ do
                appendStm [cstm|$cleftk = LABELADDR($id:loopl);|]
                cgFor 0 cn $ \ci -> do
                    cidx <- cgIdx tau ce ci
                    cgAssignBufp tau cbuf cbufp cidx
                    appendStm [cstm|INDJUMP($crightk);|]
                    -- Because we need a statement to label, but the continuation is
                    -- the next loop iteration...
                    cgWithLabel loopl $
                        appendStm [cstm|;|]
            k ccomp

        -- @tau@ must be a base (scalar) type
        emitk' cleftk crightk cbuf cbufp l tau ce ccomp k =
            cgWithLabel l $ do
            lbl <- ccompLabel ccomp
            appendStm [cstm|$cleftk = LABELADDR($id:lbl);|]
            cgAssignBufp tau cbuf cbufp ce
            appendStm [cstm|INDJUMP($crightk);|]
            k ccomp

        donek' :: Label -> DoneK
        donek' kl ce = do
            cgAssign tau_res cres ce
            appendStm [cstm|JUMP($id:kl);|]

        -- Assign the value @ce@ to the buffer pointer @cbufp@. If @ce@ is not
        -- an lvalue, then stash it in @cbuf@ first and set @cbufp@ to point to
        -- @cbuf@. This ensures that we can always pass buffer elements by
        -- reference.
        cgAssignBufp :: Type -> CExp -> CExp -> CExp -> Cg ()
        cgAssignBufp tau _ cbufp ce | isLvalue ce = do
            caddr <- cgAddrOf tau ce
            appendStm [cstm|$cbufp = $caddr;|]

        cgAssignBufp tau cbuf cbufp ce = do
            cgAssign tau cbuf ce
            appendStm [cstm|$cbufp = &$cbuf;|]

-- | Return 'True' if a compiled expression is a C lvalue.
isLvalue :: CExp -> Bool
isLvalue (CIdx (BitT {}) _ _) =
    False

isLvalue (CIdx _ ce _) =
    isLvalue ce

isLvalue (CSlice (BitT {}) carr (CInt i) _) =
    isLvalue carr && i `rem` bIT_ARRAY_ELEM_BITS == 0

isLvalue (CSlice (BitT {}) _ _ _) =
    False

isLvalue (CSlice _ carr _ _) =
    isLvalue carr

isLvalue (CExp (C.Var {}))       = True
isLvalue (CExp (C.Member {}))    = True
isLvalue (CExp (C.PtrMember {})) = True
isLvalue (CExp (C.Index {}))     = True
isLvalue _                       = False

-- | @'resultType' tau@ returns the type of the result of a computation of
-- type @tau@. If @tau@ is @ST (C tau') s a b@, then the type of the result of
-- the computation is @tau'@. For a pure computation of type @tau@, the result
-- is just of type @tau. For a non-terminating computation of type @ST T s a b@,
-- the result type is the unit type.
resultType :: Type -> Type
resultType (ST _ (C tau) _ _ _ _) = tau
resultType (ST _ T _ _ _ l)       = UnitT l
resultType tau                    = tau

-- | Return @True@ is a value of the given type is passed by reference, i.e., if
-- we need to pass the address of the value's corresponding 'CExp'. Note that
-- arrays are always passed by reference, so 'isPassByRef' returns @False@ for
-- array types.
isPassByRef :: Type -> Bool
isPassByRef (RefT (ArrT {}) _) = False
isPassByRef (RefT {})          = True
isPassByRef (ST {})            = error "isPassByRef: got ST type"
isPassByRef _                  = False

-- | Return @True@ if a value of the given type is passed by reference as an
-- argument when it is the result of a function call.
isReturnedByRef :: Type -> Bool
isReturnedByRef (ArrT {}) = True
isReturnedByRef _         = False

-- | @'cgAssign' tau ce1 ce2@ generates code to assign @ce2@, which has type
-- @tau@, to @ce1@.
cgAssign :: Type -> CExp -> CExp -> Cg ()
-- If we don't care about the value, don't actually perform the assignment. This
-- can happen when we are in a loop---we don't actually need the result of the
-- computation in the body of the loop, just its effect(s).
cgAssign _ _ CVoid =
    return ()

-- If the type of the value is unit, don't actually perform the
-- assignment. However, we *do* need no evaluate the expression; it could, for
-- example, be a function call!
cgAssign (UnitT {}) _ ce =
   appendStm [cstm|$ce;|]

cgAssign (RefT (BitT {}) _) (CIdx _ carr cidx) ce2 =
    cgBitArrayWrite carr cidx ce2

cgAssign tau0 ce1 ce2 | Just (iota, BitT {}) <- checkArrOrRefArrT tau0 = do
    clen <- cgIota iota
    cgAssignBitArray ce1 ce2 clen

cgAssign tau0 ce1 ce2 | Just (iota, tau) <- checkArrOrRefArrT tau0 = do
    ctau <- cgType tau
    ce1' <- cgArrayAddr ce1
    ce2' <- cgArrayAddr ce2
    clen <- cgIota iota
    appendStm [cstm|memcpy($ce1', $ce2', $clen*sizeof($ty:ctau));|]
  where
    cgArrayAddr :: CExp -> Cg CExp
    cgArrayAddr (CSlice (BitT _) _ _ _) =
        panicdoc $ text "cgArrayAddr: the impossible happened!"

    cgArrayAddr (CSlice _ carr cidx _) =
        return $ CExp [cexp|&$carr[$cidx]|]

    cgArrayAddr ce =
        return ce

-- We call 'unPtr' on @cv@ because the lhs of an assignment is a ref type and
-- may need to be dereferenced.
cgAssign _ cv ce =
    appendStm [cstm|$(unPtr cv) = $ce;|]

cgAssignBitArray :: CExp -> CExp -> CExp -> Cg ()
cgAssignBitArray ce1 ce2 clen =
    appendStm [cstm|kz_bitarray_copy($cdst, $cdstIdx, $csrc, $csrcIdx, $clen);|]
  where
    cdst, cdstIdx :: CExp
    (cdst, cdstIdx) = unBitSlice ce1

    csrc, csrcIdx :: CExp
    (csrc, csrcIdx) = unBitSlice ce2

    unBitSlice :: CExp -> (CExp, CExp)
    unBitSlice (CSlice _ carr cidx _) =
        (carr, cidx)

    unBitSlice carr =
        (carr, 0)

cgIdx :: Type -> CExp -> CExp -> Cg CExp
cgIdx tau carr cidx =
    return $ CIdx tau carr cidx

cgSlice :: Type -> CExp -> CExp -> Int -> Cg CExp
cgSlice tau carr cidx len =
    return $ CSlice tau carr cidx len

cgAddrOf :: Type -> CExp -> Cg CExp
cgAddrOf _ (CPtr ce) =
    return ce

cgAddrOf (ArrT {}) ce | isLvalue ce =
    return $ CExp [cexp|$ce|]

cgAddrOf _ ce | isLvalue ce =
    return $ CExp [cexp|&$ce|]

cgAddrOf tau@(ArrT {}) ce = do
    ctemp <- cgTemp "addrof" tau
    cgAssign tau ctemp ce
    return $ CExp [cexp|$ctemp|]

cgAddrOf tau ce = do
    ctemp <- cgTemp "addrof" tau
    cgAssign tau ctemp ce
    return $ CExp [cexp|&$ctemp|]

-- | Generate code for an if statement.
cgIf :: Cg CExp -> Cg () -> Cg () -> Cg ()
cgIf e1 e2 e3 = do
    ce1     <- e1
    citems2 <- inNewBlock_ e2
    citems3 <- inNewBlock_ e3
    if citems3 == mempty
      then appendStm [cstm|if ($ce1) { $items:citems2 }|]
      else appendStm [cstm|if ($ce1) { $items:citems2 } else { $items:citems3 }|]

-- | Generate C code for a @for@ loop. @cfrom@ and @cto@ are the loop bounds,
-- and @k@ is a continuation that takes an expression representing the loop
-- index and generates the body of the loop.
cgFor :: CExp -> CExp -> (CExp -> Cg ()) -> Cg ()
cgFor cfrom@(CInt i) (CInt j) k
    | j <= i     = return ()
    | j == i + 1 = k cfrom

cgFor cfrom cto k = do
    ci <- gensym "__i"
    appendDecl [cdecl|int $id:ci;|]
    (cbody, x) <- inNewBlock $
                  k (CExp [cexp|$id:ci|])
    appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) { $items:cbody }|]
    return x

-- | Append a comment to the list of top-level definitions.
appendTopComment :: Doc -> Cg ()
appendTopComment doc =
    appendTopDef [cedecl|$esc:(pretty 80 (text "/*" <+> align doc <+> text "*/"))|]

-- | Return a C hex constant.
chexconst :: Integer -> C.Exp
chexconst i = C.Const (C.IntConst ("0x" ++ showHex i "") C.Unsigned i noLoc) noLoc

-- | Return the C identifier corresponding to a value that is an instance of
-- 'Named'.
cvar :: (Located a, Named a) => a -> Cg C.Id
cvar x = reloc (locOf x) <$> gensym (zencode (namedString x))

-- | Return the C identifier corresponding to a struct.
cstruct :: Struct -> SrcLoc -> C.Id
cstruct s l = C.Id (namedString s ++ "_t") l

-- | Z-encode a string. This converts a string with special characters into a
-- form that is guaranteed to be usable as an identifier by a C compiler or
-- assembler. See
-- <https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
-- Z-Encoding>
zencode :: String -> String
zencode s = concatMap zenc s
  where
    -- | Implementation of Z-encoding. See:
    -- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
    zenc :: Char -> [Char]
    zenc c | 'a' <= c && c <= 'y' = [c]
              | 'A' <= c && c <= 'Y' = [c]
              | '0' <= c && c <= '9' = [c]
    zenc 'z'  = "zz"
    zenc 'Z'  = "ZZ"
    zenc '('  = "ZL"
    zenc ')'  = "ZR"
    zenc '['  = "ZM"
    zenc ']'  = "ZN"
    zenc ':'  = "ZC"
    zenc '&'  = "za"
    zenc '|'  = "zb"
    zenc '^'  = "zc"
    zenc '$'  = "zd"
    zenc '='  = "ze"
    zenc '>'  = "zg"
    zenc '#'  = "zh"
    zenc '.'  = "zi"
    zenc '<'  = "zl"
    zenc '-'  = "zm"
    zenc '!'  = "zn"
    zenc '+'  = "zp"
    zenc '\'' = "zq"
    zenc '\\' = "zr"
    zenc '/'  = "zs"
    zenc '*'  = "zt"
    zenc '_'  = "zu"
    zenc '%'  = "zv"
    zenc c    = "z" ++ hexOf c ++ "U"

    hexOf :: Char -> String
    hexOf c =
        case showHex (ord c) "" of
          [] -> []
          h@(c : _) | 'a' <= c && c <= 'f' -> '0' : h
                    | otherwise            -> h

rl :: (Located a, Relocatable b) => a -> b -> b
rl l x = reloc (locOf l) x
