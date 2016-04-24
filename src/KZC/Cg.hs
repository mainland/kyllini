{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg (
    evalCg,

    compileProgram
  ) where

import Prelude

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (forM_,
                      mplus,
                      when)
import Data.Bits
import Data.Loc
import Data.Maybe (isJust)
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import qualified Language.C.Syntax as C
import Numeric (showHex)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Cg.CExp
import KZC.Cg.Monad
import KZC.Cg.Util
import KZC.Check.Path
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Name
import KZC.Optimize.Fuse
import KZC.Platform
import KZC.Quote.C
import KZC.Staged
import KZC.Summary
import KZC.Trace
import KZC.Uniq

-- | Create a oneshot continuation.
oneshot :: Type -> (CExp l -> Cg l a) -> Kont l a
oneshot tau f = OneshotK Nothing tau f

-- | Create a oneshot continuation with the name of a binder to use.
oneshotBinder :: BoundVar -> Type -> (CExp l -> Cg l a) -> Kont l a
oneshotBinder bv tau f = OneshotK (Just bv) tau f

-- | Create a multishot continuation.
multishot :: (CExp l -> Cg l a) -> Kont l a
multishot f = MultishotK f

-- | Create a multishot continuation that binds its argument to the given
-- 'CExp'.
multishotBind :: Type -> CExp l -> Kont l ()
multishotBind tau cv = MultishotBindK tau cv (const $ return ())

-- | Return 'True' if the continuation is oneshot, 'False' otherwise.
isOneshot :: Kont l a -> Bool
isOneshot (OneshotK {})       = True
isOneshot (MultishotK {})     = False
isOneshot (MultishotBindK {}) = False

-- | Split a oneshot continuation into two parts: a multishot continuation that
-- stores values in a temporary, and a new oneshot continuation that consumes
-- the temporary and does the real work.
splitOneshot :: Kont l a -> Cg l (Kont l (), Cg l a)
splitOneshot (OneshotK Nothing tau f) = do
    ctemp <- cgTemp "oneshot" tau_res
    return (MultishotK $ cgAssign tau_res ctemp, f ctemp)
  where
    tau_res :: Type
    tau_res = resultType tau

splitOneshot (OneshotK (Just bv) tau f) = do
    cv <- cgBinder (bVar bv) tau
    return (MultishotK $ cgAssign tau cv, f cv)

splitOneshot (MultishotK {}) =
    fail "splitOneshot: cannot split a multishot continuation"

splitOneshot (MultishotBindK {}) =
    fail "splitOneshot: cannot split a multishot continuation"

-- | Split a continuation into two parts: a 'CExp' in which we can place the
-- result, and a continuation to be called after the result has been placed into
-- the 'CExp'.
splitMultishotBind :: String -> Type -> Bool -> Kont l a -> Cg l (CExp l, Cg l a)
splitMultishotBind v _ _needsLvalue (OneshotK Nothing tau f) = do
    ctemp <- cgTemp v tau_res
    return (ctemp, f ctemp)
  where
    tau_res :: Type
    tau_res = resultType tau

splitMultishotBind _v _tau _needsLvalue (OneshotK (Just bv) tau f) = do
    cv <- cgBinder (bVar bv) tau
    return (cv, f cv)

splitMultishotBind v tau _needsLvalue (MultishotK f) = do
    ctemp <- cgTemp v tau
    return (ctemp, f ctemp)

splitMultishotBind v tau True (MultishotBindK _tau' cv f) | not (isLvalue cv) = do
    ctemp <- cgTemp v tau
    return (ctemp, cgAssign tau cv ctemp >> f cv)

splitMultishotBind _v _tau _ (MultishotBindK _tau' cv f) =
    return (cv, f cv)

-- | Run a 'Kont l a' by giving it a 'CExp'.
runKont :: Kont l a -> CExp l -> Cg l a
runKont (OneshotK _ _ k)          ce = k ce
runKont (MultishotK k)            ce = k ce
runKont (MultishotBindK tau cv k) ce = do cgAssign tau cv ce
                                          k cv

-- | Map a function over a continuation.
mapKont :: ((CExp l -> Cg l a) -> (CExp l -> Cg l a))
        -> Kont l a
        -> Kont l a
mapKont f (OneshotK bv tau g)       = OneshotK bv tau (f g)
mapKont f (MultishotK g)            = MultishotK (f g)
mapKont f (MultishotBindK tau cv g) = MultishotBindK tau cv (f g)

restrict, static :: C.TypeQual
restrict = C.EscTypeQual "RESTRICT" noLoc
static   = C.EscTypeQual "STATIC" noLoc

compileProgram :: forall l . IsLabel l => Program l -> Cg l ()
compileProgram (Program decls comp tau) = do
    appendTopDef [cedecl|$esc:("#include <kz.h>")|]
    appendTopDecl [cdecl|typename kz_buf_t $id:in_buf;|]
    appendTopDecl [cdecl|typename kz_buf_t $id:out_buf;|]
    (clabels, cblock) <-
        collectLabels $
        inNewThreadBlock_ $
        cgDecls decls $ do
        -- Allocate and initialize input and output buffers
        (_, _, a, b) <- checkST tau
        cgInitInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgInitOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
        -- Create storage for the result
        cres <- cgTemp "main_res" (resultType tau)
        -- The done continuation simply puts the computation's result in cres
        cgTimed $ cgThread takek emitk emitsk tau comp $
            multishotBind (resultType tau) cres
        -- Clean up input and output buffers
        cgCleanupInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgCleanupOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
    cgLabels clabels
    appendTopDef [cedecl|
void kz_main(const typename kz_params_t* $id:params)
{
    $items:cblock
}|]
    stats <- getStats
    traceCg $ nest 2 $ text "Code generator statistics:" </> ppr stats
  where
    in_buf, out_buf, params :: C.Id
    in_buf  = "in"
    out_buf = "out"
    params = "params"

    takek :: TakeK l
    takek n tau _k = do
        -- Generate a pointer to the current element in the buffer.
        ctau   <- cgType tau
        cbuf   <- cgCTemp tau "take_bufp" [cty|const $ty:ctau*|] (Just [cinit|NULL|])
        cinput <- cgInput tau (CExp [cexp|$id:in_buf|]) (fromIntegral n)
        appendStm [cstm|$cbuf = (const $ty:ctau*) $cinput;|]
        appendStm [cstm|if ($cbuf == NULL) { BREAK; }|]
        case (tau, n) of
            (_, 1) | isBitT tau -> return $ CExp [cexp|*$cbuf & 1|]
                   | otherwise  -> return $ CExp [cexp|*$cbuf|]
            _                   -> return $ CExp [cexp|$cbuf|]

    emitk :: EmitK l
    emitk tau ce _k = do
        ceAddr <- cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceAddr

    emitsk :: EmitsK l
    emitsk iota tau ce _k = do
        ceAddr <- cgAddrOf (arrT iota tau) ce
        cgOutput (arrT iota tau) (CExp [cexp|$id:out_buf|]) 1 ceAddr

    cgInitInput :: Type -> CExp l -> CExp l -> Cg l ()
    cgInitInput tau cp cbuf =
        cgBufferInit "kz_init_input" tau cp cbuf

    cgInitOutput :: Type -> CExp l -> CExp l -> Cg l ()
    cgInitOutput tau cp cbuf =
        cgBufferInit "kz_init_output" tau cp cbuf

    cgCleanupInput :: Type -> CExp l -> CExp l -> Cg l ()
    cgCleanupInput tau cp cbuf =
        cgBufferCleanup "kz_cleanup_input" tau cp cbuf

    cgCleanupOutput :: Type -> CExp l -> CExp l -> Cg l ()
    cgCleanupOutput tau cp cbuf =
        cgBufferCleanup "kz_cleanup_output" tau cp cbuf

    cgBufferInit :: String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferInit = cgBufferConfig appendThreadInitStm

    cgBufferCleanup :: String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferCleanup = cgBufferConfig appendThreadCleanupStm

    cgBufferConfig :: (C.Stm -> Cg l ()) -> String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferConfig appStm f tau cp cbuf =
        go tau
      where
        go :: Type -> Cg l ()
        go (ArrT _ tau _)          = go tau
        go tau | isBitT tau        = appStm [cstm|$id:(fname "bit")($cp, &$cbuf);|]
        go (FixT I S (W 8)  0 _)   = appStm [cstm|$id:(fname "int8")($cp, &$cbuf);|]
        go (FixT I S (W 16) 0 _)   = appStm [cstm|$id:(fname "int16")($cp, &$cbuf);|]
        go (FixT I S (W 32) 0 _)   = appStm [cstm|$id:(fname "int32")($cp, &$cbuf);|]
        go (FixT I U (W 8)  0 _)   = appStm [cstm|$id:(fname "uint8")($cp, &$cbuf);|]
        go (FixT I U (W 16) 0 _)   = appStm [cstm|$id:(fname "uint16")($cp, &$cbuf);|]
        go (FixT I U (W 32) 0 _)   = appStm [cstm|$id:(fname "uint32")($cp, &$cbuf);|]
        go tau@(FixT {})           = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                     text "are not supported."
        go (FloatT FP16 _)         = appStm [cstm|$id:(fname "float")($cp, &$cbuf);|]
        go (FloatT FP32 _)         = appStm [cstm|$id:(fname "float")($cp, &$cbuf);|]
        go (FloatT FP64 _)         = appStm [cstm|$id:(fname "double")($cp, &$cbuf);|]
        go (StructT "complex16" _) = appStm [cstm|$id:(fname "complex16")($cp, &$cbuf);|]
        go (StructT "complex32" _) = appStm [cstm|$id:(fname "complex32")($cp, &$cbuf);|]
        go _                       = appStm [cstm|$id:(fname "bytes")($cp, &$cbuf);|]

        fname :: String -> C.Id
        fname t = fromString (f ++ "_" ++ t)

    cgInput :: Type -> CExp l -> CExp l -> Cg l (CExp l)
    cgInput tau cbuf cn = go tau
      where
        go :: Type -> Cg l (CExp l)
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgInput tau cbuf (cn*ci)
        go tau | isBitT tau        = return $ CExp [cexp|kz_input_bit(&$cbuf, $cn)|]
        go (FixT I S (W 8)  0 _)   = return $ CExp [cexp|kz_input_int8(&$cbuf, $cn)|]
        go (FixT I S (W 16) 0 _)   = return $ CExp [cexp|kz_input_int16(&$cbuf, $cn)|]
        go (FixT I S (W 32) 0 _)   = return $ CExp [cexp|kz_input_int32(&$cbuf, $cn)|]
        go (FixT I U (W 8)  0 _)   = return $ CExp [cexp|kz_input_uint8(&$cbuf, $cn)|]
        go (FixT I U (W 16) 0 _)   = return $ CExp [cexp|kz_input_uint16(&$cbuf, $cn)|]
        go (FixT I U (W 32) 0 _)   = return $ CExp [cexp|kz_input_uint32(&$cbuf, $cn)|]
        go tau@(FixT {})           = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                     text "are not supported."
        go (FloatT FP16 _)         = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT FP32 _)         = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT FP64 _)         = return $ CExp [cexp|kz_input_double(&$cbuf, $cn)|]
        go (StructT "complex16" _) = return $ CExp [cexp|kz_input_complex16(&$cbuf, $cn)|]
        go (StructT "complex32" _) = return $ CExp [cexp|kz_input_complex32(&$cbuf, $cn)|]
        go (TyVarT alpha _)        = lookupTyVarType alpha >>= go
        go tau                     = do ctau <- cgType tau
                                        return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

    cgOutput :: Type -> CExp l -> CExp l -> CExp l -> Cg l ()
    cgOutput tau cbuf cn cval = go tau
      where
        go :: Type -> Cg l ()
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgOutput tau cbuf (cn*ci) cval
        go tau | isBitT tau        = appendStm [cstm|kz_output_bit(&$cbuf, $cval, $cn);|]
        go (FixT I S (W 8)  0 _)   = appendStm [cstm|kz_output_int8(&$cbuf, $cval, $cn);|]
        go (FixT I S (W 16) 0 _)   = appendStm [cstm|kz_output_int16(&$cbuf, $cval, $cn);|]
        go (FixT I S (W 32) 0 _)   = appendStm [cstm|kz_output_int32(&$cbuf, $cval, $cn);|]
        go (FixT I U (W 8)  0 _)   = appendStm [cstm|kz_output_uint8(&$cbuf, $cval, $cn);|]
        go (FixT I U (W 16) 0 _)   = appendStm [cstm|kz_output_uint16(&$cbuf, $cval, $cn);|]
        go (FixT I U (W 32) 0 _)   = appendStm [cstm|kz_output_uint32(&$cbuf, $cval, $cn);|]
        go tau@(FixT {})           = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                     text "are not supported."
        go (FloatT FP16 _)         = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT FP32 _)         = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT FP64 _)         = appendStm [cstm|kz_output_double(&$cbuf, $cval, $cn);|]
        go (StructT "complex16" _) = appendStm [cstm|kz_output_complex16(&$cbuf, $cval, $cn);|]
        go (StructT "complex32" _) = appendStm [cstm|kz_output_complex32(&$cbuf, $cval, $cn);|]
        go (TyVarT alpha _)        = lookupTyVarType alpha >>= go
        go tau                     = do ctau <- cgType tau
                                        appendStm [cstm|kz_output_bytes(&$cbuf, $cval, $cn*sizeof($ty:ctau));|]

cgTimed :: forall l a . Cg l a -> Cg l a
cgTimed m = do
    flags <- askFlags
    go flags
  where
    go :: Flags -> Cg l a
    go flags | testDynFlag Timers flags = do
        cpu_time_start  :: C.Id <- gensym "cpu_time_start"
        cpu_time_end    :: C.Id <- gensym "cpu_time_end"
        real_time_start :: C.Id <- gensym "real_time_start"
        real_time_end   :: C.Id <- gensym "real_time_end"
        appendTopDecl [cdecl|long double $id:cpu_time_start, $id:cpu_time_end;|]
        appendTopDecl [cdecl|long double $id:real_time_start, $id:real_time_end;|]
        appendStm [cstm|$id:cpu_time_start = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_start = kz_get_real_time();|]
        x <- m
        appendStm [cstm|$id:cpu_time_end = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_end = kz_get_real_time();|]
        appendStm [cstm|printf("Time elapsed (usec): %d\n", (int) (($id:cpu_time_end - $id:cpu_time_start) * 1000000));|]
        appendStm [cstm|printf("Elapsed cpu time: %Les\n", $id:cpu_time_end - $id:cpu_time_start);|]
        appendStm [cstm|printf("Elapsed real time: %Les\n", $id:real_time_end - $id:real_time_start);|]
        return x

    go _flags =
        m

cgLabels :: forall l . IsLabel l => Set l -> Cg l ()
cgLabels ls = do
    go (Set.toList ls)
  where
    go :: [l] -> Cg l ()
    go [] = return ()

    go (l:ls) = do
        appendTopDef [cedecl|$esc:("#if !defined(FIRSTCLASSLABELS)")|]
        appendTopDef [cedecl|enum { $enums:(cl:cls) };|]
        appendTopDef [cedecl|$esc:("#endif /* !defined(FIRSTCLASSLABELS) */")|]
      where
        cl  :: C.CEnum
        cls :: [C.CEnum]
        cl  = [cenum|$id:l = 0|]
        cls = [ [cenum|$id:l|] | l <- ls]

-- | Generate code to check return value of a function call.
cgInitCheckErr :: Located a => C.Exp -> String -> a -> Cg l ()
cgInitCheckErr ce msg x =
    appendThreadInitStm [cstm|kz_check_error($ce, $string:(renderLoc x), $string:msg);|]

-- | Generate code to check return value of a function call.
cgCheckErr :: Located a => C.Exp -> String -> a -> Cg l ()
cgCheckErr ce msg x =
    appendStm [cstm|kz_check_error($ce, $string:(renderLoc x), $string:msg);|]

cgThread :: IsLabel l
         => TakeK  l  -- ^ Code generator for take
         -> EmitK  l  -- ^ Code generator for emit
         -> EmitsK l  -- ^ Code generator for emit
         -> Type      -- ^ Type of the result of the computation
         -> Comp l    -- ^ Computation to compiled
         -> Kont l () -- ^ Code generator to deal with result of computation
         -> Cg l ()
cgThread takek emitk emitsk tau comp k = do
    cblock <-
        inSTScope tau $
        inLocalScope $
        inNewThreadBlock_ $ do
        -- Keep track of the current continuation. This is only used when
        -- we do not have first class labels.
        l_start <- compLabel comp
        useLabel l_start
        appendThreadDecl [cdecl|typename KONT $id:cUR_KONT = LABELADDR($id:l_start);|]
        -- Create a label for the end of the computation
        l_done <- gensym "done"
        useLabel l_done
        -- Generate code for the computation
        useLabels (compUsedLabels comp)
        cgComp takek emitk emitsk comp l_done $ oneshot tau $ runKont k
    appendDecls [decl | C.BlockDecl decl <- cblock]
    appendStms [cstms|BEGIN_DISPATCH; $stms:([stm | C.BlockStm stm <- cblock]) END_DISPATCH;|]
  where
    cUR_KONT :: C.Id
    cUR_KONT = "curk"

cgDecls :: IsLabel l => [Decl l] -> Cg l a -> Cg l a
cgDecls [] k =
    k

cgDecls (decl:decls) k =
    cgDecl decl $ cgDecls decls k

cgDecl :: forall l a . IsLabel l => Decl l -> Cg l a -> Cg l a
cgDecl (LetD decl _) k =
    cgLocalDecl decl k

cgDecl decl@(LetFunD f iotas vbs tau_ret e l) k = do
    cf <- cvar f
    extendVars [(bVar f, tau)] $ do
    extendVarCExps [(bVar f, CExp [cexp|$id:cf|])] $ do
    appendTopComment (ppr f <+> colon <+> align (ppr tau))
    withSummaryContext decl $
        extendLetFun f iotas vbs tau_ret $ do
        (ciotas, cparams1) <- unzip <$> mapM cgIVar iotas
        (cvbs,   cparams2) <- unzip <$> mapM cgVarBind vbs
        cres_ident         <- gensym "let_res"
        citems <- inNewThreadBlock_ $
                  extendIVarCExps (iotas `zip` ciotas) $
                  extendVarCExps  (map fst vbs `zip` cvbs) $ do
                  cres <- if isReturnedByRef tau_res
                          then return $ CExp [cexp|$id:cres_ident|]
                          else cgTemp "let_res" tau_res
                  cgExp e $ multishotBind tau_res cres
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
    tau_res = resultType tau_ret

    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

cgDecl decl@(LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(bVar f, tau)] $
    extendVarCExps [(bVar f, CExp [cexp|$id:cf|])] $ do
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

cgDecl decl@(LetStructD s flds l) k = do
    withSummaryContext decl $ do
        cflds <- mapM cgField flds
        appendTopDecl $ rl l [cdecl|typedef struct $id:(cstruct s l) { $sdecls:cflds } $id:(cstruct s l);|]
    extendStructs [StructDef s flds l] k
  where
    cgField :: (Field, Type) -> Cg l C.FieldGroup
    cgField (fld, tau) = do
        let cfld =  zencode (namedString fld)
        ctau     <- cgType tau
        return [csdecl|$ty:ctau $id:cfld;|]

cgDecl (LetCompD v tau comp _) k =
    extendVars [(bVar v, tau)] $
    extendVarCExps [(bVar v, CComp compc)] $
    k
  where
    -- Compile a bound computation. This will be called in some future
    -- context. It may be called multiple times, so we need to create a copy of
    -- the computation with fresh labels before we compile it.
    compc :: forall a . CompC l a
    compc takek emitk emitsk klbl k =
        withInstantiatedTyVars tau $ do
        comp' <- uniquifyCompLabels comp
        useLabels (compUsedLabels comp')
        cgComp takek emitk emitsk comp' klbl k

cgDecl (LetFunCompD f ivs vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $
    extendVarCExps [(bVar f, CFunComp funcompc)] $
    k
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

    -- Compile a bound computation function given its arguments. This will be
    -- called in some future context. It may be called multiple times, so we
    -- need to create a copy of the body of the computation function with fresh
    -- labels before we compile it.
    funcompc :: forall a . FunCompC l a
    funcompc iotas es takek emitk emitsk klbl k =
        withInstantiatedTyVars tau_ret $ do
        comp'  <- uniquifyCompLabels comp
        ciotas <- mapM cgIota iotas
        ces    <- mapM cgArg es
        extendIVars (ivs `zip` repeat IotaK) $ do
        extendVars  vbs $ do
        extendIVarCExps (ivs `zip` ciotas) $ do
        extendVarCExps  (map fst vbs `zip` ces) $ do
        useLabels (compUsedLabels comp')
        cgComp takek emitk emitsk comp' klbl k
      where
        cgArg :: Arg l -> Cg l (CExp l)
        cgArg (ExpA e) =
            withFvContext e $
            cgExpOneshot e

        cgArg (CompA comp) =
            return $ CComp compc
          where
            compc :: forall a . CompC l a
            compc takek emitk emitsk klbl =
                cgComp takek emitk emitsk comp klbl

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context. We need to do this when
-- compiling a computation of computation function.
withInstantiatedTyVars :: Type -> Cg l a -> Cg l a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarTypes [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

cgLocalDecl :: forall l a . IsLabel l => LocalDecl -> Cg l a -> Cg l a
cgLocalDecl decl@(LetLD v tau e _) k =
    withSummaryContext decl $
    cgExp e $
    cgLetBinding v tau $ \cv ->
    extendVars [(bVar v, tau)] $
    extendVarCExps [(bVar v, cv)] $
    k

cgLocalDecl decl@(LetRefLD v tau maybe_e _) k =
    withSummaryContext decl $
    cgLetRefBinding v tau maybe_e $ \cve ->
    extendVars [(bVar v, refT tau)] $
    extendVarCExps [(bVar v, cve)] $
    k

-- | Generate a 'CExp' representing a constant. The 'CExp' produced is
-- guaranteed to be a legal C initializer, so it can be used in an array or
-- struct initializer.
cgConst :: forall l . IsLabel l => Const -> Cg l (CExp l)
cgConst UnitC            = return CVoid
cgConst (BoolC b)        = return $ CBool b
cgConst (FixC I _ _ 0 r) = return $ CInt (numerator r)
cgConst (FixC {})        = faildoc $ text "Fractional and non-unit scaled fixed point values are not supported."
cgConst (FloatC _ r)     = return $ CFloat r
cgConst (StringC s)      = return $ CExp [cexp|$string:s|]

cgConst c@(ArrayC cs) = do
    (_, tau) <- inferConst noLoc c >>= checkArrT
    ces      <- mapM cgConst cs
    return $ CInit [cinit|{ $inits:(cgArrayConstInits tau ces) }|]
  where
    cgArrayConstInits :: Type -> [CExp l] -> [C.Initializer]
    cgArrayConstInits tau ces | isBitT tau =
        finalizeBits $ foldl mkBits (0,0,[]) ces
      where
        mkBits :: (CExp l, Int, [C.Initializer]) -> CExp l -> (CExp l, Int, [C.Initializer])
        mkBits (cconst, i, cinits) ce
            | i == bIT_ARRAY_ELEM_BITS - 1 = (0,         0, const cconst' : cinits)
            | otherwise                    = (cconst', i+1, cinits)
          where
            cconst' :: CExp l
            cconst' = cconst .|. (ce `shiftL` i)

        finalizeBits :: (CExp l, Int, [C.Initializer]) -> [C.Initializer]
        finalizeBits (_,      0, cinits) = reverse cinits
        finalizeBits (cconst, _, cinits) = reverse $ const cconst : cinits

        const :: CExp l -> C.Initializer
        const (CInt i) = [cinit|$(chexconst i)|]
        const ce       = toInit ce

    cgArrayConstInits _tau ces =
        map toInit ces

cgConst (StructC s flds) = do
    StructDef _ fldDefs _ <- lookupStruct s
    -- We must be careful to generate initializers in the same order as the
    -- struct's fields are declared, which is why we map 'cgField' over the
    -- struct's field definitions rather than mapping it over the values as
    -- declared in @flds@
    cinits <- mapM (cgField flds) (map fst fldDefs)
    return $ CInit [cinit|{ $inits:cinits }|]
  where
    cgField :: [(Field, Const)] -> Field -> Cg l C.Initializer
    cgField flds f = do
        ce <- case lookup f flds of
                Nothing -> panicdoc $ text "cgField: missing field"
                Just c -> cgConst c
        return $ toInit ce

{- Note [Aliasing]

In general, when compiling @e1 := e2@, the translation of @e2@ could be a
variable bound to a value that aliases the compiled version of @e1@ because it
could be the case that 'cgExp' did make a copy of @e2@ to produce its
translation. Therefore, we cannot assume that if @e1@ and @e2@ don't aliases,
then their translations won't alias. Consider the following example taken from
test_c_CCA.wpl:

@
(x : struct complex32[3]) <- !ac_corr[1,3];
ac_corr[0, 3] := x
@

In this fragment, the compiler won't actually make a copy of @ac_corr[1,3]@ and
assign it to @x@; instead, the translation of @x@ will simply point to
@ac_corr[1,3]@, so this assignment must be performed with @memmove@ instead of
@memcpy@.

How do we track aliasing like this that occurs in the compiler but not in the
source language? We use the 'CAlias' data constructor. Whenever we create a
translation that can result in aliasing, we potentially tag it with
'CAlias'---we actually use the 'calias' smart constructor.

When can the compiler introduce aliasing that doesn't exist in the source
language? When it elides creating new storage for bindings, so a source language
dereference may actually be a reference to the dereferenced expression.

The two remaining issues we don't yet properly deal with are function arguments
and par computations. The source language requires that function arguments don't
alias and that branches of a par don't share any mutable state. We may be able
to deal with these by modifying the reference flow analysis in
KZC.Analysis.RefFlow.
-}

cgExpOneshot :: IsLabel l => Exp -> Cg l (CExp l)
cgExpOneshot e = do
    tau <- inferExp e
    cgExp e $ oneshot tau return

-- | Compile an 'Exp' and throw away the result while ensuring that any side
-- effects are performed.
cgExpVoid :: IsLabel l => Exp -> Cg l ()
cgExpVoid e = cgExp e $ multishot cgVoid

-- | Return 'True' if the given 'CExp' may have some sort of effect. The only
-- time a 'CExp' can currently have a side effect is when it is a function call.
mayHaveEffect :: CExp l -> Bool
mayHaveEffect (CExp [cexp|$id:_($args:_)|]) = True
mayHaveEffect _                             = False

-- | Throw away a 'CExp' while ensuring that any side effects are performed.
cgVoid :: CExp l -> Cg l ()
cgVoid ce | mayHaveEffect ce = appendStm [cstm|$ce;|]
          | otherwise        = return ()

cgExp :: forall l a . IsLabel l => Exp -> Kont l a -> Cg l a
cgExp e k =
    go e $ mapKont (\f ce -> f (reloc (locOf e) ce)) k
  where
    go :: forall a . Exp -> Kont l a -> Cg l a
    go e@(ConstE c _) k = do
        tau <- inferExp e
        cgConst c >>= cgConstExp tau
      where
        cgConstExp :: Type -> CExp l -> Cg l a
        cgConstExp tau (CInit cinit) = do
            cv :: C.Id <- gensym "__const"
            ctau       <- cgType tau
            appendTopDecl [cdecl|const $ty:ctau $id:cv = $init:cinit;|]
            runKont k $ CExp $ reloc (locOf e) [cexp|$id:cv|]

        cgConstExp _ ce =
            runKont k ce

    go (VarE v _) k =
        lookupVarCExp v >>= runKont k

    go (UnopE op e l) k = do
        tau <- inferExp e
        ce  <- cgExpOneshot e
        cgUnop tau ce op >>= runKont k
      where
        cgUnop :: Type -> CExp l -> Unop -> Cg l (CExp l)
        cgUnop tau_from ce (Cast tau_to) =
            cgCast ce tau_from tau_to

        cgUnop tau_from ce (Bitcast tau_to) =
            cgBitcast ce tau_from tau_to

        cgUnop (ArrT iota _ _) _ Len =
            cgIota iota

        cgUnop _ _ Len =
            panicdoc $
            text "cgUnop: tried to take the length of a non-array type!"

        cgUnop tau ce op | isComplexT tau =
            go op
          where
            go :: Unop -> Cg l (CExp l)
            go Neg = do
                (a, b) <- unComplex ce
                cgComplex (-a) (-b)

            go op =
                panicdoc $ text "Illegal operation on complex values:" <+> ppr op

        cgUnop _   ce Lnot              = return $ CExp [cexp|!$ce|]
        cgUnop tau ce Bnot | isBitT tau = return $ CExp [cexp|!$ce|]
                           | otherwise  = return $ CExp [cexp|~$ce|]
        cgUnop _   ce Neg               = return $ CExp [cexp|-$ce|]

        cgCast :: CExp l -> Type -> Type -> Cg l (CExp l)
        cgCast ce tau_from tau_to | isComplexT tau_from && isComplexT tau_to = do
            (a, b) <- unComplex ce
            ctemp  <- cgTemp "cast_complex" tau_to
            appendStm $ rl l [cstm|$ctemp.re = $a;|]
            appendStm $ rl l [cstm|$ctemp.im = $b;|]
            return ctemp

        cgCast ce _ tau_to | isComplexT tau_to = do
            ctemp <- cgTemp "cast_complex" tau_to
            appendStm $ rl l [cstm|$ctemp.re = $ce;|]
            appendStm $ rl l [cstm|$ctemp.im = $ce;|]
            return ctemp

        cgCast _ tau1@(FixT sc1 _ _ _ _) tau2@(FixT sc2 _ _ _ _) | sc2 /= sc1 =
            faildoc $
            text "Cannot cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2 <+>
            text "since types have different scales."

        cgCast _ tau1@(FixT _ _ _ bp1 _) tau2@(FixT _ _ _ bp2 _) | bp2 /= bp1 =
            faildoc $
            text "Cannot cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2 <+>
            text "since types have different binary points."

        cgCast ce _ tau_to | isBitT tau_to =
            return $ CExp $ rl l [cexp|$ce > 0 ? 1 : 0|]

        cgCast ce _ tau_to = do
            ctau_to <- cgType tau_to
            return $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

        cgBitcast :: CExp l -> Type -> Type -> Cg l (CExp l)
        cgBitcast ce tau_from tau_to | tau_to == tau_from =
            return ce

        cgBitcast ce tau_from tau_to@(FixT I U _ (BP 0) _) | isBitArrT tau_from = do
            cbits   <- cgBits tau_from ce
            ctau_to <- cgType tau_to
            return $ CExp $ rl l [cexp|($ty:ctau_to) $cbits|]

        cgBitcast ce tau_from@(FixT I U _ (BP 0) _) tau_to | isBitArrT tau_to = do
            ctau_to <- cgBitcastType tau_from
            return $ CBits $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

        cgBitcast ce tau_from tau_to = do
            ctau_to <- cgType tau_to
            caddr   <- cgAddrOf tau_from ce
            return $ CExp $ rl l [cexp|*(($ty:ctau_to*) $caddr)|]

    go (BinopE op e1 e2 l) k = do
        tau <- inferExp e1
        ce1 <- cgExpOneshot e1
        ce2 <- cgExpOneshot e2
        cgBinop tau ce1 ce2 op >>= runKont k
      where
        cgBinop :: Type -> CExp l -> CExp l -> Binop -> Cg l (CExp l)
        cgBinop tau ce1 ce2 op | isComplexT tau =
            go op
          where
            go :: Binop -> Cg l (CExp l)
            go Eq = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                return $ CExp $ rl l [cexp|$a == $c && $b == $d|]

            go Ne = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                return $ CExp $ rl l [cexp|$a != $c || $b != $d|]

            go Add = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                cgComplex (a+c) (b+d)

            go Sub = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                cgComplex (a-c) (b-d)

            go Mul = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                cgComplex (a*c - b*d) (b*c + a*d)

            go Div = do
                (a, b) <- unComplex ce1
                (c, d) <- unComplex ce2
                cgComplex ((a*c + b*d)/(c*c + d*d)) ((b*c - a*d)/(c*c + d*d))

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

        cgBinop tau _ _ Cat = do
            (_, tau_elem) <- checkArrT tau
            arrs          <- unfoldCat e
            if isBitT tau_elem
              then cgBitCat arrs
              else cgCat arrs
          where
            -- Split nested applications of (++) into a single list of
            -- concatenated arrays, each paired with the number of elements it
            -- contains.
            unfoldCat :: Exp -> Cg l [(Exp, Int)]
            unfoldCat (BinopE Cat e1 e2 _) =
                (++) <$> unfoldCat e1 <*> unfoldCat e2

            unfoldCat e = do
                (iota, _) <- inferExp e >>= checkArrT
                n         <- cgConstIota iota
                return [(e, fromIntegral n)]

            -- XXX: Need to allocate a single array and fill it using cgSlice
            -- and cgAssign.
            cgCat :: [(Exp, Int)] -> Cg l (CExp l)
            cgCat _ =
                fail "Cannot compile concatenation of not-bit arrays"

            cgBitCat :: [(Exp, Int)] -> Cg l (CExp l)
            cgBitCat arrs = do
                carrs <- mapM asBits arrs
                -- Rearrange the arrays we are concatenating in order from
                -- lowest bits to highest bits
                let carrs' = reverse carrs
                let ces    = shiftFields 0 carrs'
                -- Although it doesn't matter, we reverse ces here so in the
                -- source they appear ordered from highest bits to lowest bits
                return $ CBits $ foldr1 (..|..) $ reverse ces
              where
                shiftFields :: Int -> [(CExp l, Int)] -> [CExp l]
                shiftFields _ []             = []
                shiftFields n ((ce, w):flds) = shiftL ce n : shiftFields (n+w) flds

                asBits :: (Exp, Int) -> Cg l (CExp l, Int)
                asBits (e, w) = do
                    cbits <- cgExpOneshot e >>= cgBits (arrKnownT w bitT)
                    return (CBits $ CExp $ rl (locOf l) cbits, w)

    go (IfE e1 e2 e3 _) k = do
        tau <- inferExp e2
        cgIf tau e1 (cgExp e2) (cgExp e3) k

    go (LetE decl e _) k =
        cgLocalDecl decl $ cgExp e k

    go (CallE f iotas es l) k = do
        FunT ivs _ tau_ret _ <- lookupVar f
        let tau_res          =  resultType tau_ret
        cf                   <- lookupVarCExp f
        ciotas               <- mapM cgIota iotas
        ces                  <- mapM cgArg es
        if isReturnedByRef tau_res
          then extendIVarCExps (ivs `zip` ciotas) $ do
               (cres, k') <- splitMultishotBind "call_res" tau_res True k
               appendStm $ rl l [cstm|$cf($args:ciotas, $args:(ces ++ [cres]));|]
               k'
          else runKont k $ CExp [cexp|$cf($args:ciotas, $args:ces)|]
      where
        cgArg :: Exp -> Cg l (CExp l)
        cgArg e = do
            tau <- inferExp e
            go tau
          where
            go :: Type -> Cg l (CExp l)
            go tau@(ArrT {}) =
                cgExp e $ oneshot tau $ cgAddrOf tau

            go tau | isPassByRef tau =
                cgExp e $ oneshot tau $ cgAddrOf tau

            go _ =
                cgExpOneshot e

    go (DerefE e _) k =
        cgExp e $ mapKont (\f ce -> f (cgDeref ce)) k

    go e@(AssignE e1 e2 _) k = do
        appendComment $ ppr e
        tau <- inferExp e1
        ce1 <- cgExpOneshot e1
        cgExp e2 $ multishotBind tau ce1
        runKont k CVoid

    {- Note [Compiling While Loops]

    The test for a while loop is a pureish ST expression because to do anything
    useful it will need to dereference variables. Compiling this expression therefor
    produces C statement representing side effects. But how can we generate C code
    for a while loop when the test requires executing C statements? One option would
    be to use GCC's statement expressions, but we'd like to stick with standard
    C. Instead, we execute the test's statements twice, once before entering the
    loop, and once at the end of the body of the loop. This ensures that the
    required side effects are executed before the test expression is evaluated.
    -}

    go (WhileE e_test e_body l) k = do
        (citems_test, ce_test) <- inNewBlock  $ cgExpOneshot e_test
        citems_body            <- inNewBlock_ $ cgExpOneshot e_body
        appendBlock $ map (rl l) citems_test
        appendStm $ rl l [cstm|while ($ce_test) { $items:citems_body $items:citems_test }|]
        runKont k CVoid

    go (ForE _ v v_tau e_start e_len e_body l) k = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendDecl $ rl l [cdecl|$ty:cv_tau $id:cv;|]
        ce_start <- cgExpOneshot e_start
        ce_len   <- cgExpOneshot e_len
        citems   <- inNewBlock_ $ cgExpVoid e_body
        appendStm $ rl l [cstm|for ($id:cv = $ce_start; $id:cv < $(ce_start + ce_len); $id:cv++) { $items:citems }|]
        runKont k CVoid

    go e@(ArrayE es l) k =
        case unConstE e of
          Nothing -> cgArrayExp
          Just c  -> cgExp (ConstE c l) k
      where
        cgArrayExp :: Cg l a
        cgArrayExp = do
            (_, tau)   <- inferExp e >>= checkArrT
            cv :: C.Id <- gensym "__arr"
            ctau       <- cgType tau
            appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv[$int:(length es)];|]
            forM_ (es `zip` [(0::Integer)..]) $ \(e,i) -> do
                ce <- cgExpOneshot e
                cgAssign (refT tau) (CIdx tau (CExp [cexp|$id:cv|]) (fromIntegral i)) ce
            runKont k $ CExp [cexp|$id:cv|]

    go (IdxE e1 e2 maybe_len _) k = do
        (iota, tau) <- inferExp e1 >>= checkArrOrRefArrT
        cn          <- cgIota iota
        ce1         <- cgExpOneshot e1
        ce2         <- cgExpOneshot e2
        case maybe_len of
          Nothing  -> calias e <$> cgIdx tau ce1 cn ce2 >>= runKont k
          Just len -> calias e <$> cgSlice tau ce1 cn ce2 len >>= runKont k

    go e@(StructE _ flds l) k = do
        case unConstE e of
          Nothing -> CStruct <$> mapM cgField flds >>= runKont k
          Just c  -> cgExp (ConstE c l) k
      where
        cgField :: (Field, Exp) -> Cg l (Field, CExp l)
        cgField (fld, e) = do
            ce <- cgExpOneshot e
            return (fld, ce)

    go e@(ProjE e1 fld l) k = do
        ce1  <- cgExpOneshot e1
        ce1' <- rl l <$> cgProj ce1 fld
        runKont k $ calias e ce1'

    go (PrintE nl es l) k = do
        mapM_ cgPrint es
        when nl $
            appendStm $ rl l [cstm|printf("\n");|]
        runKont k CVoid
      where
        cgPrint :: Exp -> Cg l ()
        cgPrint e = do
            tau <- inferExp e
            ce  <- cgExpOneshot e
            cgPrintScalar tau ce

        cgPrintScalar :: Type -> CExp l -> Cg l ()
        cgPrintScalar (UnitT {})            _  = appendStm $ rl l [cstm|printf("()");|]
        cgPrintScalar (BoolT {})            ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "true" : "false");|]
        cgPrintScalar (FixT I U (W 1)  0 _) ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "'1" : "'0");|]
        cgPrintScalar (FixT I S (W 64) 0 _) ce = appendStm $ rl l [cstm|printf("%lld", (long long) $ce);|]
        cgPrintScalar (FixT I U (W 64) 0 _) ce = appendStm $ rl l [cstm|printf("%llu", (unsigned long long) $ce);|]
        cgPrintScalar (FixT I S _ 0 _)      ce = appendStm $ rl l [cstm|printf("%ld", (long) $ce);|]
        cgPrintScalar (FixT I U _ 0 _)      ce = appendStm $ rl l [cstm|printf("%lu", (unsigned long) $ce);|]
        cgPrintScalar tau@(FixT {})         _  = faildoc $ text "Cannot print value of type" <+> ppr tau
        cgPrintScalar (FloatT {})           ce = appendStm $ rl l [cstm|printf("%f",  (double) $ce);|]
        cgPrintScalar (StringT {})          ce = appendStm $ rl l [cstm|printf("%s",  $ce);|]
        cgPrintScalar (ArrT iota tau _)     ce = cgPrintArray iota tau ce

        cgPrintScalar (StructT s _) ce | isComplexStruct s =
            appendStm $ rl l [cstm|printf("(%ld,%ld)", (long) $ce.re, (long) $ce.im);|]

        cgPrintScalar tau _ =
            faildoc $ text "Cannot print type:" <+> ppr tau

        cgPrintArray :: Iota -> Type -> CExp l -> Cg l ()
        cgPrintArray iota tau ce | isBitT tau = do
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

    go (ErrorE _ s l) k = do
        appendStm $ rl l [cstm|kz_error($string:s);|]
        runKont k CVoid

    go (ReturnE _ e _) k =
        cgExp e k

    go (BindE WildV tau e1 e2 _) k = do
        cgExp e1 $ oneshot tau $ \ce -> do
        cgVoid ce
        cgExp e2 k

    go (BindE (TameV v) tau e1 e2 _) k =
        cgExp e1 $ cgMonadicBinding v tau $ \cv ->
          extendVars [(bVar v, tau)] $
          extendVarCExps [(bVar v, cv)] $
          cgExp e2 k

    go (LutE e) k =
        cgExp e k

cgIVar :: IVar -> Cg l (CExp l, C.Param)
cgIVar iv = do
    civ <- cvar iv
    return (CExp [cexp|$id:civ|], [cparam|int $id:civ|])

-- | Compile a function variable binding. When the variable is a ref type, it is
-- represented as a pointer, so we use the 'CPtr' constructor to ensure that
-- dereferencing occurs.
cgVarBind :: (Var, Type) -> Cg l (CExp l, C.Param)
cgVarBind (v, tau) = do
    cv     <- cvar v
    cparam <- cgParam tau (Just cv)
    if isPassByRef tau
      then return (CPtr (CExp $ rl l [cexp|$id:cv|]), cparam)
      else return (CExp $ rl l [cexp|$id:cv|], cparam)
  where
    l :: Loc
    l = locOf v <--> locOf tau

cgIota :: Iota -> Cg l (CExp l)
cgIota (ConstI i _) = return $ CInt (fromIntegral i)
cgIota (VarI iv _)  = lookupIVarCExp iv

-- | Compile an 'Iota' to an 'Integer' constant. If the argument cannot be
-- resolved to a constant, raise an exception.
cgConstIota :: Iota -> Cg l Integer
cgConstIota iota = do
    ciota <- cgIota iota
    case ciota of
      CInt n -> return n
      _      -> faildoc $ text "Non-polymorphic array required"

-- | Compile real and imaginary parts into a complex number
cgComplex :: CExp l -> CExp l -> Cg l (CExp l)
cgComplex cre cim =
    return $ CStruct [("re", cre), ("im", cim)]

-- | Destruct a 'CExp' representing a complex number into its constituent real
-- and imaginary parts.
unComplex :: CExp l -> Cg l (CExp l, CExp l)
unComplex ce = (,) <$> cgProj ce "re" <*> cgProj ce "im"

-- | Check that the argument is either an array or a reference to an array and
-- return the array's size and the type of its elements.
checkArrOrRefArrT :: Monad m => Type -> m (Iota, Type)
checkArrOrRefArrT (ArrT iota tau _)          = return (iota, tau)
checkArrOrRefArrT (RefT (ArrT iota tau _) _) = return (iota, tau)
checkArrOrRefArrT tau =
    faildoc $ nest 2 $ group $
    text "Expected array type but got:" <+/> ppr tau

unCComp :: CExp l -> Cg l (CompC l a)
unCComp (CComp compc) =
    return compc

unCComp ce =
    panicdoc $ nest 2 $ text "unCComp: not a CComp:" </> ppr ce

unCFunComp :: CExp l -> Cg l (FunCompC l a)
unCFunComp (CFunComp funcompc) =
    return funcompc

unCFunComp ce =
    panicdoc $ nest 2 $ text "unCFunComp: not a CFunComp:" </> ppr ce

-- | Compile a 'CExp' into a 'C.Exp' that is its bit representation as a
-- numerical value. The result is an appropriate argument for the 'CBits' data
-- constructor.
cgBits :: Type
       -> CExp l
       -> Cg l C.Exp
cgBits _ (CBits ce) =
    return [cexp|$ce|]

--- XXX: If ce happens to be a slice that starts at an index that is not a
--- multiple of 'bIT_ARRAY_ELEM_BITS', then it will end up being copied into a
--- temporary by 'cgAddrOf'. We should instead do our own shift and mask.
cgBits tau@(ArrT iota _ _) ce | isBitArrT tau = do
    ctau  <- cgBitcastType tau
    caddr <- cgAddrOf tau ce
    w     <- cgConstIota iota
    if cgWidthMatchesBitcastTypeWidth w
      then return [cexp|*(($ty:ctau*) $caddr)|]
      else return [cexp|*(($ty:ctau*) $caddr) & $(chexconst (2^w - 1))|]

cgBits tau@(FixT {}) ce = do
    ctau <- cgBitcastType tau
    return [cexp|($ty:ctau) $ce|]

cgBits tau ce = do
    ctau  <- cgBitcastType tau
    caddr <- cgAddrOf tau ce
    return [cexp|*(($ty:ctau*) $caddr)|]

-- | Return the C type appropriate for bit casting a value of the given type.
cgBitcastType :: Type -> Cg l C.Type
cgBitcastType tau = do
    w <- typeSize tau
    case w of
      _ | w <= 8  -> return [cty|typename uint8_t|]
      _ | w <= 16 -> return [cty|typename uint16_t|]
      _ | w <= 32 -> return [cty|typename uint32_t|]
      _ | w <= 64 -> return [cty|typename uint64_t|]
      _ ->
        faildoc $ text "Cannot compile bitcast type for" <+> ppr tau <+> "(width >64)."

-- | Return if the given width is the same as the width of the type returned by
-- 'cgBitcastType'.
cgWidthMatchesBitcastTypeWidth :: (Eq a, Num a) => a -> Bool
cgWidthMatchesBitcastTypeWidth 8  = True
cgWidthMatchesBitcastTypeWidth 16 = True
cgWidthMatchesBitcastTypeWidth 32 = True
cgWidthMatchesBitcastTypeWidth 64 = True
cgWidthMatchesBitcastTypeWidth _  = False

-- | Compile a type to its C representation.
cgType :: Type -> Cg l C.Type
cgType (UnitT {}) =
    return [cty|void|]

cgType (BoolT {}) =
    return [cty|typename uint8_t|]

cgType tau | isBitT tau =
    return bIT_ARRAY_ELEM_TYPE

cgType tau@(FixT _ S (W w) _ _)
    | w <= 8    = return [cty|typename int8_t|]
    | w <= 16   = return [cty|typename int16_t|]
    | w <= 32   = return [cty|typename int32_t|]
    | w <= 64   = return [cty|typename int64_t|]
    | otherwise = faildoc $ text "Cannot compile fixed type" <+> ppr tau <+> "(width >64)."

cgType tau@(FixT _ U (W w) _ _)
    | w <= 8    = return [cty|typename uint8_t|]
    | w <= 16   = return [cty|typename uint16_t|]
    | w <= 32   = return [cty|typename uint32_t|]
    | w <= 64   = return [cty|typename uint64_t|]
    | otherwise = faildoc $ text "Cannot compile fixed type" <+> ppr tau <+> "(width >64)."

cgType (FloatT FP16 _) =
    return [cty|float|]

cgType (FloatT FP32 _) =
    return [cty|float|]

cgType (FloatT FP64 _) =
    return [cty|double|]

cgType (StringT {}) =
    return [cty|char*|]

cgType (StructT s l) =
    return [cty|typename $id:(cstruct s l)|]

cgType (ArrT (ConstI n _) tau _) | isBitT tau =
    return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$int:(bitArrayLen n)]|]

cgType (ArrT (ConstI n _) tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau[$int:n]|]

cgType tau@(ArrT (VarI {}) _ _) =
    panicdoc $ text "cgType: cannot translate array of unknown size:" <+> ppr tau

cgType tau@(ST _ (C tau') _ _ _ _) | isPureishT tau =
    cgType tau'

cgType tau@(ST {}) =
    panicdoc $ text "cgType: cannot translate ST types:" <+> ppr tau

cgType (RefT (ArrT (ConstI n _) tau _) _) | isBitT tau = do
    return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$int:(bitArrayLen n)]|]

cgType (RefT (ArrT (ConstI n _) tau _) _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau[$int:n]|]

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

{- Note [Type Qualifiers for Array Arguments]

We use the restrict and static type qualifiers to declare that the arrays have
at least a certain size and that there is no aliasing between pointers.

See:
  http://stackoverflow.com/questions/3430315/purpose-of-static-keyword-in-array-parameter-of-function
-}

-- | Compile a function parameter.
cgParam :: Type -> Maybe C.Id -> Cg l C.Param
cgParam tau maybe_cv = do
    ctau <- cgParamType tau
    case maybe_cv of
      Nothing -> return [cparam|$ty:ctau|]
      Just cv -> return [cparam|$ty:ctau $id:cv|]
  where
    cgParamType :: Type -> Cg l C.Type
    cgParamType (ArrT (ConstI n _) tau _) | isBitT tau =
        return [cty|const $ty:bIT_ARRAY_ELEM_TYPE[$tyqual:restrict $tyqual:static $int:(bitArrayLen n)]|]

    cgParamType (ArrT (ConstI n _) tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau[$int:n]|]

    cgParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau* $tyqual:restrict|]

    cgParamType (RefT (ArrT (ConstI n _) tau _) _) | isBitT tau = do
        return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$tyqual:restrict $tyqual:static $int:(bitArrayLen n)]|]

    cgParamType (RefT (ArrT (ConstI n _) tau _) _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau[$tyqual:restrict $tyqual:static $int:n]|]

    cgParamType (RefT (ArrT _ tau _) _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau* $tyqual:restrict|]

    cgParamType (RefT tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau* $tyqual:restrict|]

    cgParamType tau = cgType tau

-- | Compile a function parameter that is used to return a result.
cgRetParam :: Type -> Maybe C.Id -> Cg l C.Param
cgRetParam tau maybe_cv = do
    ctau <- cgRetParamType tau
    case maybe_cv of
      Nothing -> return [cparam|$ty:ctau|]
      Just cv -> return [cparam|$ty:ctau $id:cv|]
  where
    cgRetParamType :: Type -> Cg l C.Type
    cgRetParamType (ArrT (ConstI n _) tau _) | isBitT tau =
        return [cty|$ty:bIT_ARRAY_ELEM_TYPE[$tyqual:restrict $tyqual:static $int:(bitArrayLen n)]|]

    cgRetParamType (ArrT (ConstI n _) tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau[$tyqual:restrict $tyqual:static $int:n]|]

    cgRetParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau* $tyqual:restrict|]

    cgRetParamType tau = cgType tau

-- | Generate code to bind a variable to a value in a let binding.
cgLetBinding :: forall l a . BoundVar -- ^ The binder
             -> Type                  -- ^ The type of the binder
             -> (CExp l -> Cg l a)    -- ^ Our continuation
             -> Kont l a              -- ^ The continuation that receives the binding.
cgLetBinding bv tau k =
    oneshotBinder bv tau $ oneshotk id
  where
    oneshotk :: (CExp l -> CExp l) -> CExp l -> Cg l a
    oneshotk f ce@CVoid =
        k (f ce)

    oneshotk f ce@(CBool {}) =
        k (f ce)

    oneshotk f ce@(CInt {}) =
        k (f ce)

    oneshotk f ce@(CFloat {}) =
        k (f ce)

    oneshotk _ (CComp {}) =
        panicdoc $ text "cgLetBinding: cannot bind a computation."

    oneshotk _ (CFunComp {}) =
        panicdoc $ text "cgLetBinding: cannot bind a computation function."

    -- Otherwise we have to remember the alias.
    oneshotk  f (CAlias e ce) =
        oneshotk (f . calias e) ce

    oneshotk f ce = do
        cv <- cgBinder (bVar bv) tau
        cgAssign tau cv ce
        k (f cv)

-- | Generate code to bind a variable to a value in a let ref binding. If an
-- initial value is not provided, the variable is bound to the default value for
-- its type.
cgLetRefBinding :: forall l a . IsLabel l
                => BoundVar           -- ^ The binder
                -> Type               -- ^ The type of the binder
                -> Maybe Exp          -- ^ The expression possibly being bound
                -> (CExp l -> Cg l a) -- ^ Our continuation
                -> Cg l a
cgLetRefBinding bv tau Nothing k = do
    cv <- cgBinder (bVar bv) tau
    init cv tau
    k cv
  where
    init :: CExp l -> Type -> Cg l ()
    init cv (BoolT {})  = cgAssign tau cv (CExp [cexp|0|])
    init cv (FixT {})   = cgAssign tau cv (CExp [cexp|0|])
    init cv (FloatT {}) = cgAssign tau cv (CExp [cexp|0.0|])

    init cv (ArrT iota tau _) | isBitT tau = do
        cn <- cgIota iota
        appendStm [cstm|memset($cv, 0, $(bitArrayLen cn)*sizeof($ty:ctau));|]
      where
        ctau :: C.Type
        ctau = bIT_ARRAY_ELEM_TYPE

    init cv (ArrT iota tau _) = do
        cn    <- cgIota iota
        ctau  <- cgType tau
        appendStm [cstm|memset($cv, 0, $cn*sizeof($ty:ctau));|]

    init cv tau = do
        ctau  <- cgType tau
        caddr <- cgAddrOf tau cv
        appendStm [cstm|memset($caddr, 0, sizeof($ty:ctau));|]

cgLetRefBinding bv tau (Just e) k = do
    cve <- cgBinder (bVar bv) tau
    inLocalScope $ cgExp e $ multishotBind tau cve
    k cve

-- | Generate code to bind a variable to a value in a monadic binding. We do a
-- little abstract interpretation here as usual to avoid, e.g., creating a new
-- variable whose value is the value of another variable or a constant. If the
-- binding has refs flow to it that are modified before some use of the
-- variable, a condition we check by calling 'askRefFlowModVar', we create a
-- binding no matter what.
cgMonadicBinding :: forall l a . BoundVar -- ^ The binder
                 -> Type                  -- ^ The type of the binder
                 -> (CExp l -> Cg l a)    -- ^ Our continuation
                 -> Kont l a              -- ^ The continuation that receives the binding.
cgMonadicBinding bv tau k =
    oneshotBinder bv tau $ oneshotk id
  where
    oneshotk :: (CExp l -> CExp l) -> CExp l -> Cg l a
    oneshotk f ce@CVoid =
        k (f ce)

    oneshotk f ce@(CBool {}) =
        k (f ce)

    oneshotk f ce@(CInt {}) =
        k (f ce)

    oneshotk f ce@(CFloat {}) =
        k (f ce)

    oneshotk _ (CComp {}) =
        panicdoc $ text "cgMonadicBinding: cannot bind a computation."

    oneshotk _ (CFunComp {}) =
        panicdoc $ text "cgMonadicBinding: cannot bind a computation function."

    -- If the binder is tainted, then we will create a new binding, so we can
    -- forget the alias.
    oneshotk f (CAlias _ ce) | isTainted bv =
        oneshotk f ce

    -- Otherwise we have to remember the alias.
    oneshotk f (CAlias e ce) =
        oneshotk (f . calias e) ce

    -- Right now we bind values when they are derived from a reference that
    -- may be modified before the derived value is used or when the value
    -- may have a side-effect, e.g., it is the result of a function
    -- call. Perhaps we should be more aggressive about binding
    -- computationally expensive values here?
    oneshotk f ce | isTainted bv || mayHaveEffect ce = do
        cv <- cgBinder (bVar bv) tau
        cgAssign tau cv ce
        k (f cv)

    oneshotk f ce =
        k (f ce)

isTainted :: BoundVar -> Bool
isTainted BoundV{ bTainted = Nothing }    = True
isTainted BoundV{ bTainted = Just taint } = taint

-- | Declare C storage for the given variable. If we are in top scope, declare
-- the storage at top level; otherwise, declare it at thread scope.
cgBinder :: Var -> Type -> Cg l (CExp l)
cgBinder _ (UnitT {}) =
    return CVoid

cgBinder v tau@(ST _ (C tau') _ _ _ _) | isPureishT tau = do
    cgBinder v tau'

cgBinder v tau = do
    isTop       <- isInTopScope
    cv          <- cvar v
    (cdecl, ce) <- cgStorage cv tau
    if isTop
      then appendTopDecl cdecl
      else appendThreadDecl cdecl
    return ce

-- | Allocate storage for a temporary of the given core type. The name of the
-- temporary is gensym'd using @s@ with a prefix of @__@.
cgTemp :: String -> Type -> Cg l (CExp l)
cgTemp _ (UnitT {}) =
    return CVoid

cgTemp s tau = do
    cv          <- gensym ("__" ++ s)
    (cdecl, ce) <- cgStorage cv tau
    appendThreadDecl cdecl
    return ce

-- | Allocate storage for a C identifier with the given core type. The first
-- argument is a boolean flag that is 'True' if this binding corresponds to a
-- top-level core binding and 'False' otherwise.
cgStorage :: C.Id -> Type -> Cg l (C.InitGroup, CExp l)
cgStorage _ (UnitT {}) =
    faildoc $ "cgStorage: asked to allocate storage for unit type."

cgStorage cv (ArrT iota tau _) | isBitT tau = do
    cn        <- cgIota iota
    let cinit =  case cn of
                   CInt n -> rl cv [cdecl|$ty:ctau $id:cv[$int:(bitArrayLen n)];|]
                   _      -> rl cv [cdecl|$ty:ctau* $id:cv = ($ty:ctau*) alloca($(bitArrayLen cn) * sizeof($ty:ctau));|]
    return (cinit, CExp $ rl cv [cexp|$id:cv|])
  where
    ctau :: C.Type
    ctau = bIT_ARRAY_ELEM_TYPE

cgStorage cv (ArrT iota tau _) = do
    ctau      <- cgType tau
    cn        <- cgIota iota
    let cinit =  case cn of
                   CInt n -> rl cv [cdecl|$ty:ctau $id:cv[$int:n];|]
                   _      -> rl cv [cdecl|$ty:ctau* $id:cv = ($ty:ctau*) alloca($cn * sizeof($ty:ctau));|]
    return (cinit, CExp $ rl cv [cexp|$id:cv|])

cgStorage cv tau@(RefT {}) = do
    ctau      <- cgType tau
    let cinit =  rl cv [cdecl|$ty:ctau $id:cv;|]
    return (cinit, CPtr $ CExp $ rl cv [cexp|$id:cv|])

cgStorage cv tau = do
    ctau      <- cgType tau
    let cinit =  rl cv [cdecl|$ty:ctau $id:cv;|]
    return (cinit, CExp $ rl cv [cexp|$id:cv|])

-- | Generate code for a C temporary with a gensym'd name, based on @s@ and
-- prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgCTemp :: Located a => a -> String -> C.Type -> Maybe C.Initializer -> Cg l (CExp l)
cgCTemp l s ctau maybe_cinit = do
    cv :: C.Id <- gensym ("__" ++ s)
    case maybe_cinit of
      Nothing    -> appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp $ rl l [cexp|$id:cv|]

-- | Generate code for a top-level C temporary with a gensym'd name, based on @s@
-- and prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgTopCTemp :: Located a => a -> String -> C.Type -> Maybe C.Initializer -> Cg l (CExp l)
cgTopCTemp l s ctau maybe_cinit = do
    cv :: C.Id <- gensym ("__" ++ s)
    case maybe_cinit of
      Nothing    -> appendTopDecl $ rl l [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendTopDecl $ rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp $ rl l [cexp|$id:cv|]

-- | Generate an empty label statement if the label argument is required.
cgLabel :: IsLabel l => l -> Cg l ()
cgLabel lbl = do
    required <- isLabelUsed lbl
    when required $
        cgWithLabel lbl $
        appendStm [cstm|;|]

-- | Label the statements generated by the continuation @k@ with the specified
-- label. We only generate a C label when the label is actually used, as
-- determined by @isLabelUsed@.
cgWithLabel :: IsLabel l => l -> Cg l a -> Cg l a
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
    lblMacro :: C.Id
    lblMacro = C.Id ("LABEL(" ++ ident ++ ")") l

    ident :: String
    l :: SrcLoc
    C.Id ident l = toIdent lbl noLoc

-- | Compile a computation and throw away he result.
cgCompVoid :: IsLabel l
           => TakeK  l -- ^ Code generator for take
           -> EmitK  l -- ^ Code generator for emit
           -> EmitsK l -- ^ Code generator for emits
           -> Comp l   -- ^ Computation to compiled
           -> l        -- ^ Label of our continuation
           -> Cg l ()
cgCompVoid takek emitk emitsk comp klbl =
    cgComp takek emitk emitsk comp klbl $ multishot cgVoid

-- | 'cgComp' compiles a computation and ensures that the continuation label is
-- jumped to. We assume that the continuation labels the code that will be
-- generated immediately after the call to 'cgComp', so if the computation
-- compiles to straight-line code, no @goto@ will be generated.
cgComp :: forall a l . IsLabel l
       => TakeK l  -- ^ Code generator for take
       -> EmitK l  -- ^ Code generator for emit
       -> EmitsK l -- ^ Code generator for emit
       -> Comp l   -- ^ Computation to compiled
       -> l        -- ^ Label of our continuation
       -> Kont l a -- ^ Continuation accepting the compilation result
       -> Cg l a
cgComp takek emitk emitsk comp klbl k =
    cgSteps (unComp comp) k
  where
    cgSteps :: forall a . [Step l] -> Kont l a -> Cg l a
    cgSteps [] _ =
        faildoc $ text "No computational steps to compile!"

    cgSteps [step] k =
        cgStep step klbl k

    cgSteps (LetC l decl _ : steps) k =
        cgWithLabel l $
        cgLocalDecl decl $
        cgSteps steps k

    cgSteps (step : BindC l WildV tau _ : steps) k = do
        cgStep step l $ oneshot tau $ \ce -> do
        cgVoid ce
        cgWithLabel l $ cgSteps steps k

    cgSteps (step : BindC l (TameV v) tau _ : steps) k =
        cgStep step l $
        mapKont cgBind $
        cgMonadicBinding v tau $ \cv ->
          extendVars [(bVar v, tau)] $
          extendVarCExps [(bVar v, cv)] $
          cgSteps steps k
      where
        -- @e@ could be a pureish computation, in which case we need to compile
        -- it here before we call the continuation with the result. See issue
        -- #12.
        cgBind :: forall a . (CExp l -> Cg l a) -> CExp l -> Cg l a
        cgBind k ce =
            cgWithLabel l $
            case ce of
              CComp compc -> compc takek emitk emitsk klbl $ multishot k
              _           -> k ce

    cgSteps (step : steps) k = do
        l   <- stepLabel (head steps)
        tau <- inferStep step
        cgStep step l $ oneshot tau $ \ce -> do
            cgVoid ce
            cgSteps steps k

    cgStep :: forall a . Step l -> l -> Kont l a -> Cg l a
    cgStep (VarC l v _) klbl k =
        cgWithLabel l $ do
        compc <- lookupVarCExp v >>= unCComp
        compc takek emitk emitsk klbl k

    cgStep (CallC l f iotas args _) klbl k = do
        cgWithLabel l $ do
        funcompc <- lookupVarCExp f >>= unCFunComp
        funcompc iotas args takek emitk emitsk klbl k

    cgStep (IfC l e thenk elsek _) klbl k =
        cgWithLabel l $ do
        tau <- inferComp thenk
        cgIf tau
             e
             (cgComp takek emitk emitsk thenk klbl)
             (cgComp takek emitk emitsk elsek klbl) k

    cgStep (LetC {}) _ _k =
        faildoc $ text "Cannot compile let computation step."

    cgStep (WhileC l e_test c_body sloc) _ k = do
        (citems_test, ce_test) <- inNewBlock $ cgExpOneshot e_test
        citems_body            <- inNewBlock_ $ do
                                  l_inner <- gensym "inner_whilek"
                                  cgCompVoid takek emitk emitsk c_body l_inner
                                  cgLabel l_inner
        cgWithLabel l $ do
            appendBlock $ map (rl sloc) citems_test
            appendStm $ rl sloc [cstm|while ($ce_test) { $items:citems_body $items:citems_test }|]
        runKont k CVoid

    cgStep (ForC l _ v v_tau e_start e_len c_body sloc) _ k = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendThreadDecl $ rl sloc [cdecl|$ty:cv_tau $id:cv;|]
        ce_start <- cgExpOneshot e_start
        ce_len   <- cgExpOneshot e_len
        citems   <- inNewBlock_ $ do
                    l_inner <- gensym "inner_fork"
                    cgCompVoid takek emitk emitsk c_body l_inner
                    cgLabel l_inner
        cgWithLabel l $
            appendStm $ rl sloc [cstm|for ($id:cv = $ce_start; $id:cv < $(ce_start + ce_len); $id:cv++) { $items:citems }|]
        runKont k CVoid

    cgStep (LiftC l e _) _ k =
        cgWithLabel l $
        cgExp e k

    -- A 'ReturnC' is a pure value, so we do not need to lower it.
    cgStep (ReturnC l e _) _ k =
        cgWithLabel l $
        cgExp e k

    cgStep (BindC {}) _ _k =
        faildoc $ text "Cannot compile bind computation step."

    cgStep (TakeC l tau _) klbl k =
        cgWithLabel l $
        takek 1 tau klbl >>= runKont k

    cgStep (TakesC l n tau _) klbl k =
        cgWithLabel l $
        takek n tau klbl >>= runKont k

    cgStep (EmitC l e _) klbl k =
        cgWithLabel l $ do
        tau <- inferExp e
        ce  <- cgExpOneshot e
        emitk tau ce klbl
        runKont k CVoid

    cgStep (EmitsC l e _) klbl k =
        cgWithLabel l $ do
        (iota, tau) <- inferExp e >>= checkArrT
        ce          <- cgExpOneshot e
        emitsk iota tau ce klbl
        runKont k CVoid

    cgStep (RepeatC l _ c_body sloc) _ k = do
        citems <- inNewBlock_ $ do
                  cgCompVoid takek emitk emitsk c_body l
                  cgLabel l
        appendStm $ rl sloc [cstm|for (;;) { $items:citems }|]
        runKont k CVoid

    cgStep step@(ParC ann b left right _) _ k =
        withSummaryContext step $ do
        dflags <- askFlags
        cgPar dflags
      where
        cgPar :: Flags -> Cg l a
        cgPar dflags
            | testDynFlag Fuse dflags = fuse dflags
            | otherwise               = dontFuse dflags ann

        fuse :: Flags -> Cg l a
        fuse dflags = do
            do (s, a, c) <- askSTIndTypes
               tau       <- inferStep step
               comp      <- fusePar s a b c left right
               useLabels (compUsedLabels comp)
               checkComp comp tau
               cgComp takek emitk emitsk comp klbl k
          `mplus`
            do traceFusion $ text "Failed to fuse" <+>
                   (nest 2 $ text "producer:" </> ppr left) </>
                   (nest 2 $ text "and consumer:" </> ppr right)
               dontFuse dflags ann

        dontFuse :: Flags -> PipelineAnn -> Cg l a
        dontFuse dflags ann = do
           tau_res <- resultType <$> inferStep step
           case ann of
             AlwaysPipeline | testDynFlag Pipeline dflags ->
                 cgParMultiThreaded  takek emitk emitsk tau_res b left right klbl k
             _ ->
                 cgParSingleThreaded takek emitk emitsk tau_res b left right klbl k

    cgStep (LoopC {}) _ _k =
        faildoc $ text "cgStep: saw LoopC"

-- | Compile a par, i.e., a producer/consumer pair, using the simple
-- single-threaded strategy. The take and emit code generators should generate
-- code for the par's take and emit.
cgParSingleThreaded :: forall a l . IsLabel l
                    => TakeK  l -- ^ Code generator for /producer's/ take
                    -> EmitK  l -- ^ Code generator for /consumer's/ emit
                    -> EmitsK l -- ^ Code generator for /consumer's/ emit
                    -> Type     -- ^ The type of the result of the par
                    -> Type     -- ^ The type of the par's internal buffer
                    -> Comp l   -- ^ The producer computation
                    -> Comp l   -- ^ The consumer computation
                    -> l        -- ^ The computation's continuation
                    -> Kont l a -- ^ Continuation accepting the compilation result
                    -> Cg l a
cgParSingleThreaded takek emitk emitsk tau_res b left right klbl k = do
    (s, a, c) <- askSTIndTypes
    -- Generate a temporary to hold the result of the par construct.
    cres <- cgTemp "par_res" tau_res
    -- Create the computation that follows the par.
    l_pardone <- gensym "par_done"
    useLabel l_pardone
    -- donek will generate code to store the result of the par and jump to
    -- the continuation.
    let donek :: Kont l ()
        donek = multishot $ \ce -> do
                cgAssign tau_res cres ce
                appendStm [cstm|JUMP($id:l_pardone);|]
    -- Generate variables to hold the left and right computations'
    -- continuations.
    leftl   <- compLabel left
    useLabel leftl
    rightl  <- compLabel right
    useLabel rightl
    cleftk  <- cgCTemp b "par_leftk"  [cty|typename KONT|] (Just [cinit|LABELADDR($id:leftl)|])
    crightk <- cgCTemp b "par_rightk" [cty|typename KONT|] (Just [cinit|LABELADDR($id:rightl)|])
    -- Generate a pointer to the current element in the buffer.
    ctau    <- cgType b
    ctauptr <- cgBufPtrType b
    cbuf    <- cgCTemp b "par_buf"  ctau    Nothing
    cbufp   <- cgCTemp b "par_bufp" ctauptr Nothing
    -- Generate code for the left and right computations.
    localSTIndTypes (Just (b, b, c)) $
        cgComp (takek' cleftk crightk cbuf cbufp) emitk emitsk right klbl donek
    localSTIndTypes (Just (s, a, b)) $
        cgComp takek (emitk' cleftk crightk cbuf cbufp) (emitsk' cleftk crightk cbuf cbufp) left klbl donek
    cgWithLabel l_pardone $
        runKont k cres
  where
    cgBufPtrType :: Type -> Cg l C.Type
    cgBufPtrType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgBufPtrType tau = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgDerefBufPtr :: Type -> CExp l -> CExp l
    cgDerefBufPtr (ArrT {}) ce = ce
    cgDerefBufPtr _         ce = CExp [cexp|*$ce|]

    takek' :: CExp l -> CExp l -> CExp l -> CExp l -> TakeK l
    -- The one element take is easy. We know the element will be in @cbufp@,
    -- so we call @k1@ with @cbufp@ as the argument, which generates a
    -- 'CComp', @ccomp@ that represents the continuation that consumes the
    -- taken value. We then set the right computation's continuation to the
    -- label of @ccomp@, since it is the continuation, generate code to jump
    -- to the left computation's continuation, and then call @k2@ with
    -- @ccomp@ suitably modified to have a required label.
    takek' cleftk crightk _cbuf cbufp 1 _tau k = do
        useLabel k
        appendStm [cstm|$crightk = LABELADDR($id:k);|]
        appendStm [cstm|INDJUMP($cleftk);|]
        return $ cgDerefBufPtr b cbufp

    -- The multi-element take is a bit tricker. We allocate a buffer to hold
    -- all the elements, and then loop, jumping to the left computation's
    -- continuation repeatedly, until the buffer is full. Then we fall
    -- through to the next action, which is why we call @k2@ with @ccomp@
    -- without forcing its label to be required---we don't need the label!
    takek' cleftk crightk _cbuf cbufp n tau _k = do
        ctau_arr <- cgType (ArrT (ConstI n noLoc) tau noLoc)
        carr     <- cgCTemp tau "par_takes_xs" [cty|$ty:ctau_arr|] Nothing
        klbl     <- gensym "inner_takesk"
        useLabel klbl
        appendStm [cstm|$crightk = LABELADDR($id:klbl);|]
        cgFor 0 (fromIntegral n) $ \ci -> do
            appendStm [cstm|INDJUMP($cleftk);|]
            cgWithLabel klbl $
                cgAssign (refT tau) (CIdx tau carr ci) (cgDerefBufPtr b cbufp)
        return carr

    emitk' :: CExp l -> CExp l -> CExp l -> CExp l -> EmitK l
    -- @tau@ must be a base (scalar) type
    emitk' cleftk crightk cbuf cbufp tau ce k = do
        useLabel k
        appendStm [cstm|$cleftk = LABELADDR($id:k);|]
        cgAssignBufp tau cbuf cbufp ce
        appendStm [cstm|INDJUMP($crightk);|]

    emitsk' :: CExp l -> CExp l -> CExp l -> CExp l -> EmitsK l
    emitsk' cleftk crightk cbuf cbufp (ConstI 1 _) tau ce k = do
        ce' <- cgIdx tau ce 1 0
        emitk' cleftk crightk cbuf cbufp tau ce' k

    emitsk' cleftk crightk cbuf cbufp iota tau ce _k = do
        cn    <- cgIota iota
        loopl <- gensym "emitsk_next"
        useLabel loopl
        appendStm [cstm|$cleftk = LABELADDR($id:loopl);|]
        cgFor 0 cn $ \ci -> do
            cidx <- cgIdx tau ce cn ci
            cgAssignBufp tau cbuf cbufp cidx
            appendStm [cstm|INDJUMP($crightk);|]
            -- Because we need a statement to label, but the continuation is
            -- the next loop iteration...
            cgLabel loopl

    -- Assign the value @ce@ to the buffer pointer @cbufp@. If @ce@ is not
    -- an lvalue, then stash it in @cbuf@ first and set @cbufp@ to point to
    -- @cbuf@. This ensures that we can always pass buffer elements by
    -- reference.
    cgAssignBufp :: Type -> CExp l -> CExp l -> CExp l -> Cg l ()
    cgAssignBufp tau _ cbufp ce | isLvalue ce = do
        caddr <- cgAddrOf tau ce
        appendStm [cstm|$cbufp = $caddr;|]

    cgAssignBufp tau cbuf cbufp ce = do
        cgAssign tau cbuf ce
        appendStm [cstm|$cbufp = &$cbuf;|]

-- | Generate code that exits from a computation that is part of a par.
type ExitK l = Cg l ()

-- | Compile a par, i.e., a producer/consumer pair, using the multi-threaded
-- strategy. The take and emit code generators passed as arguments to
-- 'cgParMultiThreaded' should generate code for the outer take and emit---the
-- inner take and emit is done with a producer-consumer buffer.
cgParMultiThreaded :: forall a l . IsLabel l
                   => TakeK  l -- ^ Code generator for /producer's/ take
                   -> EmitK  l -- ^ Code generator for /consumer's/ emit
                   -> EmitsK l -- ^ Code generator for /consumer's/ emit
                   -> Type     -- ^ The type of the result of the par
                   -> Type     -- ^ The type of the par's internal buffer
                   -> Comp l   -- ^ The producer computation
                   -> Comp l   -- ^ The consumer computation
                   -> l        -- ^ The computation's continuation
                   -> Kont l a -- ^ Continuation accepting the compilation result
                   -> Cg l a
cgParMultiThreaded takek emitk emitsk tau_res b left right klbl k = do
    (s, a, c) <- askSTIndTypes
    -- Generate a temporary to hold the par buffer.
    cb   <- cgType b
    cbuf <- cgTopCTemp b "par_buf" [cty|$ty:cb[KZ_BUFFER_SIZE]|] Nothing
    -- Generate a name for the producer thread function
    cf <- gensym "producer"
    -- Generate a temporary to hold the thread info.
    ctinfo <- cgCTemp b "par_tinfo" [cty|typename kz_tinfo_t|] Nothing
    -- Generate a temporary to hold the thread.
    cthread <- cgCTemp b "par_thread" [cty|typename kz_thread_t|] Nothing
    -- Generate a temporary to hold the result of the par construct.
    cres <- cgTemp "par_res" tau_res
    -- Create a label for the computation that follows the par.
    l_pardone <- gensym "par_done"
    useLabel l_pardone
    -- Re-label the consumer computation. We have to do this because we need to
    -- generate code that initializes the par construct, and this initialization
    -- code needs to have the label of the consumer computation because that is
    -- the label that will be jumped to to run the consumer computation.
    l_consumer  <- compLabel right
    l_consumer' <- gensym "consumer"
    let right'  =  setCompLabel l_consumer' right
    -- Generate to initialize the thread
    when (not (isUnitT tau_res)) $
        appendThreadInitStm [cstm|ctinfo.result = &$cres;|]
    cgInitCheckErr [cexp|kz_thread_init(&$ctinfo, &$cthread, $id:cf)|] "Cannot create thread." right
    -- Generate to start the thread
    cgWithLabel l_consumer $
        cgCheckErr [cexp|kz_thread_post(&$ctinfo)|] "Cannot start thread." right
    -- Generate code for the consumer
    localSTIndTypes (Just (b, b, c)) $
        cgConsumer cthread ctinfo cbuf cres right' l_pardone
    -- Generate code for the producer
    localSTIndTypes (Just (s, a, b)) $
        cgProducer cf cbuf left
    -- Label the end of the computation
    cgWithLabel l_pardone $
        runKont k cres
  where
    cgExitWhenDone :: CExp l -> ExitK l -> Cg l ()
    cgExitWhenDone ctinfo exitk = do
        cblock <- inNewBlock_ exitk
        appendStm [cstm|if ($ctinfo.done) { $items:cblock }|]

    -- | Insert a memory barrier
    cgMemoryBarrier :: Cg l ()
    cgMemoryBarrier =
        appendStm [cstm|kz_memory_barrier();|]

    cgProducer :: C.Id -> CExp l -> Comp l -> Cg l ()
    cgProducer cf cbuf comp = do
        tau <- inferComp comp
        (clabels, cblock) <-
            collectLabels $
            inNewThreadBlock_ $
            cgThread takek' emitk' emitsk' tau comp donek
        cgLabels clabels
        appendTopDef [cedecl|
void* $id:cf(void* _tinfo)
{
    typename kz_tinfo_t* tinfo = (typename kz_tinfo_t*) _tinfo;

    for (;;) {
        kz_check_error(kz_thread_wait(tinfo), $string:(renderLoc comp), "Error waiting for thread to start.");
        {
            $items:cblock
        }
        (*tinfo).done = 1;
    }
    return NULL;
}|]
      where
        ctinfo :: CExp l
        ctinfo = CExp [cexp|*tinfo|]

        -- When the producer takes, we need to make sure that the consumer has
        -- asked for more data than we have given it, so we spin until the
        -- consumer requests data.
        takek' :: TakeK l
        takek' n tau k = do
            cgWaitForConsumerRequest ctinfo exitk
            takek n tau k

        emitk' :: EmitK l
        -- @tau@ must be a base (scalar) type
        emitk' tau ce _k =
            cgProduce ctinfo cbuf exitk tau ce

        emitsk' :: EmitsK l
        -- Right now we just loop and write the elements one by one---it would
        -- be better to write them all at once.
        emitsk' iota tau ce _k = do
            cn <- cgIota iota
            cgFor 0 cn $ \ci -> do
                cidx <- cgIdx tau ce cn ci
                cgProduce ctinfo cbuf exitk tau cidx

        exitk :: Cg l ()
        exitk = appendStm [cstm|BREAK;|]

        donek :: Kont l ()
        donek = multishot $ \ce -> do
            ctau_res <- cgType tau_res
            cgAssign tau_res (CPtr (CExp [cexp|($ty:ctau_res*) $ctinfo.result|])) ce
            cgMemoryBarrier
            appendStm [cstm|$ctinfo.done = 1;|]

        -- | Put a single data element in the buffer.
        cgProduce :: CExp l -> CExp l -> ExitK l -> Type -> CExp l -> Cg l ()
        cgProduce ctinfo cbuf exitk tau ce = do
            cgWaitWhileBufferFull ctinfo exitk
            cgAssign tau (CExp [cexp|$cbuf[$ctinfo.prod_cnt % KZ_BUFFER_SIZE]|]) ce
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.prod_cnt;|]

        -- | Wait until the consumer requests data
        cgWaitForConsumerRequest :: CExp l -> ExitK l -> Cg l ()
        cgWaitForConsumerRequest ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.cons_req - $ctinfo.prod_cnt == 0);|]
            cgExitWhenDone ctinfo exitk

        -- | Wait while the buffer is full
        cgWaitWhileBufferFull :: CExp l -> ExitK l -> Cg l ()
        cgWaitWhileBufferFull ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == KZ_BUFFER_SIZE);|]
            cgExitWhenDone ctinfo exitk

    cgConsumer :: CExp l -> CExp l -> CExp l -> CExp l -> Comp l -> l -> Cg l ()
    cgConsumer cthread ctinfo cbuf cres comp l_pardone = do
        cgComp takek' emitk' emitsk' comp klbl $
            multishotBind tau_res cres
        appendStm [cstm|$ctinfo.done = 1;|]
        appendStm [cstm|kz_check_error(kz_thread_join($cthread, NULL), $string:(renderLoc comp), "Cannot join on thread.");|]
        appendStm [cstm|JUMP($id:l_pardone);|]
      where
        takek' :: TakeK l
        takek' 1 _tau _k = do
            cgRequestData ctinfo 1
            cgConsume ctinfo cbuf exitk return

        takek' n tau _k = do
            ctau  <- cgType tau
            carr  <- cgCTemp tau "par_takes_xs" [cty|$ty:ctau[$int:n]|] Nothing
            cgRequestData ctinfo (fromIntegral n)
            cgFor 0 (fromIntegral n) $ \ci -> do
                cgConsume ctinfo cbuf exitk $ \ce ->
                    appendStm [cstm|$carr[$ci] = $ce;|]
            return carr

        emitk' :: EmitK l
        emitk' = emitk

        emitsk' :: EmitsK l
        emitsk' = emitsk

        exitk :: Cg l ()
        exitk = appendStm [cstm|JUMP($id:l_pardone);|]

        -- | Consumer a single data element from the buffer. We take a consumption
        -- continuation, because we must be sure that we insert a memory barrier
        -- before incrementing the consumer count.
        cgConsume :: forall a . CExp l -> CExp l -> ExitK l -> (CExp l -> Cg l a) -> Cg l a
        cgConsume ctinfo cbuf exitk consumek = do
            cgWaitWhileBufferEmpty ctinfo exitk
            cidx <- cgCTemp right "cons_idx" [cty|int|] Nothing
            appendStm [cstm|$cidx = $ctinfo.cons_cnt % KZ_BUFFER_SIZE;|]
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.cons_cnt;|]
            x <- consumek (CExp [cexp|$cbuf[$cidx]|])
            return x

        -- | Request @cn@ data elements.
        cgRequestData :: CExp l -> CExp l -> Cg l ()
        cgRequestData ctinfo cn =
            appendStm [cstm|$ctinfo.cons_req += $cn;|]

        -- | Wait while the buffer is empty
        cgWaitWhileBufferEmpty :: CExp l -> ExitK l -> Cg l ()
        cgWaitWhileBufferEmpty ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == 0);|]
            cgExitWhenDone ctinfo exitk

-- | Return 'True' if a compiled expression is a C lvalue.
isLvalue :: CExp l -> Bool
isLvalue (CIdx tau _ _) | isBitT tau =
    False

isLvalue (CIdx _ ce _) =
    isLvalue ce

isLvalue ce@(CSlice tau carr _ _) | isBitT tau =
    isLvalue carr && isJust (unBitCSliceBase ce)

isLvalue (CSlice tau _ _ _) | isBitT tau =
    False

isLvalue (CSlice _ carr _ _) =
    isLvalue carr

isLvalue (CExp (C.Var {}))       = True
isLvalue (CExp (C.Member {}))    = True
isLvalue (CExp (C.PtrMember {})) = True
isLvalue (CExp (C.Index {}))     = True
isLvalue (CAlias _ ce)           = isLvalue ce
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
cgAssign :: forall l . Type -> CExp l -> CExp l -> Cg l ()
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

cgAssign tau ce1 ce2 = do
    alias <- mayAlias ce1 ce2
    assign alias tau ce1 ce2
  where
    mayAlias :: CExp l -> CExp l -> Cg l Bool
    mayAlias ce1@(CAlias e1' _) ce2@(CAlias e2' _) = do
        alias <- pathsMayAlias <$> refPath e1' <*> refPath e2'
        traceCg $ nest 2 $
            text "Potentially aliasing assignment" <+> parens (ppr alias) </>
            ppr ce1 <+> text ":=" <+> ppr ce2
        return alias

    mayAlias _ce1 _ce2 =
        return False

    assign :: Bool -> Type -> CExp l -> CExp l -> Cg l ()
    assign mayAlias tau (CAlias _ ce1) ce2 =
       assign mayAlias tau ce1 ce2

    assign mayAlias tau ce1 (CAlias _ ce2) =
       assign mayAlias tau ce1 ce2

    -- XXX: Should use more efficient bit twiddling code here. See:
    --
    --   http://realtimecollisiondetection.net/blog/?p=78
    --   https://graphics.stanford.edu/~seander/bithacks.html
    --   https://stackoverflow.com/questions/18561655/bit-set-clear-in-c
    --
    assign _ (RefT tau _) (CIdx _ carr cidx) ce2 | isBitT tau =
        appendStm [cstm|$carr[$cbitIdx] = ($carr[$cbitIdx] & ~$cmask) | $cbit;|]
      where
        cbitIdx, cbitOff :: CExp l
        (cbitIdx, cbitOff) = cidx `quotRem` bIT_ARRAY_ELEM_BITS

        cmask, cbit :: CExp l
        cmask = 1 `shiftL'` cbitOff
        -- Bits are always masked off, so we we can assume ce2 is either 0 or
        -- 1. If we couldn't make this assumption, we would need to use
        -- [cexp|!!$ce2|] here.
        cbit = ce2 `shiftL'` cbitOff

    assign _ tau0 ce1 ce2 | Just (iota, tau) <- checkArrOrRefArrT tau0, isBitT tau = do
        clen <- cgIota iota
        cgAssignBitArray ce1 ce2 clen
      where
        cgAssignBitArray :: CExp l -> CExp l -> CExp l -> Cg l ()
        cgAssignBitArray ce1 ce2 clen = do
            appendComment $ text "Bit array:" <+> ppr ce1 <+> text ":=" <+> ppr ce2
            case (unBitCSliceBase ce1, unBitCSliceBase ce2, clen) of
              (Just cdst, Just csrc, CInt len) -> fastPath cdst csrc 0 len
              _ -> case (unCSlice ce1, unCSlice ce2, clen) of
                     ((cdst, CInt dstIdx), (csrc, CInt srcIdx), CInt len) ->
                         mediumPath cdst dstIdx csrc srcIdx len
                     ((cdst, cdstIdx), (csrc, csrcIdx), clen) ->
                         slowPath cdst cdstIdx csrc csrcIdx clen
          where
            fastPath :: CExp l -> CExp l -> Integer -> Integer -> Cg l ()
            fastPath _cdst _csrc _i 0 =
                return ()

            -- The following generates code with unaligned accesses, so we can't
            -- use it.

{-
            fastPath cdst csrc i n | q /= 0 = do
                forM_ [0..q - 1] $ \j ->
                    appendStm [cstm|((typename uint64_t*) &$cdst[$int:i])[$int:j] = ((typename uint64_t*) &$csrc[$int:i])[$int:j];|]
                fastPath cdst csrc (i + 8*q) r
              where
                (q, r) = n `quotRem` 64

            fastPath cdst csrc i n | q /= 0 = do
                forM_ [0..q - 1] $ \j ->
                    appendStm [cstm|((typename uint32_t*) &$cdst[$int:i])[$int:j] = ((typename uint32_t*) &$csrc[$int:i])[$int:j];|]
                fastPath cdst csrc (i + 4*q) r
              where
                (q, r) = n `quotRem` 32

            fastPath cdst csrc i n | q /= 0 = do
                forM_ [0..q - 1] $ \j ->
                    appendStm [cstm|((typename uint16_t*) &$cdst[$int:i])[$int:j] = ((typename uint16_t*) &$csrc[$int:i])[$int:j];|]
                fastPath cdst csrc (i + 2*q) r
              where
                (q, r) = n `quotRem` 16
-}

            fastPath cdst csrc i n | q /= 0 = do
                forM_ [0..q - 1] $ \j ->
                    appendStm [cstm|$cdst[$int:(i+j)] = $csrc[$int:(i+j)];|]
                fastPath cdst csrc (i + q) r
              where
                (q, r) = n `quotRem` 8

            fastPath cdst csrc i n | n < 8 =
                maskedAssign (CExp [cexp|$cdst[$int:i]|]) (CExp [cexp|$csrc[$int:i]|]) n

            fastPath _ _ i _ =
                slowPath cdst (cdstIdx + fromIntegral i) csrc (csrcIdx + fromIntegral i) clen
              where
                cdst, cdstIdx :: CExp l
                (cdst, cdstIdx) = unCSlice ce1

                csrc, csrcIdx :: CExp l
                (csrc, csrcIdx) = unCSlice ce2

            mediumPath :: CExp l -> Integer -> CExp l -> Integer -> Integer -> Cg l ()
            mediumPath cdst dstIdx csrc srcIdx len =
                slowPath cdst (CInt dstIdx) csrc (CInt srcIdx) (CInt len)

            maskedAssign :: CExp l -> CExp l -> Integer -> Cg l ()
            maskedAssign cdst csrc n =
                appendStm [cstm|$cdst = $(cdst ..&.. cnotmask ..|.. csrc ..&.. cmask);|]
              where
                cmask, cnotmask :: CExp l
                cmask    = CExp $ chexconst (2^n - 1)
                cnotmask = CExp $ [cexp|~$(chexconst (2^n - 1))|]

            slowPath :: CExp l -> CExp l -> CExp l -> CExp l -> CExp l -> Cg l ()
            slowPath cdst cdstIdx csrc csrcIdx clen = do
                csrc' <- cgLower tau0 csrc
                incBitArrayCopies
                appendStm [cstm|kz_bitarray_copy($cdst, $cdstIdx, $csrc', $csrcIdx, $clen);|]

    assign mayAlias tau0 ce1 ce2 | Just (iota, tau) <- checkArrOrRefArrT tau0 = do
        ctau <- cgType tau
        ce1' <- cgArrayAddr ce1
        ce2' <- cgArrayAddr ce2
        clen <- cgIota iota
        incMemCopies
        if mayAlias
          then appendStm [cstm|memmove($ce1', $ce2', $clen*sizeof($ty:ctau));|]
          else appendStm [cstm|memcpy($ce1', $ce2', $clen*sizeof($ty:ctau));|]
      where
        cgArrayAddr :: CExp l -> Cg l (CExp l)
        cgArrayAddr (CSlice tau _ _ _) | isBitT tau =
            panicdoc $ text "cgArrayAddr: the impossible happened!"

        cgArrayAddr (CSlice _ carr cidx _) =
            return $ CExp [cexp|&$carr[$cidx]|]

        cgArrayAddr (CAlias e ce) =
            calias e <$> cgArrayAddr ce

        cgArrayAddr ce =
            return ce

    assign _ _ cv (CStruct flds) =
        mapM_ cgAssignField flds
      where
        cgAssignField :: (Field, CExp l) -> Cg l ()
        cgAssignField (fld, ce) =
            appendStm [cstm|$cv.$id:cfld = $ce;|]
          where
            cfld :: String
            cfld = zencode (namedString fld)

    -- We call 'cgDeref' on @cv@ because the lhs of an assignment is a ref type and
    -- may need to be dereferenced.
    assign _ _ cv ce =
        appendStm [cstm|$(cgDeref cv) = $ce;|]

cgBoundsCheck :: CExp l -> CExp l -> Cg l ()
cgBoundsCheck clen cidx = do
    boundsCheck <- asksFlags (testDynFlag BoundsCheck)
    when boundsCheck $ do
        appendStm [cstm|kz_assert($cidx >= 0 && $cidx < $clen, $string:(renderLoc cidx), "Array index %d out of bounds (%d)", $cidx, $clen);|]

-- | Generate a 'CExp' representing an index into an array.
cgIdx :: Type          -- ^ Type of the array element
      -> CExp l        -- ^ The array
      -> CExp l        -- ^ The length of the array
      -> CExp l        -- ^ The array index
      -> Cg l (CExp l) -- ^ The indexed element
cgIdx tau (CSlice _ carr cidx1 _) clen cidx2 = do
    cgBoundsCheck clen cidx2
    return $ CIdx tau carr (cidx1 + cidx2)

cgIdx tau (CAlias _ carr) clen cidx =
    cgIdx tau carr clen cidx

cgIdx tau carr clen cidx = do
    cgBoundsCheck clen cidx
    return $ CIdx tau carr cidx

-- | Generate a 'CExp' representing a slice of an array.
cgSlice :: Type          -- ^ Type of the array element
        -> CExp l        -- ^ The array
        -> CExp l        -- ^ The length of the array
        -> CExp l        -- ^ The array index
        -> Int           -- ^ The length of the slice
        -> Cg l (CExp l) -- ^ The slice
cgSlice tau carr clen cidx len = do
    cgBoundsCheck clen cidx
    cgBoundsCheck clen (cidx + fromIntegral (len - 1))
    return $ CSlice tau carr cidx len

-- | Generate a 'CExp' representing a field projected from a struct.
cgProj :: CExp l -> Field -> Cg l (CExp l)
cgProj ce@(CStruct flds) fld =
    case lookup fld flds of
      Nothing -> faildoc $ text "Cannot find field" <+> ppr fld <+> text "in" <+> ppr ce
      Just ce -> return ce

cgProj (CAlias _ ce) fld =
    cgProj ce fld

cgProj ce fld =
    return $ CExp [cexp|$ce.$id:cfld|]
  where
    cfld :: C.Id
    cfld = C.Id (zencode (namedString fld)) (srclocOf ce)

-- | Dereference a 'CExp' representing a value with ref type, which may or may
-- not be represented as a pointer.
cgDeref :: CExp l -> CExp l
cgDeref (CPtr ce)     = CExp [cexp|*$ce|]
cgDeref (CAlias e ce) = calias e (cgDeref ce)
cgDeref ce            = ce

-- | Take the address of a 'CExp' representing a value of the given type.
cgAddrOf :: Type -> CExp l -> Cg l (CExp l)
cgAddrOf _ (CPtr ce) =
    return ce

cgAddrOf tau (CAlias _ ce) =
    cgAddrOf tau ce

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
cgIf :: forall l a . IsLabel l
     => Type
     -> Exp
     -> (forall a . Kont l a -> Cg l a)
     -> (forall a . Kont l a -> Cg l a)
     -> Kont l a
     -> Cg l a
-- Our strategy is to first attempt to run @me2@ and @me3@ and see if they
-- generate any side effects. If not, we can generate a ternary if. Otherwise,
-- we have to generate an if statement.
cgIf tau e1 me2 me3 k = do
    ce1            <- cgExpOneshot e1
    (citems2, ce2) <- inNewBlock (me2 $ oneshot tau $ cgLower tau)
    (citems3, ce3) <- inNewBlock (me3 $ oneshot tau $ cgLower tau)
    go ce1 citems2 ce2 citems3 ce3
  where
    go :: CExp l -> [C.BlockItem] -> CExp l -> [C.BlockItem] -> CExp l -> Cg l a
    go ce1 [] ce2 [] ce3 =
        runKont k $ CExp [cexp|$ce1 ? $ce2 : $ce3|]

    go ce1 citems2 ce2 citems3 ce3 | isOneshot k = do
        (oneshotk, k') <- splitOneshot k
        citems2'       <- inNewBlock_ (runKont oneshotk ce2)
        citems3'       <- inNewBlock_ (runKont oneshotk ce3)
        appendStm $ cif ce1 (citems2 <> citems2') (citems3 <> citems3')
        k'

    go ce1 citems2 ce2 citems3 ce3 = do
        (citems2', x) <- inNewBlock (runKont k ce2)
        (citems3', _) <- inNewBlock (runKont k ce3)
        appendStm $ cif ce1 (citems2 <> citems2') (citems3 <> citems3')
        return x

-- | Generate C code for a @for@ loop. @cfrom@ and @cto@ are the loop bounds,
-- and @k@ is a continuation that takes an expression representing the loop
-- index and generates the body of the loop.
cgFor :: CExp l -> CExp l -> (CExp l -> Cg l ()) -> Cg l ()
cgFor cfrom@(CInt i) (CInt j) k
    | j <= i     = return ()
    | j == i + 1 = k cfrom

cgFor cfrom cto k = do
    ci :: C.Id <- gensym "__i"
    appendThreadDecl [cdecl|int $id:ci;|]
    (cbody, x) <- inNewBlock $
                  k (CExp [cexp|$id:ci|])
    appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) { $items:cbody }|]
    return x

-- | Lower a 'CExp' into a form we can use directly in an antiquotation.
cgLower :: Type -> CExp l -> Cg l (CExp l)
cgLower tau ce =
    go ce
  where
    go :: CExp l -> Cg l (CExp l)
    go ce@(CStruct {}) = do
        cv <- cgTemp "lower" tau
        cgAssign tau cv ce
        return cv

    go ce@(CBits {}) = do
        ctau <- cgBitcastType tau
        cv   <- cgCTemp ce "bits" ctau Nothing
        appendStm [cstm|$cv = $ce;|]
        return $ CExp [cexp|($ty:bIT_ARRAY_ELEM_TYPE *) &$cv|]

    go (CAlias _ ce) =
        go ce

    go ce =
        return ce

-- | Append a comment to the list of top-level definitions.
appendTopComment :: Doc -> Cg l ()
appendTopComment doc =
    appendTopDef [cedecl|$esc:(pretty 80 (text "/*" <+> align doc <+> text "*/"))|]

-- | Append a comment to the current sequence of statements.
appendComment :: Doc -> Cg l ()
appendComment doc =
    appendStm [cstm|$escstm:(pretty 80 (text "/*" <+> align doc <+> text "*/"))|]

-- | Return a C hex constant.
chexconst :: Integer -> C.Exp
chexconst i = C.Const (C.IntConst ("0x" ++ showHex i "") C.Unsigned i noLoc) noLoc

-- | Return the C identifier corresponding to a value that is an instance of
-- 'Named'.
cvar :: (Located a, Named a) => a -> Cg l C.Id
cvar x = reloc (locOf x) <$> gensym (zencode (namedString x))

-- | Return the C identifier corresponding to a struct.
cstruct :: Struct -> SrcLoc -> C.Id
cstruct s l = C.Id (namedString s ++ "_t") l

-- | Construct a prettier if statement
cif :: ToExp ce => ce -> [C.BlockItem] -> [C.BlockItem] -> C.Stm
cif ce1 [C.BlockStm cstm2] [] =
    [cstm|if ($ce1) $stm:cstm2|]
cif ce1 [C.BlockStm cstm2] [C.BlockStm cstm3] =
    [cstm|if ($ce1) $stm:cstm2 else $stm:cstm3|]
cif ce1 [C.BlockStm cstm2] citems3 =
    [cstm|if ($ce1) $stm:cstm2 else { $items:citems3 }|]
cif ce1 citems2 [] =
    [cstm|if ($ce1) { $items:citems2 }|]
cif ce1 citems2 [C.BlockStm cstm3] =
    [cstm|if ($ce1) { $items:citems2 } else $stm:cstm3|]
cif ce1 citems2 citems3 =
    [cstm|if ($ce1) { $items:citems2 } else { $items:citems3 }|]

-- | Render a location as a string
renderLoc :: Located a => a -> String
renderLoc x = displayS (renderCompact (ppr (locOf x))) ""

rl :: (Located a, Relocatable b) => a -> b -> b
rl l x = reloc (locOf l) x
