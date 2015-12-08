{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}

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
                      mplus,
                      void,
                      when)
import Data.Bits
import Data.Loc
import Data.Monoid (mempty)
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

compileProgram :: LProgram -> Cg ()
compileProgram (Program decls comp tau) = do
    appendTopDef [cedecl|$esc:("#include <kz.h>")|]
    appendTopDecl [cdecl|typename kz_buf_t $id:in_buf;|]
    appendTopDecl [cdecl|typename kz_buf_t $id:out_buf;|]
    (clabels, cblock) <-
        collectLabels $
        inNewMainThreadBlock_ $
        cgDecls decls $ do
        -- Allocate and initialize input and output buffers
        (_, _, a, b) <- checkST tau
        cgInitInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgInitOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
        -- Create storage for the result
        cres <- cgTemp "main_res" (resultType tau)
        -- The done continuation simply puts the computation's result in cres
        let donek :: DoneK
            donek ce = cgAssign (resultType tau) cres ce
        -- Compile the computation
        cgThread takek emitk donek tau comp
        -- Clean up input and output buffers
        cgCleanupInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgCleanupOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
    cgLabels clabels
    appendTopDef [cedecl|
void kz_main(const typename kz_params_t* $id:params)
{
    $items:cblock
}|]
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
        appendStm [cstm|if($cbuf == NULL) { BREAK; }|]
        case (tau, n) of
            (BitT {}, 1) -> return $ CExp [cexp|*$cbuf & 1|]
            (_, 1)       -> return $ CExp [cexp|*$cbuf|]
            _            -> return $ CExp [cexp|$cbuf|]

    emitk :: EmitK Label
    emitk tau ce _k = do
        ceAddr <- cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceAddr

    cgInitInput :: Type -> CExp -> CExp -> Cg ()
    cgInitInput tau cp cbuf =
        cgBufferInit "kz_init_input" tau cp cbuf

    cgInitOutput :: Type -> CExp -> CExp -> Cg ()
    cgInitOutput tau cp cbuf =
        cgBufferInit "kz_init_output" tau cp cbuf

    cgCleanupInput :: Type -> CExp -> CExp -> Cg ()
    cgCleanupInput tau cp cbuf =
        cgBufferCleanup "kz_cleanup_input" tau cp cbuf

    cgCleanupOutput :: Type -> CExp -> CExp -> Cg ()
    cgCleanupOutput tau cp cbuf =
        cgBufferCleanup "kz_cleanup_output" tau cp cbuf

    cgBufferInit :: String -> Type -> CExp -> CExp -> Cg ()
    cgBufferInit = cgBufferConfig appendInitStm

    cgBufferCleanup :: String -> Type -> CExp -> CExp -> Cg ()
    cgBufferCleanup = cgBufferConfig appendCleanupStm

    cgBufferConfig :: (C.Stm -> Cg ()) -> String -> Type -> CExp -> CExp -> Cg ()
    cgBufferConfig appStm f tau cp cbuf =
        go tau
      where
        go :: Type -> Cg ()
        go (ArrT _ tau _)          = go tau
        go (BitT {})               = appStm [cstm|$id:(fname "bit")($cp, &$cbuf);|]
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

    cgInput :: Type -> CExp -> CExp -> Cg CExp
    cgInput tau cbuf cn = go tau
      where
        go :: Type -> Cg CExp
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgInput tau cbuf (cn*ci)
        go (BitT {})               = return $ CExp [cexp|kz_input_bit(&$cbuf, $cn)|]
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

    cgOutput :: Type -> CExp -> CExp -> CExp -> Cg ()
    cgOutput tau cbuf cn cval = go tau
      where
        go :: Type -> Cg ()
        go (ArrT iota tau _)       = do ci <- cgIota iota
                                        cgOutput tau cbuf (cn*ci) cval
        go (BitT {})               = appendStm [cstm|kz_output_bit(&$cbuf, $cval, $cn);|]
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

cgLabels :: Set Label -> Cg ()
cgLabels ls = do
    go (Set.toList ls)
  where
    go :: [Label] -> Cg ()
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
cgInitCheckErr :: Located a => C.Exp -> String -> a -> Cg ()
cgInitCheckErr ce msg x =
    appendInitStm [cstm|kz_check_error($ce, $string:loc, $string:msg);|]
  where
    loc :: String
    loc = displayS (renderCompact (ppr (locOf x))) ""

-- | Generate code to check return value of a function call.
cgCheckErr :: Located a => C.Exp -> String -> a -> Cg ()
cgCheckErr ce msg x =
    appendStm [cstm|kz_check_error($ce, $string:loc, $string:msg);|]
  where
    loc :: String
    loc = displayS (renderCompact (ppr (locOf x))) ""

-- | Generate code to handle the result of a thread's computation.
type DoneK = CExp -> Cg ()

cgThread :: TakeK Label -- ^ Code generator for take
         -> EmitK Label -- ^ Code generator for emit
         -> DoneK       -- ^ Code generator to deal with result of computation
         -> Type        -- ^ Type of the result of the computation
         -> LComp       -- ^ Computation to compiled
         -> Cg ()
cgThread takek emitk donek tau comp = do
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
        l_done <- genLabel "done"
        useLabel l_done
        -- Generate code for the computation
        useLabels (compUsedLabels comp)
        ce <- cgComp takek emitk comp l_done
        cgWithLabel l_done $ donek ce
    appendDecls [decl | C.BlockDecl decl <- cblock]
    appendStms [cstms|BEGIN_DISPATCH; $stms:([stm | C.BlockStm stm <- cblock]) END_DISPATCH;|]
  where
    cUR_KONT :: C.Id
    cUR_KONT = "curk"

cgDecls :: [LDecl] -> Cg a -> Cg a
cgDecls [] k =
    k

cgDecls (decl:decls) k =
    cgDecl decl $ cgDecls decls k

cgDecl :: LDecl -> Cg a -> Cg a
cgDecl (LetD decl _) k =
    cgLocalDecl decl k

cgDecl decl@(LetFunD f iotas vbs tau_ret e l) k = do
    cf <- cvar f
    extendVars [(bVar f, tau)] $ do
    extendVarCExps [(bVar f, CExp [cexp|$id:cf|])] $ do
    appendTopComment (ppr f <+> colon <+> align (ppr tau))
    withSummaryContext decl $ do
        inSTScope tau_ret $ do
        extendIVars (iotas `zip` repeat IotaK) $ do
        extendVars vbs $ do
        (ciotas, cparams1) <- unzip <$> mapM cgIVar iotas
        (cvbs,   cparams2) <- unzip <$> mapM cgVarBind vbs
        cres_ident         <- gensym "let_res"
        citems <- inNewThreadBlock_ $
                  extendIVarCExps (iotas `zip` ciotas) $
                  extendVarCExps  (map fst vbs `zip` cvbs) $
                  inLocalScope $ do
                  cres <- if isReturnedByRef tau_res
                          then return $ CExp [cexp|$id:cres_ident|]
                          else cgTemp "let_res" tau_res
                  cgExp e >>= cgAssign tau_res cres
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
    cgField :: (Field, Type) -> Cg C.FieldGroup
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
    compc :: CompC
    compc takek emitk k =
        withInstantiatedTyVars tau $ do
        comp' <- uniquifyCompLabels comp
        useLabels (compUsedLabels comp')
        cgComp takek emitk comp' k

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
    funcompc :: FunCompC
    funcompc iotas es takek emitk k =
        withInstantiatedTyVars tau_ret $ do
        comp'  <- uniquifyCompLabels comp
        ciotas <- mapM cgIota iotas
        ces    <- mapM cgArg es
        extendIVars (ivs `zip` repeat IotaK) $ do
        extendVars  vbs $ do
        extendIVarCExps (ivs `zip` ciotas) $ do
        extendVarCExps  (map fst vbs `zip` ces) $ do
        useLabels (compUsedLabels comp')
        cgComp takek emitk comp' k
      where
        cgArg :: LArg -> Cg CExp
        cgArg (ExpA e) =
            withFvContext e $
            cgExp e

        cgArg (CompA comp) =
            return $ CComp compc
          where
            compc :: CompC
            compc takek emitk k = cgComp takek emitk comp k

-- | Figure out the type substitution necessary for transforming the given type
-- to the ST type of the current computational context. We need to do this when
-- compiling a computation of computation function.
withInstantiatedTyVars :: Type -> Cg a -> Cg a
withInstantiatedTyVars tau@(ST _ _ s a b _) k = do
    ST _ _ s' a' b' _ <- appSTScope tau
    extendTyVarTypes [(alpha, tau) | (TyVarT alpha _, tau) <- [s,a,b] `zip` [s',a',b']] k

withInstantiatedTyVars _tau k =
    k

cgLocalDecl :: LocalDecl -> Cg a -> Cg a
cgLocalDecl decl@(LetLD v tau e _) k = do
    cve <- withSummaryContext decl $ do
           inSTScope tau $ do
           ce         <- cgExp e
           isTopLevel <- isInTopScope
           cve        <- cgBinder isTopLevel (bVar v) tau
           cgAssign tau cve ce
           return cve
    extendVars [(bVar v, tau)] $ do
    extendVarCExps [(bVar v, cve)] $ do
    k

cgLocalDecl decl@(LetRefLD v tau maybe_e _) k = do
    cve <- withSummaryContext decl $ do
           isTopLevel <- isInTopScope
           cve        <- cgBinder isTopLevel (bVar v) tau
           case maybe_e of
             Nothing -> cgDefaultValue tau cve
             Just e  -> do ce <- inLocalScope $ cgExp e
                           cgAssign tau cve ce
           return cve
    extendVars [(bVar v, refT tau)] $ do
    extendVarCExps [(bVar v, cve)] $ do
    k

cgDefaultValue :: Type -> CExp -> Cg ()
cgDefaultValue tau cv = go tau
  where
    go :: Type -> Cg ()
    go (BoolT {})  = cgAssign tau cv (CExp [cexp|0|])
    go (BitT {})   = cgAssign tau cv (CExp [cexp|0|])
    go (FixT {})   = cgAssign tau cv (CExp [cexp|0|])
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

cgConst :: Const -> Cg CExp
cgConst UnitC            = return CVoid
cgConst (BoolC b)        = return $ CBool b
cgConst (BitC b)         = return $ CBit b
cgConst (FixC I _ _ 0 r) = return $ CInt (numerator r)
cgConst (FixC {})        = faildoc $ text "Fractional and non-unit scaled fixed point values are not supported."
cgConst (FloatC _ r)     = return $ CFloat r
cgConst (StringC s)      = return $ CExp [cexp|$string:s|]

cgConst c@(ArrayC cs) = do
    tau           <- inferConst noLoc c
    (_, tau_elem) <- checkArrT tau
    ces           <- mapM cgConst cs
    cv            <- gensym "__const_arr"
    ctau          <- cgType tau
    appendTopDecl [cdecl|const $ty:ctau $id:cv = { $inits:(cgArrayConstInits tau_elem ces) };|]
    return $ CExp [cexp|$id:cv|]
  where
    cgArrayConstInits :: Type -> [CExp] -> [C.Initializer]
    cgArrayConstInits (BitT {}) ces =
        finalizeBits $ foldl mkBits (0,0,[]) ces
      where
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

    cgArrayConstInits _tau ces =
        [[cinit|$ce|] | ce <- ces]

cgConst c@(StructC s flds) = do
    cv                    <- gensym "__const_struct"
    ctau                  <- inferConst noLoc c >>= cgType
    StructDef _ fldDefs _ <- lookupStruct s
    -- We must be careful to generate initializers in the same order as the
    -- struct's fields are declared, which is why we map 'cgField' over the
    -- struct's field definitions rather than mapping it over the values as
    -- declared in @flds@
    cinits                <- mapM (cgField flds) (map fst fldDefs)
    appendTopDecl [cdecl|const $ty:ctau $id:cv = { $inits:cinits };|]
    return $ CExp [cexp|$id:cv|]
  where
    cgField :: [(Field, Const)] -> Field -> Cg C.Initializer
    cgField flds f = do
        c  <- case lookup f flds of
                Nothing -> panicdoc $ text "cgField: missing field"
                Just c -> return c
        ce <- cgConst c
        return [cinit|$ce|]

cgExp :: Exp -> Cg CExp
cgExp (ConstE c _) =
    cgConst c

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

    cgCast _ tau1@(FixT sc1 _ _ _ _) tau2@(FixT sc2 _ _ _ _) | sc2 /= sc1 =
        faildoc $
        text "Cannot cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2 <+>
        text "since types have different scales."

    cgCast _ tau1@(FixT _ _ _ bp1 _) tau2@(FixT _ _ _ bp2 _) | bp2 /= bp1 =
        faildoc $
        text "Cannot cast from" <+> ppr tau1 <+> text "to" <+> ppr tau2 <+>
        text "since types have different binary points."

    cgCast ce _ tau_to = do
        ctau_to <- cgType tau_to
        return $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

    cgBitcast :: CExp -> Type -> Type -> Cg CExp
    cgBitcast ce tau_from tau_to = do
        ctau_from <- cgBitcastType tau_from
        ctau_to   <- cgType tau_to
        return $ CExp $ rl l [cexp|*(($ty:ctau_to*) (($ty:ctau_from*) $ce))|]

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

cgExp (IfE e1 e2 e3 _) = do
    tau <- inferExp e2
    cgIf tau e1 (cgExp e2) (cgExp e3)

cgExp (LetE decl e _) =
    cgLocalDecl decl $ cgExp e

cgExp (CallE f iotas es l) = do
    FunT _ _ tau_ret _ <- lookupVar f
    let tau_res        =  resultType tau_ret
    cf                 <- lookupVarCExp f
    FunT ivs _ _ _     <- lookupVar f
    ciotas             <- mapM cgIota iotas
    extendIVarCExps (ivs `zip` ciotas) $ do
    ces <- mapM cgArg es
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

cgExp (DerefE e _) = do
    tau   <- inferExp e >>= checkRefT
    ce    <- cgExp e
    ctemp <- cgTemp "deref" tau
    cgAssign tau ctemp (unPtr ce)
    return ctemp

cgExp (AssignE e1 e2 _) = do
    tau <- inferExp e1
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    cgAssign tau ce1 ce2
    return CVoid

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

cgExp (WhileE e_test e_body l) = do
    (citems_test, ce_test) <- inNewBlock $ cgExp e_test
    citems_body            <- inNewBlock_ $ cgExp e_body
    appendBlock $ map (rl l) citems_test
    appendStm $ rl l [cstm|while ($ce_test) { $items:citems_body $items:citems_test }|]
    return CVoid

cgExp (ForE _ v v_tau e_start e_len e_body l) = do
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

cgExp e@(ArrayE es l) =
    case unConstE e of
      Nothing -> cgArrayExp
      Just c  -> cgConst c
  where
    cgArrayExp :: Cg CExp
    cgArrayExp = do
        (_, tau) <- inferExp e >>= checkArrT
        cv       <- gensym "__arr"
        ctau     <- cgType tau
        appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv[$int:(length es)];|]
        forM_ (es `zip` [(0::Integer)..]) $ \(e,i) -> do
            ce <- cgExp e
            cgArrayWrite tau (CExp [cexp|$id:cv|]) (fromIntegral i) ce
        return $ CExp [cexp|$id:cv|]

cgExp (IdxE e1 e2 maybe_len _) = do
    (_, tau) <- inferExp e1 >>= checkArrOrRefArrT
    ce1      <- cgExp e1
    ce2      <- cgExp e2
    case maybe_len of
      Nothing  -> cgIdx tau ce1 ce2
      Just len -> cgSlice tau ce1 ce2 len

cgExp e@(StructE s flds l) = do
    case unConstE e of
      Nothing -> cgStructExp
      Just c  -> cgConst c
  where
    cgStructExp :: Cg CExp
    cgStructExp = do
        cv <- cgTemp "struct" (StructT s l)
        mapM_ (cgField cv) flds
        return cv

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

cgExp (ReturnE _ e _) =
    cgExp e

cgExp (BindE WildV _ e1 e2 _) = do
    void $ cgExp e1
    cgExp e2

cgExp (BindE (TameV v) tau e1 e2 _) = do
    ce1 <- cgExp e1
    extendVars [(bVar v, tau)] $ do
    extendVarCExps [(bVar v, ce1)] $ do
    cgExp e2

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

unCComp :: CExp -> Cg CompC
unCComp (CComp compc) =
    return compc

unCComp ce =
    panicdoc $ nest 2 $ text "unCComp: not a CComp:" </> ppr ce

unCFunComp :: CExp -> Cg FunCompC
unCFunComp (CFunComp funcompc) =
    return funcompc

unCFunComp ce =
    panicdoc $ nest 2 $ text "unCFunComp: not a CFunComp:" </> ppr ce

-- | Return the C type appropriate for bit casting.
cgBitcastType :: Type -> Cg C.Type
cgBitcastType tau = do
    w <- typeBitWidth tau
    case w of
      _ | w <= 8  -> return [cty|typename uint8_t|]
      _ | w <= 16 -> return [cty|typename uint16_t|]
      _ | w <= 32 -> return [cty|typename uint32_t|]
      _ | w <= 64 -> return [cty|typename uint64_t|]
      _ ->
        faildoc $ text "Cannot compile bitcast type for" <+> ppr tau <+> "(width >64)."

-- | Compile a type to its C representation.
cgType :: Type -> Cg C.Type
cgType (UnitT {}) =
    return [cty|void|]

cgType (BoolT {}) =
    return [cty|typename uint8_t|]

cgType (BitT {}) =
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

cgType (ArrT (ConstI n _) (BitT _) _) =
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
cgBinder isTopLevel v tau@(ST _ (C tau') _ _ _ _) | isPureishT tau = do
    cgBinder isTopLevel v tau'

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
                       | otherwise  = appendThreadDecl decl

-- | Generate code for a C temporary with a gensym'd name, based on @s@ and
-- prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgCTemp :: Located a => a -> String -> C.Type -> Maybe C.Initializer -> Cg CExp
cgCTemp l s ctau maybe_cinit = do
    cv <- gensym ("__" ++ s)
    case maybe_cinit of
      Nothing    -> appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendThreadDecl $ rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp $ rl l [cexp|$id:cv|]

-- | Generate code for a top-level C temporary with a gensym'd name, based on @s@
-- and prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgTopCTemp :: Located a => a -> String -> C.Type -> Maybe C.Initializer -> Cg CExp
cgTopCTemp l s ctau maybe_cinit = do
    cv <- gensym ("__" ++ s)
    case maybe_cinit of
      Nothing    -> appendTopDecl $ rl l [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendTopDecl $ rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp $ rl l [cexp|$id:cv|]

-- | Generate an empty label statement if the label argument is required.
cgLabel :: Label -> Cg ()
cgLabel lbl = do
    required <- isLabelUsed lbl
    when required $
        cgWithLabel lbl $
        appendStm [cstm|;|]

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
    lblMacro :: C.Id
    lblMacro = C.Id ("LABEL(" ++ ident ++ ")") l

    ident :: String
    l :: SrcLoc
    C.Id ident l = toIdent lbl noLoc

-- | 'cgComp' compiles a computation and ensures that the continuation label is
-- jumped to. We assume that the continuation labels the code that will be
-- generated immediately after the call to 'cgComp', so if the computation
-- compiles to straight-line code, no @goto@ will be generated.
cgComp :: TakeK Label -- ^ Code generator for take
       -> EmitK Label -- ^ Code generator for emit
       -> LComp       -- ^ Computation to compiled
       -> Label       -- ^ Label of our continuation
       -> Cg CExp     -- ^ Value returned by the computation.
cgComp takek emitk comp k =
    cgSteps (unComp comp)
  where
    cgSteps :: [Step Label] -> Cg CExp
    cgSteps [] =
        faildoc $ text "No computational steps to compile!"

    cgSteps (LetC l decl _ : steps) =
        cgWithLabel l $
        cgLocalDecl decl $
        cgSteps steps

    cgSteps [step] =
        cgStep step k

    cgSteps (step:steps) = do
        k <- stepLabel (head steps)
        (withFvContext step $ cgStep step k) >>= cgBind steps

    cgBind :: [Step Label] -> CExp -> Cg CExp
    cgBind [] ce =
        return ce

    cgBind (BindC l WildV _ _ : steps) _ =
        cgWithLabel l $ do
        cgSteps steps

    cgBind (BindC l (TameV v) tau _ : steps) ce =
        cgWithLabel l $ do
        clow <- cgLower tau ce
        extendVars [(bVar v, tau)] $ do
        extendVarCExps [(bVar v, clow)] $ do
        cgSteps steps

    cgBind steps _ =
        cgSteps steps

    cgStep :: Step Label -> Label -> Cg CExp
    cgStep (VarC l v _) k =
        cgWithLabel l $ do
        compc <- lookupVarCExp v >>= unCComp
        compc takek emitk k

    cgStep (CallC l f iotas args _) k = do
        cgWithLabel l $ do
        funcompc <- lookupVarCExp f >>= unCFunComp
        funcompc iotas args takek emitk k

    cgStep (IfC l e thenk elsek _) k =
        cgWithLabel l $ do
        tau <- inferComp thenk
        cgIf tau e (cgComp takek emitk thenk k) (cgComp takek emitk elsek k)

    cgStep (LetC {}) _ =
        faildoc $ text "Cannot compile let computation step."

    cgStep (WhileC l e_test c_body sloc) _ = do
        (citems_test, ce_test) <- inNewBlock $ cgExp e_test
        citems_body            <- inNewBlock_ $ do
                                  l_inner <- genLabel "inner_whilek"
                                  void $ cgComp takek emitk c_body l_inner
                                  cgLabel l_inner
        cgWithLabel l $ do
            appendBlock $ map (rl sloc) citems_test
            appendStm $ rl sloc [cstm|while ($ce_test) { $items:citems_body $items:citems_test }|]
        return CVoid

    cgStep (ForC l _ v v_tau e_start e_len c_body sloc) _ = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendThreadDecl $ rl sloc [cdecl|$ty:cv_tau $id:cv;|]
        ce_start <- cgExp e_start
        ce_len   <- cgExp e_len
        citems   <- inNewBlock_ $ do
                    l_inner <- genLabel "inner_fork"
                    void $ cgComp takek emitk c_body l_inner
                    cgLabel l_inner
        cgWithLabel l $
            appendStm $ rl sloc [cstm|for ($id:cv = $ce_start; $id:cv < $(ce_start + ce_len); $id:cv++) { $items:citems }|]
        return CVoid

    -- A 'LiftC' is a monadic value, but it doesn't take or emit. That is, it is
    -- in ST, so it may have side effects, but those side effects do not include
    -- taking or emitting. Therefore, we need to lower it to make sure the side
    -- effect happens.
    cgStep (LiftC l e _) _ =
        cgWithLabel l $ do
        tau <- inferExp e
        cgExp e >>= cgLower (resultType tau)

    -- A 'ReturnC' is a pure value, so we do not need to lower it.
    cgStep (ReturnC l e _) _ =
        cgWithLabel l $
        cgExp e

    cgStep (BindC {}) _ =
        faildoc $ text "Cannot compile bind computation step."

    cgStep (TakeC l tau _) k =
        cgWithLabel l $
        takek 1 tau k

    cgStep (TakesC l n tau _) k =
        cgWithLabel l $
        takek n tau k

    cgStep (EmitC l e _) k =
        cgWithLabel l $ do
        tau <- inferExp e
        ce  <- cgExp e
        emitk tau ce k
        return CVoid

    cgStep (EmitsC l e _) k =
        cgWithLabel l $ do
        tau <- inferExp e
        ce  <- cgExp e
        emitk tau ce k
        return CVoid

    cgStep (RepeatC l _ c_body sloc) _ = do
        citems <- inNewBlock_ $ do
                  void $ cgComp takek emitk c_body l
                  cgLabel l
        appendStm $ rl sloc [cstm|for (;;) { $items:citems }|]
        return CVoid

    cgStep step@(ParC ann b left right _) _ =
        withSummaryContext step $ do
        doFuse <- asksFlags (testDynFlag Fuse)
        if doFuse then fuse else dontFuse ann
      where
        fuse :: Cg CExp
        fuse = do
            do (s, a, c) <- askSTIndTypes
               tau       <- inferStep step
               comp      <- fusePar s a b c left right
               useLabels (compUsedLabels comp)
               checkComp comp tau
               cgComp takek emitk comp k
          `mplus`
            do traceFusion $ text "Failed to fuse" <+>
                   (nest 2 $ text "producer:" </> ppr left) </>
                   (nest 2 $ text "and consumer:" </> ppr right)
               dontFuse ann

        dontFuse :: PipelineAnn -> Cg CExp
        dontFuse ann = do
           tau_res <- resultType <$> inferStep step
           case ann of
             Pipeline -> cgParMultiThreaded  takek emitk tau_res b left right k
             _        -> cgParSingleThreaded takek emitk tau_res b left right k

    cgStep (LoopC {}) _ =
        faildoc $ text "cgStep: saw LoopC"

-- | Compile a par, i.e., a producer/consumer pair, using the simple
-- single-threaded strategy. The take and emit code generators should generate
-- code for the par's take and emit.
cgParSingleThreaded :: TakeK Label -- ^ Code generator for /producer's/ take
                    -> EmitK Label -- ^ Code generator for /consumer's/ emit
                    -> Type        -- ^ The type of the result of the par
                    -> Type        -- ^ The type of the par's internal buffer
                    -> LComp       -- ^ The producer computation
                    -> LComp       -- ^ The consumer computation
                    -> Label       -- ^ The computation's continuation
                    -> Cg CExp     -- ^ The result of the computation
cgParSingleThreaded takek emitk tau_res b left right k = do
    (s, a, c) <- askSTIndTypes
    -- Generate a temporary to hold the result of the par construct.
    cres <- cgTemp "par_res" tau_res
    -- Create the computation that follows the par.
    l_pardone <- genLabel "par_done"
    useLabel l_pardone
    -- donek will generate code to store the result of the par and jump to
    -- the continuation.
    let donek :: CExp -> Cg ()
        donek ce = do cgAssign tau_res cres ce
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
    ctau  <- cgType b
    cbuf  <- cgCTemp b "par_buf"  [cty|$ty:ctau|]  Nothing
    cbufp <- cgCTemp b "par_bufp" [cty|const $ty:ctau*|] Nothing
    -- Generate code for the left and right computations.
    localSTIndTypes (Just (b, b, c)) $
        cgComp (takek' cleftk crightk cbuf cbufp) emitk right k >>= donek
    localSTIndTypes (Just (s, a, b)) $
        cgComp takek (emitk' cleftk crightk cbuf cbufp) left k >>= donek
    cgLabel l_pardone
    return cres
  where
    takek' :: CExp -> CExp -> CExp -> CExp -> TakeK Label
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
        return $ CExp [cexp|*$cbufp|]

    -- The multi-element take is a bit tricker. We allocate a buffer to hold
    -- all the elements, and then loop, jumping to the left computation's
    -- continuation repeatedly, until the buffer is full. Then we fall
    -- through to the next action, which is why we call @k2@ with @ccomp@
    -- without forcing its label to be required---we don't need the label!
    takek' cleftk crightk _cbuf cbufp n tau _k = do
        ctau_arr <- cgType (ArrT (ConstI n noLoc) tau noLoc)
        carr     <- cgCTemp tau "par_takes_xs" [cty|$ty:ctau_arr|] Nothing
        lbl      <- genLabel "inner_takesk"
        useLabel lbl
        appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
        cgFor 0 (fromIntegral n) $ \ci -> do
            appendStm [cstm|INDJUMP($cleftk);|]
            cgWithLabel lbl $
                cgArrayWrite tau carr ci (CExp [cexp|*$cbufp|])
        return carr

    emitk' :: CExp -> CExp -> CExp -> CExp -> EmitK Label
    emitk' cleftk crightk cbuf cbufp (ArrT (ConstI 1 _) tau _) ce k = do
        useLabel k
        appendStm [cstm|$cleftk = LABELADDR($id:k);|]
        cidx <- cgIdx tau ce 0
        cgAssignBufp tau cbuf cbufp cidx
        appendStm [cstm|INDJUMP($crightk);|]

    emitk' cleftk crightk cbuf cbufp (ArrT iota tau _) ce _k = do
        cn    <- cgIota iota
        loopl <- genLabel "emitsk_next"
        useLabel loopl
        appendStm [cstm|$cleftk = LABELADDR($id:loopl);|]
        cgFor 0 cn $ \ci -> do
            cidx <- cgIdx tau ce ci
            cgAssignBufp tau cbuf cbufp cidx
            appendStm [cstm|INDJUMP($crightk);|]
            -- Because we need a statement to label, but the continuation is
            -- the next loop iteration...
            cgLabel loopl

    -- @tau@ must be a base (scalar) type
    emitk' cleftk crightk cbuf cbufp tau ce k = do
        useLabel k
        appendStm [cstm|$cleftk = LABELADDR($id:k);|]
        cgAssignBufp tau cbuf cbufp ce
        appendStm [cstm|INDJUMP($crightk);|]

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

-- | Generate code that exits from a computation that is part of a par.
type ExitK = Cg ()

-- | Compile a par, i.e., a producer/consumer pair, using the multi-threaded
-- strategy. The take and emit code generators passed as arguments to
-- 'cgParMultiThreaded' should generate code for the outer take and emit---the
-- inner take and emit is done with a producer-consumer buffer.
cgParMultiThreaded :: TakeK Label -- ^ Code generator for /producer's/ take
                   -> EmitK Label -- ^ Code generator for /consumer's/ emit
                   -> Type        -- ^ The type of the result of the par
                   -> Type        -- ^ The type of the par's internal buffer
                   -> LComp       -- ^ The producer computation
                   -> LComp       -- ^ The consumer computation
                   -> Label       -- ^ The computation's continuation
                   -> Cg CExp     -- ^ The result of the computation
cgParMultiThreaded takek emitk tau_res b left right k = do
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
    l_pardone <- genLabel "par_done"
    useLabel l_pardone
    -- Re-label the consumer computation. We have to do this because we need to
    -- generate code that initializes the par construct, and this initialization
    -- code needs to have the label of the consumer computation because that is
    -- the label that will be jumped to to run the consumer computation.
    l_consumer  <- compLabel right
    l_consumer' <- genLabel "consumer"
    let right'  =  setCompLabel l_consumer' right
    -- Generate to initialize the thread
    when (not (isUnitT tau_res)) $
        appendInitStm [cstm|ctinfo.result = &$cres;|]
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
    cgLabel l_pardone
    return cres
  where
    cgExitWhenDone :: CExp -> ExitK -> Cg ()
    cgExitWhenDone ctinfo exitk = do
        cblock <- inNewBlock_ exitk
        appendStm [cstm|if ($ctinfo.done) { $items:cblock }|]

    -- | Insert a memory barrier
    cgMemoryBarrier :: Cg ()
    cgMemoryBarrier =
        appendStm [cstm|kz_memory_barrier();|]

    cgProducer :: C.Id -> CExp -> LComp -> Cg ()
    cgProducer cf cbuf comp = do
        tau <- inferComp comp
        (clabels, cblock) <-
            collectLabels $
            inNewThreadBlock_ $
            cgThread takek' emitk' donek tau comp
        cgLabels clabels
        appendTopDef [cedecl|
void* $id:cf(void* _tinfo)
{
    typename kz_tinfo_t* tinfo = (typename kz_tinfo_t*) _tinfo;

    for (;;) {
        kz_check_error(kz_thread_wait(tinfo), $string:loc, "Error waiting for thread to start.");
        {
            $items:cblock
        }
        (*tinfo).done = 1;
    }
    return NULL;
}|]
      where
        ctinfo :: CExp
        ctinfo = CExp [cexp|*tinfo|]

        loc :: String
        loc = displayS (renderCompact (ppr (locOf comp))) ""

        -- When the producer takes, we need to make sure that the consumer has
        -- asked for more data than we have given it, so we spin until the
        -- consumer requests data.
        takek' :: TakeK Label
        takek' n tau k = do
            cgWaitForConsumerRequest ctinfo exitk
            takek n tau k

        emitk' :: EmitK Label
        -- Right now we just loop and write the elements one by one---it would
        -- be better to write them all at once.
        emitk' (ArrT iota tau _) ce _k = do
            cn <- cgIota iota
            cgFor 0 cn $ \ci -> do
                cidx <- cgIdx tau ce ci
                cgProduce ctinfo cbuf exitk tau cidx

        -- @tau@ must be a base (scalar) type
        emitk' tau ce _k =
            cgProduce ctinfo cbuf exitk tau ce

        exitk :: Cg ()
        exitk = appendStm [cstm|BREAK;|]

        donek :: DoneK
        donek ce = do
            ctau_res <- cgType tau_res
            cgAssign tau_res (CPtr (CExp [cexp|($ty:ctau_res*) $ctinfo.result|])) ce
            cgMemoryBarrier
            appendStm [cstm|$ctinfo.done = 1;|]

        -- | Put a single data element in the buffer.
        cgProduce :: CExp -> CExp -> ExitK -> Type -> CExp -> Cg ()
        cgProduce ctinfo cbuf exitk tau ce = do
            cgWaitWhileBufferFull ctinfo exitk
            cgAssign tau (CExp [cexp|$cbuf[$ctinfo.prod_cnt % KZ_BUFFER_SIZE]|]) ce
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.prod_cnt;|]

        -- | Wait until the consumer requests data
        cgWaitForConsumerRequest :: CExp -> ExitK -> Cg ()
        cgWaitForConsumerRequest ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.cons_req - $ctinfo.prod_cnt == 0);|]
            cgExitWhenDone ctinfo exitk

        -- | Wait while the buffer is full
        cgWaitWhileBufferFull :: CExp -> ExitK -> Cg ()
        cgWaitWhileBufferFull ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == KZ_BUFFER_SIZE);|]
            cgExitWhenDone ctinfo exitk

    cgConsumer :: CExp -> CExp -> CExp -> CExp -> LComp -> Label -> Cg ()
    cgConsumer cthread ctinfo cbuf cres comp l_pardone = do
        ce <- cgComp takek' emitk' comp k
        appendStm [cstm|$ctinfo.done = 1;|]
        cgAssign tau_res cres ce
        let loc_s = displayS (renderCompact (ppr (locOf comp))) ""
        appendStm [cstm|kz_check_error(kz_thread_join($cthread, NULL), $string:loc_s, "Cannot join on thread.");|]
        appendStm [cstm|JUMP($id:l_pardone);|]
      where
        takek' :: TakeK Label
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

        emitk' :: EmitK Label
        emitk' = emitk

        exitk :: Cg ()
        exitk = appendStm [cstm|JUMP($id:l_pardone);|]

        -- | Consumer a single data element from the buffer. We take a consumption
        -- continuation, because we must be sure that we insert a memory barrier
        -- before incrementing the consumer count.
        cgConsume :: CExp -> CExp -> ExitK -> (CExp -> Cg a) -> Cg a
        cgConsume ctinfo cbuf exitk consumek = do
            cgWaitWhileBufferEmpty ctinfo exitk
            x <- consumek (CExp [cexp|$cbuf[$ctinfo.cons_cnt % KZ_BUFFER_SIZE]|])
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.cons_cnt;|]
            return x

        -- | Request @cn@ data elements.
        cgRequestData :: CExp -> CExp -> Cg ()
        cgRequestData ctinfo cn =
            appendStm [cstm|$ctinfo.cons_req += $cn;|]

        -- | Wait while the buffer is empty
        cgWaitWhileBufferEmpty :: CExp -> ExitK -> Cg ()
        cgWaitWhileBufferEmpty ctinfo exitk = do
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == 0);|]
            cgExitWhenDone ctinfo exitk

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

-- | Write an element to an array.
cgArrayWrite :: Type -> CExp -> CExp -> CExp -> Cg ()
cgArrayWrite (BitT {}) carr ci cx = cgBitArrayWrite carr ci cx
cgArrayWrite _         carr ci cx = appendStm [cstm|$carr[$ci] = $cx;|]

-- XXX: Should use more efficient bit twiddling code here. See:
--
--   http://realtimecollisiondetection.net/blog/?p=78
--   https://graphics.stanford.edu/~seander/bithacks.html
--   https://stackoverflow.com/questions/18561655/bit-set-clear-in-c
--

-- | Write an element to a bit array.
cgBitArrayWrite :: CExp -> CExp -> CExp -> Cg ()
cgBitArrayWrite carr ci cx =
    if cx
    then appendStm [cstm|$carr[$cbitIdx] |= $cbitMask;|]
    else appendStm [cstm|$carr[$cbitIdx] &= ~$cbitMask;|]
  where
    cbitIdx, cbitOff :: CExp
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp
    cbitMask = 1 `shiftL'` cbitOff

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
cgIdx tau (CSlice _ carr cidx1 _) cidx2 =
    return $ CIdx tau carr (cidx1 + cidx2)

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
cgIf :: Type -> Exp -> Cg CExp -> Cg CExp -> Cg CExp
cgIf tau e1 me2 me3 = do
    cres        <- cgTemp "if_res" tau_res
    ce1         <- cgExp e1
    citems2     <- inNewBlock_ (me2 >>= cgAssign tau_res cres)
    citems3     <- inNewBlock_ (me3 >>= cgAssign tau_res cres)
    if citems3 == mempty
      then appendStm [cstm|if ($ce1) { $items:citems2 }|]
      else appendStm [cstm|if ($ce1) { $items:citems2 } else { $items:citems3 }|]
    return cres
  where
    tau_res :: Type
    tau_res = resultType tau

-- | Generate C code for a @for@ loop. @cfrom@ and @cto@ are the loop bounds,
-- and @k@ is a continuation that takes an expression representing the loop
-- index and generates the body of the loop.
cgFor :: CExp -> CExp -> (CExp -> Cg ()) -> Cg ()
cgFor cfrom@(CInt i) (CInt j) k
    | j <= i     = return ()
    | j == i + 1 = k cfrom

cgFor cfrom cto k = do
    ci <- gensym "__i"
    appendThreadDecl [cdecl|int $id:ci;|]
    (cbody, x) <- inNewBlock $
                  k (CExp [cexp|$id:ci|])
    appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) { $items:cbody }|]
    return x

cgLower :: Type -> CExp -> Cg CExp
cgLower tau ce = go ce
  where
    go :: CExp -> Cg CExp
    go ce@CVoid =
        return ce

    go ce@(CBool {}) =
        return ce

    go ce@(CBit {}) =
        return ce

    go ce@(CInt {}) =
        return ce

    go ce@(CFloat {}) =
        return ce

    go (CComp {}) =
        faildoc $ text "Cannot lower a computation."

    go ce@(CExp (C.Var {})) =
        return ce

    go ce = do
        clow <- cgTemp "lower" tau
        cgAssign tau clow ce
        return clow

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

rl :: (Located a, Relocatable b) => a -> b -> b
rl l x = reloc (locOf l) x
