{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Backend.C
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Backend.C (
    compileProgram
  ) where

import Prelude

import Control.Monad (forM_,
                      unless,
                      when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Bits
import Data.Foldable (toList)
import Data.Loc
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import qualified Data.Vector as V
import qualified Language.C.Quote as C
import Numeric (showHex)
import Text.PrettyPrint.Mainland

import KZC.Backend.C.CExp
import KZC.Backend.C.Code
import KZC.Backend.C.Monad
import KZC.Backend.C.Util
import KZC.Check.Path
import KZC.Config
import KZC.Core.Enum
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Interp (compileAndRunGen)
import KZC.Label
import KZC.Monad (KZC)
import KZC.Name
import KZC.Optimize.LutToGen (lutGenToExp)
import KZC.Quote.C
import KZC.Util.Error
import KZC.Util.Staged
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Util.ZEncode

-- | Create a oneshot continuation.
oneshot :: Type -> (CExp l -> Cg l a) -> Kont l a
oneshot = OneshotK Nothing

-- | Create a oneshot continuation with the name of a binder to use.
oneshotBinder :: BoundVar -> Type -> (CExp l -> Cg l a) -> Kont l a
oneshotBinder bv = OneshotK (Just bv)

-- | Create a multishot continuation.
multishot :: (CExp l -> Cg l a) -> Kont l a
multishot = MultishotK

-- | Create a multishot continuation that binds its argument to the given
-- 'CExp'.
multishotBind :: Type -> CExp l -> Kont l ()
multishotBind tau cv = MultishotBindK tau cv (const $ return ())

-- | Return 'True' if the continuation is oneshot, 'False' otherwise.
isOneshot :: Kont l a -> Bool
isOneshot OneshotK{}       = True
isOneshot MultishotK{}     = False
isOneshot MultishotBindK{} = False

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
    cv <- cgBinder (bVar bv) tau False
    return (MultishotK $ cgAssign tau cv, f cv)

splitOneshot MultishotK{} =
    fail "splitOneshot: cannot split a multishot continuation"

splitOneshot MultishotBindK{} =
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
    cv <- cgBinder (bVar bv) tau False
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

calign, _crestrict, cstatic :: C.TypeQual
calign     = C.EscTypeQual "ALIGN" noLoc
_crestrict = C.EscTypeQual "RESTRICT" noLoc
cstatic    = C.EscTypeQual "STATIC" noLoc

compileProgram :: IsLabel l => Program l -> KZC [C.Definition]
compileProgram = evalCg . cgProgram

cgProgram :: forall l . IsLabel l => Program l -> Cg l ()
cgProgram (Program _imports decls maybe_main) = do
    Main comp tau <- maybe (fail "No main computation!")
                           return
                           maybe_main
    appendTopDef [cedecl|$esc:("#include <kz.h>")|]
    appendTopDecl [cdecl|typename kz_buf_t $id:in_buf;|]
    appendTopDecl [cdecl|typename kz_buf_t $id:out_buf;|]
    (clabels, cblock) <-
        collectLabels $
        inNewCodeBlock_ $
        cgDecls decls $ do
        -- Allocate and initialize input and output buffers
        (_, _, a, b) <- checkST tau
        cgInitInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgInitOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
        -- Create storage for the result
        cdone <- cgTopCTemp tau "done" [cty|int|] (Just [cinit|0|])
        cres  <- cgTemp "main_res" (resultType tau)
        -- The done continuation simply puts the computation's result in cres
        let exitk = do whenUsesConsumerThread $
                         appendStm [cstm|$cdone = 1;|]
                       appendStm [cstm|BREAK;|]
        cgTimed $
            withGuardTakeK guardtakek $
            withTakeK  takek $
            withTakesK takesk $
            withEmitK  emitk $
            withEmitsK emitsk $
            withExitK  exitk $
            cgThread tau comp $
            multishot$ \ce -> do
              cgAssign (resultType tau) cres ce
              whenUsesConsumerThread $ do
                cgMemoryBarrier
                appendStm [cstm|$cdone = 1;|]
              appendStm [cstm|BREAK;|]
        -- Generate code to initialize threads
        cgInitThreads comp
        whenUsesConsumerThread $
          -- Wait for result
          appendThreadCleanupStm [cstm|while (!$cdone);|]
        -- Clean up input and output buffers
        cgCleanupInput  a (CExp [cexp|$id:params|]) (CExp [cexp|$id:in_buf|])
        cgCleanupOutput b (CExp [cexp|$id:params|]) (CExp [cexp|$id:out_buf|])
    cgLabels clabels
    appendTopFunDef [cedecl|
void kz_main(const typename kz_params_t* $id:params)
{
    $items:(toBlockItems cblock)
}|]
    dumpStats <- asksConfig (testDynFlag ShowCgStats)
    when dumpStats $ do
        stats  <- getStats
        liftIO $ putDocLn $ nest 2 $
            text "Code generator statistics:" </> ppr stats
  where
    in_buf, out_buf, params :: C.Id
    in_buf  = "in"
    out_buf = "out"
    params = "params"

    guardtakek :: GuardTakeK l
    guardtakek = return ()

    takek :: TakeK l
    takek tau _klbl k = do
        -- Generate a pointer to the current element in the buffer.
        ctau   <- cgType tau
        cbuf   <- cgThreadCTemp tau "take_bufp" [cty|$tyqual:calign const $ty:ctau*|] (Just [cinit|NULL|])
        cinput <- cgInput tau (CExp [cexp|$id:in_buf|]) 1
        if [cexp|($cbuf = (const $ty:ctau*) $cinput) == NULL|]
          then cgExit
          else return ()
        go tau cbuf
      where
        go tau cbuf
          | isBitT tau    = k $ CExp [cexp|*$cbuf & 1|]
          | isBitArrT tau = k $ CBitSlice $ CExp [cexp|*$cbuf|]
          | otherwise     = k $ CExp [cexp|*$cbuf|]

    takesk :: TakesK l
    takesk n tau _klbl k = do
        -- Generate a pointer to the current element in the buffer.
        ctau   <- cgType tau
        cbuf   <- cgThreadCTemp tau "take_bufp" [cty|$tyqual:calign const $ty:ctau*|] (Just [cinit|NULL|])
        cinput <- cgInput tau (CExp [cexp|$id:in_buf|]) (fromIntegral n)
        if [cexp|($cbuf = (const $ty:ctau*) $cinput) == NULL|]
          then cgExit
          else return ()
        go tau cbuf
      where
        go tau cbuf
          | isBitT tau = k $ CBitSlice $ CExp [cexp|$cbuf|]
          | otherwise  = k $ CExp [cexp|$cbuf|]

    emitk :: EmitK l
    emitk tau ce _klbl k = do
        ceAddr <- cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceAddr
        k

    emitsk :: EmitsK l
    emitsk n tau ce _klbl k = do
        ceAddr <- cgAddrOf (arrT n tau) ce
        cgOutput (arrT n tau) (CExp [cexp|$id:out_buf|]) 1 ceAddr
        k

    cgInitInput :: Type -> CExp l -> CExp l -> Cg l ()
    cgInitInput = cgBufferInit "kz_init_input"

    cgInitOutput :: Type -> CExp l -> CExp l -> Cg l ()
    cgInitOutput = cgBufferInit "kz_init_output"

    cgCleanupInput :: Type -> CExp l -> CExp l -> Cg l ()
    cgCleanupInput = cgBufferCleanup "kz_cleanup_input"

    cgCleanupOutput :: Type -> CExp l -> CExp l -> Cg l ()
    cgCleanupOutput = cgBufferCleanup "kz_cleanup_output"

    cgBufferInit :: String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferInit = cgBufferConfig appendThreadInitStm

    cgBufferCleanup :: String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferCleanup = cgBufferConfig appendThreadCleanupStm

    cgBufferConfig :: (C.Stm -> Cg l ()) -> String -> Type -> CExp l -> CExp l -> Cg l ()
    cgBufferConfig appStm f tau cp cbuf = go tau
      where
        go :: Type -> Cg l ()
        go (ArrT _ tau _)     = go tau
        go tau | isBitT tau   = appStm [cstm|$id:(fname "bit")($cp, &$cbuf);|]
        go (IntT IDefault  _) = appStm [cstm|$id:(fname "int")($cp, &$cbuf);|]
        go (IntT (I 8)  _)    = appStm [cstm|$id:(fname "int8")($cp, &$cbuf);|]
        go (IntT (I 16) _)    = appStm [cstm|$id:(fname "int16")($cp, &$cbuf);|]
        go (IntT (I 32) _)    = appStm [cstm|$id:(fname "int32")($cp, &$cbuf);|]
        go (IntT UDefault  _) = appStm [cstm|$id:(fname "uint")($cp, &$cbuf);|]
        go (IntT (U 8)  _)    = appStm [cstm|$id:(fname "uint8")($cp, &$cbuf);|]
        go (IntT (U 16) _)    = appStm [cstm|$id:(fname "uint16")($cp, &$cbuf);|]
        go (IntT (U 32) _)    = appStm [cstm|$id:(fname "uint32")($cp, &$cbuf);|]
        go tau@IntT{}         = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                          text "are not supported."
        go (FloatT FP16 _)    = appStm [cstm|$id:(fname "float")($cp, &$cbuf);|]
        go (FloatT FP32 _)    = appStm [cstm|$id:(fname "float")($cp, &$cbuf);|]
        go (FloatT FP64 _)    = appStm [cstm|$id:(fname "double")($cp, &$cbuf);|]

        go tau_struct@StructT{} = do
            maybe_tau <- runMaybeT $ checkComplexT tau_struct
            case maybe_tau of
              Just tau | tau == int16T -> appStm [cstm|$id:(fname "complex16")($cp, &$cbuf);|]
                       | tau == int32T -> appStm [cstm|$id:(fname "complex32")($cp, &$cbuf);|]
              _                        -> appStm [cstm|$id:(fname "bytes")($cp, &$cbuf);|]

        go _ =
            appStm [cstm|$id:(fname "bytes")($cp, &$cbuf);|]

        fname :: String -> C.Id
        fname t = fromString (f ++ "_" ++ t)

    cgInput :: Type -> CExp l -> CExp l -> Cg l (CExp l)
    cgInput tau cbuf cn = go tau
      where
        go :: Type -> Cg l (CExp l)
        go (ArrT n tau _)    = do ci <- cgNatType n
                                  cgInput tau cbuf (cn*ci)
        go tau | isBitT tau  = return $ CExp [cexp|kz_input_bit(&$cbuf, $cn)|]
        go (IntT IDefault _) = return $ CExp [cexp|kz_input_int(&$cbuf, $cn)|]
        go (IntT (I 8)  _)   = return $ CExp [cexp|kz_input_int8(&$cbuf, $cn)|]
        go (IntT (I 16) _)   = return $ CExp [cexp|kz_input_int16(&$cbuf, $cn)|]
        go (IntT (I 32) _)   = return $ CExp [cexp|kz_input_int32(&$cbuf, $cn)|]
        go (IntT UDefault _) = return $ CExp [cexp|kz_input_uint(&$cbuf, $cn)|]
        go (IntT (U 8)  _)   = return $ CExp [cexp|kz_input_uint8(&$cbuf, $cn)|]
        go (IntT (U 16) _)   = return $ CExp [cexp|kz_input_uint16(&$cbuf, $cn)|]
        go (IntT (U 32) _)   = return $ CExp [cexp|kz_input_uint32(&$cbuf, $cn)|]
        go tau@IntT{}        = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                         text "are not supported."
        go (FloatT FP16 _)   = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT FP32 _)   = return $ CExp [cexp|kz_input_float(&$cbuf, $cn)|]
        go (FloatT FP64 _)   = return $ CExp [cexp|kz_input_double(&$cbuf, $cn)|]
        go (TyVarT alpha _)  = lookupTyVarType alpha >>= go

        go tau_struct@StructT{} = do
            maybe_tau <- runMaybeT $ checkComplexT tau_struct
            case maybe_tau of
              Just tau | tau == int16T -> return $ CExp [cexp|kz_input_complex16(&$cbuf, $cn)|]
                       | tau == int32T -> return $ CExp [cexp|kz_input_complex32(&$cbuf, $cn)|]
              _                        -> do ctau <- cgType tau
                                             return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

        go tau = do
            ctau <- cgType tau
            return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

    cgOutput :: Type -> CExp l -> CExp l -> CExp l -> Cg l ()
    cgOutput tau cbuf cn cval = go tau
      where
        go :: Type -> Cg l ()
        go (ArrT n tau _)     = do ci <- cgNatType n
                                   cgOutput tau cbuf (cn*ci) cval
        go tau | isBitT tau   = appendStm [cstm|kz_output_bit(&$cbuf, $cval, $cn);|]
        go (IntT IDefault  _) = appendStm [cstm|kz_output_int(&$cbuf, $cval, $cn);|]
        go (IntT (I 8)  _)    = appendStm [cstm|kz_output_int8(&$cbuf, $cval, $cn);|]
        go (IntT (I 16) _)    = appendStm [cstm|kz_output_int16(&$cbuf, $cval, $cn);|]
        go (IntT (I 32) _)    = appendStm [cstm|kz_output_int32(&$cbuf, $cval, $cn);|]
        go (IntT UDefault  _) = appendStm [cstm|kz_output_uint(&$cbuf, $cval, $cn);|]
        go (IntT (U 8)  _)    = appendStm [cstm|kz_output_uint8(&$cbuf, $cval, $cn);|]
        go (IntT (U 16) _)    = appendStm [cstm|kz_output_uint16(&$cbuf, $cval, $cn);|]
        go (IntT (U 32) _)    = appendStm [cstm|kz_output_uint32(&$cbuf, $cval, $cn);|]
        go tau@IntT{}         = faildoc $ text "Buffers with values of type" <+> ppr tau <+>
                                          text "are not supported."
        go (FloatT FP16 _)    = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT FP32 _)    = appendStm [cstm|kz_output_float(&$cbuf, $cval, $cn);|]
        go (FloatT FP64 _)    = appendStm [cstm|kz_output_double(&$cbuf, $cval, $cn);|]
        go (TyVarT alpha _)   = lookupTyVarType alpha >>= go

        go tau_struct@StructT{} = do
            maybe_tau <- runMaybeT $ checkComplexT tau_struct
            case maybe_tau of
              Just tau | tau == int16T -> appendStm [cstm|kz_output_complex16(&$cbuf, $cval, $cn);|]
                       | tau == int32T -> appendStm [cstm|kz_output_complex32(&$cbuf, $cval, $cn);|]
              _                        -> do ctau <- cgType tau
                                             appendStm [cstm|kz_output_bytes(&$cbuf, $cval, $cn*sizeof($ty:ctau));|]

        go tau = do
            ctau <- cgType tau
            appendStm [cstm|kz_output_bytes(&$cbuf, $cval, $cn*sizeof($ty:ctau));|]

cgInitThreads :: Located a => a -> Cg l ()
cgInitThreads x =
    getThreads >>= mapM_ cgInitThread
  where
    cgInitThread :: Thread l -> Cg l ()
    cgInitThread t =
      cgInitCheckErr [cexp|kz_thread_init(&$(threadInfo t),
                                          &$(thread t),
                                          $id:(threadFun t))|]
                     "Cannot create thread."
                     x

cgTimed :: forall l a . Cg l a -> Cg l a
cgTimed m = do
    flags <- askConfig
    go flags
  where
    go :: Config -> Cg l a
    go flags | testDynFlag Timers flags = do
        cpu_time_start  :: C.Id <- gensym "cpu_time_start"
        cpu_time_end    :: C.Id <- gensym "cpu_time_end"
        real_time_start :: C.Id <- gensym "real_time_start"
        real_time_end   :: C.Id <- gensym "real_time_end"
        appendTopDecl [cdecl|static long double $id:cpu_time_start, $id:cpu_time_end;|]
        appendTopDecl [cdecl|static long double $id:real_time_start, $id:real_time_end;|]
        appendStm [cstm|$id:cpu_time_start = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_start = kz_get_real_time();|]
        x <- m
        appendStm [cstm|$id:cpu_time_end = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_end = kz_get_real_time();|]
        appendStm [cstm|printf("Time elapsed (usec): %d\n", (int) (($id:cpu_time_end - $id:cpu_time_start) * 1000000));|]
        appendStm [cstm|printf("Elapsed cpu time (sec): %Le\n", $id:cpu_time_end - $id:cpu_time_start);|]
        appendStm [cstm|printf("Elapsed real time (sec): %Le\n", $id:real_time_end - $id:real_time_start);|]
        return x

    go _flags =
        m

cgLabels :: forall l . IsLabel l => Set l -> Cg l ()
cgLabels ls =
    unless (Set.null ls) $ do
      appendTopDef [cedecl|$esc:("#if !defined(FIRSTCLASSLABELS)")|]
      appendTopDef [cedecl|enum { $enums:(cls) };|]
      appendTopDef [cedecl|$esc:("#endif /* !defined(FIRSTCLASSLABELS) */")|]
  where
    cls :: [C.CEnum]
    cls = [[cenum|$id:l|] | l <- Set.toList ls]

-- | Generate code to check return value of a function call.
cgInitCheckErr :: Located a => C.Exp -> String -> a -> Cg l ()
cgInitCheckErr ce msg x =
    appendThreadInitStm [cstm|kz_check_error($ce, $string:(renderLoc x), $string:msg);|]

-- | Generate code to check return value of a function call.
cgCheckErr :: Located a => C.Exp -> String -> a -> Cg l ()
cgCheckErr ce msg x =
    appendStm [cstm|kz_check_error($ce, $string:(renderLoc x), $string:msg);|]

cgThread :: IsLabel l
         => Type     -- ^ Type of the result of the computation
         -> Comp l   -- ^ Computation to compiled
         -> Kont l a -- ^ Code generator to deal with result of computation
         -> Cg l a
cgThread tau comp k = do
    (cblock, x) <-
        inSTScope tau $
        inLocalScope $
        inNewCodeBlock $ do
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
        cgComp comp l_done $ oneshot tau $ runKont k
    appendDecls (toList (blockDecls cblock))
    appendStms [cstms|$stms:(toList (blockInitStms cblock))
                      BEGIN_DISPATCH;
                      $stms:(toList (blockStms cblock))
                      END_DISPATCH;
                      $stms:(toList (blockCleanupStms cblock))
                     |]
    return x
  where
    cUR_KONT :: C.Id
    cUR_KONT = "curk"

cgDecls :: IsLabel l => [Decl l] -> Cg l a -> Cg l a
cgDecls decls k = foldr cgDecl k decls

cgDecl :: forall l a . IsLabel l => Decl l -> Cg l a -> Cg l a
cgDecl decl@(StructD s [] flds l) k = do
    withSummaryContext decl $ do
        cflds <- mapM cgField flds
        appendTopDecl $ rl l [cdecl|typedef struct $id:(cstruct s l) { $sdecls:cflds } $id:(cstruct s l);|]
    extendStructs [StructDef s [] flds l] k
  where
    cgField :: (Field, Type) -> Cg l C.FieldGroup
    cgField (fld, tau) = do
        ctau <- cgType tau
        return [csdecl|$ty:ctau $id:(cfield fld);|]

cgDecl decl@StructD{} _k =
    withSummaryContext decl $
    faildoc $ text "Cannot compile polymorphic structs."

cgDecl (LetD decl _) k = do
    flags <- askConfig
    cgLocalDecl flags decl k

cgDecl decl@(LetFunD f tvks vbs tau_ret e l) k =
    extendVars [(bVar f, tau)] $ do
    cf <- cvar f
    extendVarCExps [(bVar f, CExp [cexp|$id:cf|])] $ do
      appendTopComment (ppr f <+> colon <+> align (ppr tau))
      withSummaryContext decl $
          extendLetFun f tvks vbs tau_ret $ do
          let nats          =  map fst tvks
          (cnats, cparams1) <- unzip <$> mapM cgNatTyVar nats
          (cvbs,  cparams2) <- unzip <$> mapM cgVarBind vbs
          cres_ident        <- gensym "let_res"
          cblock <- inNewCodeBlock_ $
                    extendTyVarCExps (nats `zip` cnats) $
                    extendVarCExps  (map fst vbs `zip` cvbs) $ do
                    cres <- if isReturnedByRef tau_res
                            then return $ CExp [cexp|$id:cres_ident|]
                            else cgTemp "let_res" tau_res
                    cgExp e $ multishotBind tau_res cres
                    when (not (isUnitT tau_res) && not (isReturnedByRef tau_res)) $
                        appendStm $ rl l [cstm|return $cres;|]
          if isReturnedByRef tau_res
            then do cretparam <- cgRetParam tau_res (Just cres_ident)
                    appendTopFunDef $ rl l [cedecl|static void $id:cf($params:(cparams1 ++ cparams2 ++ [cretparam])) { $items:(toBlockItems cblock) }|]
            else do ctau_res <- cgType tau_res
                    appendTopFunDef $ rl l [cedecl|static $ty:ctau_res $id:cf($params:(cparams1 ++ cparams2)) { $items:(toBlockItems cblock) }|]
      k
  where
    tau_res :: Type
    tau_res = resultType tau_ret

    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

cgDecl decl@(LetExtFunD f tvks vbs tau_ret l) k =
    extendExtFuns [(bVar f, tau)] $
    extendVarCExps [(bVar f, CExp [cexp|$id:cf|])] $ do
    appendTopComment (ppr f <+> colon <+> align (ppr tau))
    withSummaryContext decl $ do
        -- External functions are only be polymorphic in types of kind nat.
        let nats      =  map fst tvks
        (_, cparams1) <- unzip <$> mapM cgNatTyVar nats
        (_, cparams2) <- unzip <$> mapM cgVarBind vbs
        if isReturnedByRef tau_res
          then do cretparam <- cgRetParam tau_res Nothing
                  appendTopFunDef $ rl l [cedecl|void $id:cf($params:(cparams1 ++ cparams2 ++ [cretparam]));|]
          else do ctau_ret <- cgType tau_res
                  appendTopFunDef $ rl l [cedecl|$ty:ctau_ret $id:cf($params:(cparams1 ++ cparams2));|]
    k
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

    tau_res :: Type
    tau_res = resultType tau_ret

    cf :: C.Id
    cf = C.Id ("__kz_" ++ namedString f) l

cgDecl (LetCompD v tau comp _) k =
    extendVars [(bVar v, tau)] $
    extendVarCExps [(bVar v, CComp compc)] k
  where
    -- Compile a bound computation. This will be called in some future
    -- context. It may be called multiple times, so we need to create a copy of
    -- the computation with fresh labels before we compile it.
    compc :: forall a . CompC l a
    compc klbl k =
        withInstantiatedTyVars tau $ do
        comp' <- traverse uniquify comp
        useLabels (compUsedLabels comp')
        cgComp comp' klbl k

cgDecl (LetFunCompD f tvks vbs tau_ret comp l) k =
    extendVars [(bVar f, tau)] $
    extendVarCExps [(bVar f, CFunComp funcompc)] k
  where
    tau :: Type
    tau = funT tvks (map snd vbs) tau_ret l

    -- Compile a bound computation function given its arguments. This will be
    -- called in some future context. It may be called multiple times, so we
    -- need to create a copy of the body of the computation function with fresh
    -- labels before we compile it.
    funcompc :: forall a . FunCompC l a
    funcompc _taus es klbl k =
        withInstantiatedTyVars tau_ret $ do
        comp'      <- traverse uniquify comp
        let nats   =  map fst tvks
        (cnats, _) <- unzip <$> mapM cgNatTyVar (map fst tvks)
        ces        <- mapM cgArg es
        extendTyVars tvks $
          extendVars  vbs $
          extendTyVarCExps (nats `zip` cnats) $
          extendVarCExps   (map fst vbs `zip` ces) $ do
          useLabels (compUsedLabels comp')
          cgComp comp' klbl k
      where
        cgArg :: Arg l -> Cg l (CExp l)
        cgArg (ExpA e) =
            withFvContext e $
            cgExpOneshot e

        cgArg (CompA comp) =
            return $ CComp compc
          where
            compc :: forall a . CompC l a
            compc = cgComp comp

cgLocalDecl :: forall l a . IsLabel l => Config -> LocalDecl -> Cg l a -> Cg l a
cgLocalDecl flags decl@(LetLD v tau e0@(GenE e gs _) _) k | testDynFlag ComputeLUTs flags =
    withSummaryContext decl $ do
    appendComment $ text "Lut:" </> ppr e0
    cv <- cgBinder (bVar v) tau False
    extendVars [(bVar v, tau)] $
      extendVarCExps [(bVar v, cv)] $ do
      e'     <- lutGenToExp (bVar v) e gs
      citems <- inLocalScope $ inNewBlock_ $ cgExp e' $ multishot cgVoid
      appendStm [cstm|{ $items:citems }|]
      k

cgLocalDecl _flags decl@(LetLD v tau e _) k =
    withSummaryContext decl $
    cgExp e $
    cgLetBinding v tau $ \cv ->
    extendVars [(bVar v, tau)] $
    extendVarCExps [(bVar v, cv)] k

cgLocalDecl _flags decl@(LetRefLD v tau maybe_e _) k =
    withSummaryContext decl $
    cgLetRefBinding v tau maybe_e $ \cve ->
    extendVars [(bVar v, refT tau)] $
    extendVarCExps [(bVar v, cve)] k

cgLocalDecl _flags LetViewLD{} _k =
    faildoc $ text "Views not supported."

-- | Generate a 'CExp' representing a constant. The 'CExp' produced is
-- guaranteed to be a legal C initializer, so it can be used in an array or
-- struct initializer.
cgConst :: forall l . Const -> Cg l (CExp l)
cgConst UnitC        = return CVoid
cgConst (BoolC b)    = return $ CBool b
cgConst (IntC _ x)   = return $ CInt (fromIntegral x)
cgConst (FloatC _ f) = return $ CFloat (toRational f)
cgConst (StringC s)  = return $ CExp [cexp|$string:s|]

cgConst c@(ArrayC cs) = do
    (_, tau) <- inferConst noLoc c >>= checkArrT
    ces      <- V.toList <$> V.mapM cgConst cs
    return $ CInit [cinit|{ $inits:(cgArrayNatTnits tau ces) }|]

cgConst (ReplicateC n c) = do
    tau    <- inferConst noLoc c
    c_dflt <- defaultValueC tau
    ce     <- cgConst c
    return $
      if c == c_dflt
      then CInit [cinit|{ $init:(toInitializer ce) }|]
      else CInit [cinit|{ $inits:(cgArrayNatTnits tau (replicate n ce)) }|]

cgConst (EnumC tau) =
    cgConst =<< ArrayC <$> enumType tau

cgConst (StructC struct taus flds) = do
    fldDefs <- lookupStructFields struct taus
    -- We must be careful to generate initializers in the same order as the
    -- struct's fields are declared, which is why we map 'cgField' over the
    -- struct's field definitions rather than mapping it over the values as
    -- declared in @flds@
    cinits <- mapM (cgField flds . fst) fldDefs
    return $ CInit [cinit|{ $inits:cinits }|]
  where
    cgField :: [(Field, Const)] -> Field -> Cg l C.Initializer
    cgField flds f = do
        ce <- case lookup f flds of
                Nothing -> panicdoc $ text "cgField: missing field"
                Just c -> cgConst c
        return $ toInitializer ce

cgArrayNatTnits :: forall l . Type -> [CExp l] -> [C.Initializer]
cgArrayNatTnits tau ces | isBitT tau =
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
    const ce       = toInitializer ce

cgArrayNatTnits _tau ces =
    map toInitializer ces

{- Note [Bit Arrays]

We represent bit arrays as C arrays of type `bIT_ARRAY_ELEM_TYPE`, which has
size `bIT_ARRAY_ELEM_BITS`, where the least significant bit is 0 and the least
significant group of bits is element 0 of the C array. We must be careful when
the size of the bit array is not zero module `bIT_ARRAY_ELEM_BITS`; in this
case, there are "zombie bits" in the representation. This leads to two problems:

  1. When using the `CExp` as a source, we may need to mask out the zombie bits.

  2. When using the `CExp` as a destination, we need to be sure not to overwrite
  the zombie bits, because the expression may be a slice of a larger array!

We attempt to solve this by imposing the following invariants:

  1. Zombie bits are only assigned to if they are truly zombie bits, i.e., if
  the destination is a slice, the "zombie" bits may be non-zombie bits in the
  sliced array!

  2. Zombie bits are always zero.

Maintaining these invariants requires the following:

  1. Even if a bit array is marked as not needing a default value, we still
  initialize any zombie bits to zero. See `cgInitAlways`.

  2. During assignment, we only assign to the zombie bits if the destination is
  not a slice. This guarantees we only overwrite true zombie bits.

  3. During assignment, if the source is a slice, we mask off the zombie bits.
  This ensures that the rhs of the assignment has only zombie bits whose values
  are zero.

Bit arrays that may be slices are marked using the `CBitSlice` data constructor.
Note that function arguments may also be bit array slices; such arguments are
marked with either `CPtr` or `CBitSlice` data constructor in `cgVarBind`.

We used to always mask off extraneous bits, but these extra masks can lead to
not insignificant performance degradation.
-}

{- Note [Declaration Scopes]

Originally, all variable declarations were placed at the top of the enclosing
function's body except for the special case of index variables for pure loops,
i.e., 'ForE' loops. We now make a serious effort to minimize the scope of a
declaration. Hopefully this will make the C compiler's job easier and will lead
to less stack space being used.

The complication is that we use labels. Consider the following quote from the
C11 standard, 6.8.6.1p1:

    The identifier in a goto statement shall name a label located somewhere in
    the enclosing function. A goto statement shall not jump from outside the
    scope of an identifier having a variably modified type to inside the scope
    of that identifier.

Therefore, any variable with two uses separated by a label that can be targeted
from outside the block containing /all/ uses of the variable must be declared at
the beginning of the function's body. We enforce a slightly different invariant:
any variable with two uses separated by a label will be declared at the
beginning of the function's body.

We maintain this invariant by tracking the set of declared identifiers (in the
'declared' field of 'CgState'), the set of identifiers that have been used (in
'used'), the set of identifiers that are out of scope by virtue of an
intervening label that occurred after their declaration ('outOfScope'), and the
set of identifiers that have been used after they went out of scope
('usedOutOfScope'). The current set of declarations is marked out of scope by
virtue of an intervening label by calling 'newLabelScope'.

When we collect declarations and statements to create a new block of code,
declarations for identifiers that were used after they were makred out of scope
are automatically promoted to thread-level declarations.

A new block of code that collects declarations is constructed with 'newScope',
which transparently collects code generated by its computation argument and adds
it as a single block.

When do we need to call 'newBlock'? Right after we have called 'newLocalScope',
i.e., after we have generated a label that will be the target of some goto. Most
of the time this is taken care of automatically by 'cgWithLabel', but we need to
manually call 'newScope' after generating code for loops that call cgLabel.

One special case is 'cgIf'. We want to insert /as few/ calls to newScope as
possible, so that declarations are group together when possible. However, we
can't move any declaration past a label. Therefore, we need to call 'newScope'
so that it scopes over any code generated immediately after a label, but not
more often than that. For 'cgIf', we call a continuation once after generating
the if, not once for each branch, so the code generators for each branch don't
scope over the if's code generating continuation, so any call to 'newScope' will
not scope over the if's continuation. Therefore, we test the if statement we
construct to see if it contains any labels, using 'hasLabel'. If it does, we
call 'newScope'; otherwise, we don't.
-}


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
dereference may actually be a reference to the dereferenced expression, i.e., a
source language dereference may just be a pointer to the original ref!

How do we manage to still adhere to the language's semantics? The semantics say
that the left and right halves of a par must have disjoint sets of free ref
variables. The type checker checks this property, but to properly enforce it, we
must also check that /calls/ to computation functions do not have arguments that
alias.

The tricky bit is that we may dereference a value and then either use this
dereferenced value in a call to a computation function, passing it along with
the original ref as an argument, or we may use both the original ref and the
dereferenced value in different halves of a par. If we avoid copying on
dereference, we've now violated the semantics! Consider this example, where
@foo@ is a computation function:

@
(y : struct complex32[32]) <- !x
foo(x, y);
@

If we try to be too smart in the code generator, x and y will alias!

Fortunately, the ref flow analysis takes care of this. In a call to a
computation, it marks ref arguments as modified /before/ using any of the
arguments. This way, when y is "used", we see that its source "x", was
"modified", so we actually copy x into y before calling foo. For regular
functions, we allow aliasing, so we don't need to perform the copy.

For par, if either the left or right branch modifies a ref, then we need to see
it as having been modified in both branches. Therefore, when performing the ref
data flow analysis, we look at both branches, collect the set of modified refs,
and then, if these sets overlap, go back and examine both branches again to
check for variables that are used after their source ref was modified. Consider
this example:

@
(y : struct complex32[32]) <- !x
{computation using y} >>> {computation using x};
@

If the right branch writes to x, then we need to make a copy in y. If it
/doesn't/ modify x, then we don't need to make the copy! But if we analyze the
left branch first in isolation, we don't know that y is potentially used after x
is modified. That's why we need to collect the sets of modified refs from /both
branches/ and test for overlap.

Regardless, we must be sure to insert a memory barrier before launching threads
to make sure any changes to x are written before y is used.
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

-- | Return 'True' if the given 'CExp' is "simple", i.e., if it doesn't cause
-- any work to be done.
isSimple :: CExp l -> Bool
isSimple CVoid     = True
isSimple CBool{}   = True
isSimple CInt{}    = True
isSimple CFloat{}  = True
isSimple ce
    | isLvalue ce  = True
isSimple _         = False

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
        ce <- cgConst c
        cgConstExp e ce k

    go (VarE v _) k =
        lookupVarCExp v >>= runKont k

    go e0@(UnopE op e l) k = withSummaryContext e0 $ do
        tau       <- inferExp e
        ce        <- cgExpOneshot e
        maybe_tau <- runMaybeT $ checkComplexT tau
        case maybe_tau of
          Just{}  -> cgUnopComplex op ce >>= runKont k
          Nothing -> cgUnop op tau ce  >>= runKont k
      where
        cgUnop ::  Unop -> Type -> CExp l -> Cg l (CExp l)
        cgUnop (Cast tau_to) tau_from ce =
            cgCast ce tau_from tau_to

        cgUnop (Bitcast tau_to) tau_from ce =
            cgBitcast ce tau_from tau_to

        cgUnop Len (RefT (ArrT n _ _) _) _ =
            cgNatType n

        cgUnop Len (ArrT n _ _) _ =
            cgNatType n

        cgUnop Len _ _ =
            panicdoc $
            text "cgUnop: tried to take the length of a non-array type!"

        cgUnop Lnot _ ce = return $ CExp [cexp|!$ce|]

        cgUnop Bnot tau ce
          | isBitT tau = return $ CExp [cexp|!$ce|]
          | otherwise  = return $ CExp [cexp|~$ce|]

        cgUnop Neg _ ce = return $ CExp [cexp|-$ce|]

        cgUnop Abs IntT{}          ce = return $ CExp [cexp|abs($ce)|]
        cgUnop Abs (FloatT FP32 _) ce = return $ CExp [cexp|fabsf($ce)|]
        cgUnop Abs (FloatT FP64 _) ce = return $ CExp [cexp|fabs($ce)|]

        cgUnop Exp   (FloatT FP32 _) ce = return $ CExp [cexp|expf($ce)|]
        cgUnop Exp   (FloatT FP64 _) ce = return $ CExp [cexp|exp($ce)|]
        cgUnop Exp2  (FloatT FP32 _) ce = return $ CExp [cexp|exp2f($ce)|]
        cgUnop Exp2  (FloatT FP64 _) ce = return $ CExp [cexp|exp2($ce)|]
        cgUnop Expm1 (FloatT FP32 _) ce = return $ CExp [cexp|expm1f($ce)|]
        cgUnop Expm1 (FloatT FP64 _) ce = return $ CExp [cexp|expm1($ce)|]

        cgUnop Log   (FloatT FP32 _) ce = return $ CExp [cexp|logf($ce)|]
        cgUnop Log   (FloatT FP64 _) ce = return $ CExp [cexp|log($ce)|]
        cgUnop Log2  (FloatT FP32 _) ce = return $ CExp [cexp|log2f($ce)|]
        cgUnop Log2  (FloatT FP64 _) ce = return $ CExp [cexp|log2($ce)|]
        cgUnop Log1p (FloatT FP32 _) ce = return $ CExp [cexp|log1pf($ce)|]
        cgUnop Log1p (FloatT FP64 _) ce = return $ CExp [cexp|log1p($ce)|]

        cgUnop Sqrt (FloatT FP32 _) ce = return $ CExp [cexp|sqrtf($ce)|]
        cgUnop Sqrt (FloatT FP64 _) ce = return $ CExp [cexp|sqrt($ce)|]

        cgUnop Sin  (FloatT FP32 _) ce = return $ CExp [cexp|sinf($ce)|]
        cgUnop Sin  (FloatT FP64 _) ce = return $ CExp [cexp|sin($ce)|]
        cgUnop Cos  (FloatT FP32 _) ce = return $ CExp [cexp|cosf($ce)|]
        cgUnop Cos  (FloatT FP64 _) ce = return $ CExp [cexp|cos($ce)|]
        cgUnop Tan  (FloatT FP32 _) ce = return $ CExp [cexp|tanf($ce)|]
        cgUnop Tan  (FloatT FP64 _) ce = return $ CExp [cexp|tan($ce)|]
        cgUnop Asin (FloatT FP32 _) ce = return $ CExp [cexp|asinf($ce)|]
        cgUnop Asin (FloatT FP64 _) ce = return $ CExp [cexp|asin($ce)|]
        cgUnop Acos (FloatT FP32 _) ce = return $ CExp [cexp|acosf($ce)|]
        cgUnop Acos (FloatT FP64 _) ce = return $ CExp [cexp|acos($ce)|]
        cgUnop Atan (FloatT FP32 _) ce = return $ CExp [cexp|atanf($ce)|]
        cgUnop Atan (FloatT FP64 _) ce = return $ CExp [cexp|atan($ce)|]

        cgUnop Sinh  (FloatT FP32 _) ce = return $ CExp [cexp|sinhf($ce)|]
        cgUnop Sinh  (FloatT FP64 _) ce = return $ CExp [cexp|sinh($ce)|]
        cgUnop Cosh  (FloatT FP32 _) ce = return $ CExp [cexp|coshf($ce)|]
        cgUnop Cosh  (FloatT FP64 _) ce = return $ CExp [cexp|cosh($ce)|]
        cgUnop Tanh  (FloatT FP32 _) ce = return $ CExp [cexp|tanhf($ce)|]
        cgUnop Tanh  (FloatT FP64 _) ce = return $ CExp [cexp|tanh($ce)|]
        cgUnop Asinh (FloatT FP32 _) ce = return $ CExp [cexp|asinhf($ce)|]
        cgUnop Asinh (FloatT FP64 _) ce = return $ CExp [cexp|asinh($ce)|]
        cgUnop Acosh (FloatT FP32 _) ce = return $ CExp [cexp|acoshf($ce)|]
        cgUnop Acosh (FloatT FP64 _) ce = return $ CExp [cexp|acosh($ce)|]
        cgUnop Atanh (FloatT FP32 _) ce = return $ CExp [cexp|atanhf($ce)|]
        cgUnop Atanh (FloatT FP64 _) ce = return $ CExp [cexp|atanh($ce)|]

        cgUnop _ _ _ =
            faildoc $ text "Cannot compile operator."

        cgUnopComplex :: Unop ->  CExp l -> Cg l (CExp l)
        cgUnopComplex Neg ce = do
            (a, b) <- unComplex ce
            cgComplex (-a) (-b)

        cgUnopComplex op _ce =
            panicdoc $ text "Illegal operation on complex value:" <+> ppr op

        cgCast :: CExp l -> Type -> Type -> Cg l (CExp l)
        cgCast ce _ tau_to | isBitT tau_to =
            return $ CExp $ rl l [cexp|$ce > 0 ? 1 : 0|]

        cgCast ce _ tau_to = do
            ctau_to <- cgType tau_to
            return $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

        cgBitcast :: CExp l -> Type -> Type -> Cg l (CExp l)
        cgBitcast ce tau_from tau_to | tau_to == tau_from =
            return ce

        cgBitcast ce tau_from tau_to@(IntT U{} _) | isBitArrT tau_from = do
            cbits   <- cgBits tau_from ce
            ctau_to <- cgType tau_to
            return $ CExp $ rl l [cexp|($ty:ctau_to) $cbits|]

        cgBitcast ce tau_from@(IntT U{} _) tau_to | isBitArrT tau_to = do
            ctau_to <- cgBitcastType tau_from
            return $ CBits $ CExp $ rl l [cexp|($ty:ctau_to) $ce|]

        -- When casting a bit array to a Bool, we need to mask off the high
        -- bits, which are left undefined!
        cgBitcast ce tau_from tau_to@BoolT{} | isBitArrT tau_from = do
            ctau_to   <- cgType tau_to
            caddr     <- cgAddrOf tau_from ce
            return $ CExp $ rl l [cexp|*(($ty:ctau_to*) $caddr) & 0x1|]

        cgBitcast ce tau_from tau_to = do
            ctau_to <- cgType tau_to
            caddr   <- cgAddrOf tau_from ce
            return $ CExp $ rl l [cexp|*(($ty:ctau_to*) $caddr)|]

    go e0@(BinopE op e1 e2 l) k = withSummaryContext e0 $ do
        tau <- inferExp e1
        ce1 <- cgExpOneshot e1
        ce2 <- cgExpOneshot e2
        maybe_tau <- runMaybeT $ checkComplexT tau
        case maybe_tau of
          Just{}  -> cgBinopComplex ce1 ce2 op >>= runKont k
          Nothing -> cgBinop tau ce1 ce2 op >>= runKont k
      where
        cgBinop :: Type -> CExp l -> CExp l -> Binop -> Cg l (CExp l)
        cgBinop _ ce1 ce2 Lt   = return $ CExp $ rl l [cexp|$ce1 <  $ce2|]
        cgBinop _ ce1 ce2 Ne   = return $ CExp $ rl l [cexp|$ce1 != $ce2|]
        cgBinop _ ce1 ce2 Le   = return $ CExp $ rl l [cexp|$ce1 <= $ce2|]
        cgBinop _ ce1 ce2 Eq   = return $ CExp $ rl l [cexp|$ce1 == $ce2|]
        cgBinop _ ce1 ce2 Ge   = return $ CExp $ rl l [cexp|$ce1 >= $ce2|]
        cgBinop _ ce1 ce2 Gt   = return $ CExp $ rl l [cexp|$ce1 >  $ce2|]
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
                (n, _) <- inferExp e >>= checkArrT
                n      <- cgConstNatType n
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

        cgBinopComplex :: CExp l -> CExp l -> Binop -> Cg l (CExp l)
        cgBinopComplex ce1 ce2 Eq = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            return $ CExp $ rl l [cexp|$a == $c && $b == $d|]

        cgBinopComplex ce1 ce2 Ne = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            return $ CExp $ rl l [cexp|$a != $c || $b != $d|]

        cgBinopComplex ce1 ce2 Add = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            cgComplex (a+c) (b+d)

        cgBinopComplex ce1 ce2 Sub = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            cgComplex (a-c) (b-d)

        cgBinopComplex ce1 ce2 Mul = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            cgComplex (a*c - b*d) (b*c + a*d)

        cgBinopComplex ce1 ce2 Div = do
            (a, b) <- unComplex ce1
            (c, d) <- unComplex ce2
            cgComplex ((a*c + b*d)/(c*c + d*d)) ((b*c - a*d)/(c*c + d*d))

        cgBinopComplex _ce1 _ce2 op =
            panicdoc $ text "Illegal operation on complex values:" <+> ppr op

    go (IfE e1 e2 e3 _) k = do
        tau <- inferExp e2
        cgIf tau e1 (cgExp e2) (cgExp e3) k

    go (LetE decl e _) k = do
        flags <- askConfig
        cgLocalDecl flags decl $
          cgExp e k

    go (CallE f taus es l) k = do
        (tvks, _, tau_ret) <- lookupVar f >>= unFunT
        let tau_res        =  resultType tau_ret
        cf                 <- lookupVarCExp f
        let nats           =  map fst tvks
        cnats              <- mapM cgNatType taus
        ces                <- mapM cgArg es
        if isReturnedByRef tau_res
          then extendTyVarCExps (nats `zip` cnats) $ do
               (cres, k') <- splitMultishotBind "call_res" tau_res True k
               appendStm $ rl l [cstm|$cf($args:cnats, $args:(ces ++ [cres]));|]
               k'
          else runKont k $ CExp [cexp|$cf($args:cnats, $args:ces)|]
      where
        cgArg :: Exp -> Cg l (CExp l)
        cgArg e = do
            tau <- inferExp e
            go tau
          where
            go :: Type -> Cg l (CExp l)
            go tau@ArrT{} =
                cgExp e $ oneshot tau $ cgAddrOf tau

            go tau | isPassByRef tau =
                cgExp e $ oneshot tau $ cgAddrOf tau

            go tau =
                cgExpOneshot e >>= cgLower tau

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
        cgLoop Nothing $
            cgWhile l e_test $
            cgExpOneshot e_body
        runKont k CVoid

    go (ForE _ v v_tau gint e_body l) k = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars [(v, v_tau)] $
            extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
            appendDecl $ rl l [cdecl|$ty:cv_tau $id:cv;|]
            cgLoop Nothing $ do
                useCId cv
                (ce_start, ce_test) <- cgGenInterval gint
                citems              <- inNewBlock_ $ cgExpVoid e_body
                appendStm $ rl l [cstm|for ($id:cv = $ce_start;
                                            $(ce_test cv);
                                            $id:cv++) {
                                         $items:citems
                                       }|]
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
            appendDecl $ rl l [cdecl|$tyqual:calign $ty:ctau $id:cv[$int:(length es)];|]
            forM_ (es `zip` [(0::Integer)..]) $ \(e,i) -> do
                ce <- cgExpOneshot e
                cgAssign (refT tau) (CIdx tau (CExp [cexp|$id:cv|]) (fromIntegral i)) ce
            runKont k $ CExp [cexp|$id:cv|]

    go (IdxE e1 e2 maybe_len _) k = do
        (n, tau) <- inferExp e1 >>= checkArrOrRefArrT
        cn       <- cgNatType n
        ce1      <- cgExpOneshot e1
        ce2      <- cgExpOneshot e2
        case maybe_len of
          Nothing  -> calias e <$> cgIdx tau ce1 cn ce2 >>= runKont k
          Just len -> calias e <$> cgSlice tau ce1 cn ce2 len >>= runKont k

    go e@(StructE _ _ flds l) k =
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
        cgPrintScalar UnitT{}           _  = appendStm $ rl l [cstm|printf("()");|]
        cgPrintScalar BoolT{}           ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "true" : "false");|]
        cgPrintScalar (IntT (U 1)  _)   ce = appendStm $ rl l [cstm|printf("%s",  $ce ? "'1" : "'0");|]
        cgPrintScalar (IntT IDefault _) ce = appendStm $ rl l [cstm|printf("%d", (int) $ce);|]
        cgPrintScalar (IntT (I w) _)    ce
          | w <= 32                        = appendStm $ rl l [cstm|printf("%ld", (long) $ce);|]
          | otherwise                      = appendStm $ rl l [cstm|printf("%lld", (long long) $ce);|]
        cgPrintScalar (IntT UDefault _) ce = appendStm $ rl l [cstm|printf("%u", (unsigned) $ce);|]
        cgPrintScalar (IntT (U w) _)    ce
          | w <= 32                        = appendStm $ rl l [cstm|printf("%lu", (long) $ce);|]
          | otherwise                      = appendStm $ rl l [cstm|printf("%llu", (long long) $ce);|]
        cgPrintScalar FloatT{}          ce = appendStm $ rl l [cstm|printf("%f",  (double) $ce);|]
        cgPrintScalar StringT{}         ce = appendStm $ rl l [cstm|printf("%s",  $ce);|]
        cgPrintScalar (ArrT n tau _)    ce = cgPrintArray n tau ce

        cgPrintScalar tau_struct@StructT{} ce = do
            maybe_tau <- runMaybeT $ checkComplexT tau_struct
            case maybe_tau of
              Just (IntT IDefault _) -> appendStm $ rl l [cstm|printf("(%d,%d)", (int) $ce.re, (int) $ce.im);|]
              Just (IntT I{} _)      -> appendStm $ rl l [cstm|printf("(%ld,%ld)", (long) $ce.re, (long) $ce.im);|]
              Just (IntT UDefault _) -> appendStm $ rl l [cstm|printf("(%u,%u)", (unsigned) $ce.re, (unsigned) $ce.im);|]
              Just (IntT U{} _)      -> appendStm $ rl l [cstm|printf("(%lu,%lu)", (unsigned long) $ce.re, (unsigned long) $ce.im);|]
              Just FloatT{}          -> appendStm $ rl l [cstm|printf("(%Lf,%Lf)", (long double) $ce.re, (long double) $ce.im);|]
              _                      -> faildoc $ text "Cannot print type:" <+> ppr tau_struct

        cgPrintScalar tau _ =
            faildoc $ text "Cannot print type:" <+> ppr tau

        cgPrintArray :: Type -> Type -> CExp l -> Cg l ()
        cgPrintArray nat tau ce | isBitT tau = do
            cn    <- cgNatType nat
            caddr <- cgAddrOf (ArrT nat tau noLoc) ce
            appendStm $ rl l [cstm|kz_bitarray_print($caddr, $cn);|]

        cgPrintArray nat tau ce = do
            cn    <- cgNatType nat
            caddr <- cgAddrOf (ArrT nat tau noLoc) ce
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

    go (BindE WildV tau e1 e2 _) k =
        cgExp e1 $ oneshot tau $ \ce -> do
        cgVoid ce
        cgExp e2 k

    go (BindE (TameV v) tau e1 e2 _) k =
        cgExp e1 $ cgMonadicBinding v tau $ \cv ->
          extendVars [(bVar v, tau)] $
          extendVarCExps [(bVar v, cv)] $
          cgExp e2 k

    go (LutE _ e) k =
        cgExp e k

    go e0@(GenE e gs _) k = do
        ce <- compileAndRunGen e gs >>= cgConst
        cgConstExp e0 ce k

cgConstExp :: Exp -> CExp l -> Kont l a -> Cg l a
cgConstExp e (CInit cinit) k = do
    tau        <- inferExp e
    cv :: C.Id <- gensym "__const"
    ctau       <- cgType tau
    appendTopDecl [cdecl|static $tyqual:calign const $ty:ctau $id:cv = $init:cinit;|]
    runKont k $ CExp $ reloc (locOf e) [cexp|$id:cv|]

cgConstExp _ ce k =
    runKont k ce

-- | Generate loop initialization and loop test for a 'GenInterval Exp'.
cgGenInterval :: IsLabel l
              => GenInterval Exp
              -> Cg l (CExp l, C.Id -> CExp l)
cgGenInterval (FromToInclusive e1 e2 _) = do
    ce1 <- cgExpOneshot e1
    ce2 <- cgExpOneshot e2
    return (ce1, \i -> CExp [cexp|$id:i <= $ce2|])

cgGenInterval (FromToExclusive e1 e2 _) = do
    ce1 <- cgExpOneshot e1
    ce2 <- cgExpOneshot e2
    return (ce1, \i -> CExp [cexp|$id:i < $ce2|])

cgGenInterval (StartLen e1 e2 _) = do
    ce1 <- cgExpOneshot e1
    ce2 <- cgExpOneshot e2
    return (ce1, \i -> CExp [cexp|$id:i < $(ce1 + ce2)|])

-- | Generate code for a looping construct. Any identifiers used in the body of
-- the loop are marked as used again after code for the body has been generated
-- in case there is a label at the end of the loop's body.
cgLoop :: IsLabel l => Maybe l -> Cg l () -> Cg l ()
cgLoop Nothing m = do
    cids <- collectUsed_ m
    useCIds cids

cgLoop (Just l) m = cgWithLabel l $ do
    cids <- collectUsed_ m
    useCIds cids

-- | Compile a function variable binding. When the variable is a ref type, it is
-- represented as a pointer, so we use the 'CPtr' constructor to ensure that
-- dereferencing occurs.
cgVarBind :: (Var, Type) -> Cg l (CExp l, C.Param)
cgVarBind (v, tau) = do
    cv     <- cvar v
    cparam <- cgParam tau (Just cv)
    return $ go cv cparam
  where
    go :: C.Id -> C.Param -> (CExp l, C.Param)
    go cv cparam
      | isPassByRef tau = (CPtr $ CExp $ rl l [cexp|$id:cv|], cparam)
      | isBitArrT tau   = (CBitSlice $ CExp $ rl l [cexp|$id:cv|], cparam)
      | otherwise       = (CExp $ rl l [cexp|$id:cv|], cparam)

    l :: Loc
    l = locOf v <--> locOf tau

-- | Compile a Nat type variable binding.
cgNatTyVar :: TyVar -> Cg l (CExp l, C.Param)
cgNatTyVar alpha = do
    calpha <- cvar alpha
    return (CExp [cexp|$id:calpha|], [cparam|int $id:calpha|])

-- | Compile a type-level Nat to a C expression.
cgNatType :: Type -> Cg l (CExp l)
cgNatType (NatT i _) =
    return $ CInt (fromIntegral i)

cgNatType (TyVarT alpha _) =
    lookupTyVarCExp alpha

cgNatType tau =
    faildoc $ text "Cannot compile non-Nat kinded type:" <+> ppr tau

-- | Compile a type-level Nat to an 'Integer' constant. If the argument cannot
-- be resolved to a constant, raise an exception.
cgConstNatType :: Type -> Cg l Integer
cgConstNatType tau = do
    ce <- cgNatType tau
    case ce of
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
cgBits tau@(ArrT n _ _) ce | isBitArrT tau = do
    ctau  <- cgBitcastType tau
    caddr <- cgAddrOf tau ce
    w     <- cgConstNatType n
    if cgWidthMatchesBitcastTypeWidth w || not (needsBitMask ce)
      then return [cexp|*(($ty:ctau*) $caddr)|]
      else return [cexp|*(($ty:ctau*) $caddr) & $(chexconst (2^w - 1))|]

cgBits tau@IntT{} ce = do
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
cgType UnitT{} =
    return [cty|void|]

cgType BoolT{} =
    return [cty|typename uint8_t|]

cgType tau | isBitT tau =
    cgBitElemType

cgType (IntT IDefault _) =
    return [cty|int|]

cgType tau@(IntT (I w) _)
    | w <= 8    = return [cty|typename int8_t|]
    | w <= 16   = return [cty|typename int16_t|]
    | w <= 32   = return [cty|typename int32_t|]
    | w <= 64   = return [cty|typename int64_t|]
    | otherwise = faildoc $ text "Cannot compile fixed type" <+> ppr tau <+> "(width >64)."

cgType (IntT UDefault _) =
    return [cty|unsigned|]

cgType tau@(IntT (U w) _)
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

cgType StringT{} =
    return [cty|char*|]

cgType tau_struct@(StructT struct [] l) = do
    maybe_tau <- runMaybeT $ checkComplexT tau_struct
    case maybe_tau of
      Just tau | tau == int8T  -> return [cty|typename complex8_t|]
               | tau == int16T -> return [cty|typename complex16_t|]
               | tau == int32T -> return [cty|typename complex32_t|]
               | tau == int64T -> return [cty|typename complex64_t|]
      _ -> return [cty|typename $id:(cstruct struct l)|]

cgType tau@StructT{} =
    withSummaryContext tau $
    faildoc $ text "Cannot compile polymorphic struct types."

cgType (ArrT (NatT n _) tau _) | isBitT tau = do
    cbitElemType <- cgBitElemType
    return [cty|$ty:cbitElemType[$int:(bitArrayLen n)]|]

cgType (ArrT (NatT n _) tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau[$int:n]|]

cgType tau@(ArrT _ _ _) =
    panicdoc $ text "cgType: cannot translate array of unknown size:" <+> ppr tau

cgType tau@(ST (C tau') _ _ _ _) | isPureishT tau =
    cgType tau'

cgType tau@ST{} =
    panicdoc $ text "cgType: cannot translate ST types:" <+> ppr tau

cgType (RefT (ArrT (NatT n _) tau _) _) | isBitT tau = do
    cbitElemType <- cgBitElemType
    return [cty|$ty:cbitElemType[$int:(bitArrayLen n)]|]

cgType (RefT (ArrT (NatT n _) tau _) _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau[$int:n]|]

cgType (RefT (ArrT _ tau _) _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (RefT tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (ForallT alphas (FunT args ret _) _) =
    cgFunType (map fst alphas) args ret

cgType (FunT args ret _) =
    cgFunType [] args ret

cgType NatT{} =
    return [cty|int|]

cgType tau@ForallT{} =
    faildoc $ text "cgType: cannot translate polymorphic type:" <+> ppr tau

cgType (TyVarT alpha _) =
    lookupTyVarType alpha >>= cgType

-- | Compute the type of array elements in a bit array.
cgBitElemType :: Cg l C.Type
cgBitElemType = cgType (IntT (U bIT_ARRAY_ELEM_BITS) noLoc)

cgFunType :: [TyVar] -> [Type] -> Type -> Cg l C.Type
cgFunType nats args ret = do
    let natTys =  replicate (length nats) [cparam|int|]
    argTys     <- mapM (`cgParam` Nothing) args
    if isReturnedByRef ret
      then do retTy <- cgParam ret Nothing
              return [cty|void (*)($params:(natTys ++ argTys ++ [retTy]))|]
      else do retTy <- cgType ret
              return [cty|$ty:retTy (*)($params:(natTys ++ argTys))|]

{- Note [Type Qualifiers for Array Arguments]

We use the static type qualifiers to declare that the arrays have at least a
certain size. We no longer use restrict, because we can't guarantee that there
is no aliasing between pointers.

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
    cgParamType (ArrT (NatT n _) tau _) | isBitT tau = do
        cbitElemType <- cgBitElemType
        return [cty|const $ty:cbitElemType[$tyqual:cstatic $int:(bitArrayLen n)]|]

    cgParamType (ArrT (NatT n _) tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau[$int:n]|]

    cgParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgParamType (RefT (ArrT (NatT n _) tau _) _) | isBitT tau = do
        cbitElemType <- cgBitElemType
        return [cty|$ty:cbitElemType[$tyqual:cstatic $int:(bitArrayLen n)]|]

    cgParamType (RefT (ArrT (NatT n _) tau _) _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau[$tyqual:cstatic $int:n]|]

    cgParamType (RefT (ArrT _ tau _) _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau*|]

    cgParamType (RefT tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau*|]

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
    cgRetParamType (ArrT (NatT n _) tau _) | isBitT tau = do
        cbitElemType <- cgBitElemType
        return [cty|$ty:cbitElemType[$tyqual:cstatic $int:(bitArrayLen n)]|]

    cgRetParamType (ArrT (NatT n _) tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau[$tyqual:cstatic $int:n]|]

    cgRetParamType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|$ty:ctau*|]

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
    oneshotk _ CComp{} =
        panicdoc $ text "cgLetBinding: cannot bind a computation."

    oneshotk _ CFunComp{} =
        panicdoc $ text "cgLetBinding: cannot bind a computation function."

    -- If the binder is tainted, then we will create a new binding, so we can
    -- forget the alias.
    oneshotk f (CAlias _ ce) | isTainted bv =
        oneshotk f ce

    -- Otherwise we have to remember the alias.
    oneshotk  f (CAlias e ce) =
        oneshotk (f . calias e) ce

    oneshotk f ce | not (isTainted bv) && isSimple ce =
        k (f ce)

    oneshotk f ce = do
        cv <- cgBinder (bVar bv) tau False
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
    cv <- cgBinder (bVar bv) tau (needDefault bv)
    if needDefault bv
      then incDefaultInits
      else cgInitAlways cv tau
    k cv
  where
    needDefault :: BoundVar -> Bool
    needDefault BoundV{ bNeedDefault = Just False} = False
    needDefault _                                  = True

cgLetRefBinding bv tau (Just e) k = do
    cve <- cgBinder (bVar bv) tau False
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

    oneshotk f ce@CBool{} =
        k (f ce)

    oneshotk f ce@CInt{} =
        k (f ce)

    oneshotk f ce@CFloat{} =
        k (f ce)

    oneshotk _ CComp{} =
        panicdoc $ text "cgMonadicBinding: cannot bind a computation."

    oneshotk _ CFunComp{} =
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
        cv <- cgBinder (bVar bv) tau False
        cgAssign tau cv ce
        k (f cv)

    oneshotk f ce =
        k (f ce)

isTainted :: BoundVar -> Bool
isTainted BoundV{ bTainted = Nothing }    = True
isTainted BoundV{ bTainted = Just taint } = taint

-- | Declare C storage for the given variable. If we are in top scope, declare
-- the storage at top level; otherwise, declare it at thread scope.
cgBinder :: Var -> Type -> Bool -> Cg l (CExp l)
cgBinder _ UnitT{} _ =
    return CVoid

cgBinder v tau@(ST (C tau') _ _ _ _) init | isPureishT tau =
    cgBinder v tau' init

cgBinder v tau init = do
    isTop       <- isInTopScope
    cv          <- cvar v
    (cdecl, ce) <- cgStorage cv tau init
    if isTop
      then appendTopDecl cdecl
      else appendDecl cdecl
    return ce

-- | Perform mandatory initialization of an l-value.
cgInitAlways :: CExp l -> Type -> Cg l ()
cgInitAlways cv (ArrT n tau _) | isBitT tau = do
    cn <- cgNatType n
    case cn of
      CInt n | bitArrayOff n == 0 -> return ()
      _ -> appendStm [cstm|$cv[$(bitArrayLen cn-1)] = 0;|]

cgInitAlways _ _ =
    return ()

-- | Allocate storage for a temporary of the given core type. The name of the
-- temporary is gensym'd using @s@ with a prefix of @__@.
cgTemp :: String -> Type -> Cg l (CExp l)
cgTemp _ UnitT{} =
    return CVoid

cgTemp s tau = do
    cv          <- gensym ("__" ++ s)
    (cdecl, ce) <- cgStorage cv tau False
    appendDecl cdecl
    cgInitAlways ce tau
    return ce

-- | Allocate storage for a C identifier with the given core type.
cgStorage :: C.Id -- ^ C identifier for storage
          -> Type -- ^ Type of storage
          -> Bool -- ^ 'True' if storage should be initialized to default value
          -> Cg l (C.InitGroup, CExp l)
cgStorage _ UnitT{} _ =
    faildoc "cgStorage: asked to allocate storage for unit type."

-- Note that we use 'appendStm' for initialization code for arrays allocated
-- with @alloca@. This is OK since the only time we don't statically know an
-- array's size is when we are in a function body.
cgStorage cv (ArrT n tau _) init | isBitT tau =
    cgNatType n >>= go
  where
    go :: CExp l -> Cg l (C.InitGroup, CExp l)
    go (CInt n) | init = do
        cbitElemType <- cgBitElemType
        let cinit = rl cv [cdecl|$tyqual:calign $ty:cbitElemType $id:cv[$int:(bitArrayLen n)] = {0};|]
        return (cinit, ce)

    go (CInt n) = do
        cbitElemType <- cgBitElemType
        let cinit = rl cv [cdecl|$tyqual:calign $ty:cbitElemType $id:cv[$int:(bitArrayLen n)];|]
        return (cinit, ce)

    go cn = do
        cbitElemType <- cgBitElemType
        let cinit = rl cv [cdecl|$ty:cbitElemType* $id:cv = ($ty:cbitElemType*) alloca($(bitArrayLen cn) * sizeof($ty:cbitElemType));|]
        appendStm [cstm|memset($id:cv, 0, $(bitArrayLen cn)*sizeof($ty:cbitElemType));|]
        return (cinit, ce)

    ce :: CExp l
    ce = CExp $ rl cv [cexp|$id:cv|]

cgStorage cv (ArrT n tau _) init = do
    ctau <- cgType tau
    cgNatType n >>= go ctau
  where
    go :: C.Type -> CExp l -> Cg l (C.InitGroup, CExp l)
    go ctau (CInt n) | init = do
        cdflt    <- cgDefault tau
        let cinit =  rl cv [cdecl|$tyqual:calign $ty:ctau $id:cv[$int:n] = { $init:cdflt };|]
        return (cinit, ce)

    go ctau (CInt n) = do
        let cinit = rl cv [cdecl|$tyqual:calign $ty:ctau $id:cv[$int:n];|]
        return (cinit, ce)

    go ctau cn = do
        let cinit = rl cv [cdecl|$ty:ctau* $id:cv = ($ty:ctau*) alloca($cn * sizeof($ty:ctau));|]
        appendStm [cstm|memset($id:cv, 0, $cn*sizeof($ty:ctau));|]
        return (cinit, ce)

    ce :: CExp l
    ce = CExp $ rl cv [cexp|$id:cv|]

cgStorage cv tau init =
    cgType tau >>= go
  where
    go :: C.Type -> Cg l (C.InitGroup, CExp l)
    go ctau | init = do
        cdflt     <- cgDefault (unRefT tau)
        let cinit =  rl cv [cdecl|$ty:ctau $id:cv = $init:cdflt;|]
        return (cinit, ce)

    go ctau = do
        let cinit =  rl cv [cdecl|$ty:ctau $id:cv;|]
        return (cinit, ce)

    ce :: CExp l
    ce | isRefT tau = CPtr $ CExp $ rl cv [cexp|$id:cv|]
       | otherwise  = CExp $ rl cv [cexp|$id:cv|]

cgDefault :: Type -> Cg l C.Initializer
cgDefault tau = toInitializer <$> (defaultValueC tau >>= cgConst)

-- | Generate code for a C temporary with a gensym'd name, based on @s@ and
-- prefixed with @__@, having C type @ctau@, and with the initializer
-- @maybe_cinit@.
cgCTempDecl :: Located a
            => a
            -> String
            -> C.Type
            -> Maybe C.Initializer
            -> Cg l (C.InitGroup, CExp l)
cgCTempDecl l s ctau maybe_cinit = do
    cv :: C.Id <- gensym ("__" ++ s)
    let decl = case maybe_cinit of
                 Nothing    -> rl l [cdecl|$ty:ctau $id:cv;|]
                 Just cinit -> rl l [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return (decl, CExp $ rl l [cexp|$id:cv|])

-- | Generate code for a C temporary.
cgCTemp :: Located a
        => a
        -> String
        -> C.Type
        -> Maybe C.Initializer
        -> Cg l (CExp l)
cgCTemp l s ctau maybe_cinit = do
    (decl, ce) <- cgCTempDecl l s ctau maybe_cinit
    appendDecl decl
    return ce

-- | Generate code for a thread-level C temporary.
cgThreadCTemp :: Located a
              => a
              -> String
              -> C.Type
              -> Maybe C.Initializer
              -> Cg l (CExp l)
cgThreadCTemp l s ctau maybe_cinit = do
    (decl, ce) <- cgCTempDecl l s ctau maybe_cinit
    appendThreadDecl decl
    return ce

-- | Generate code for a top-level C temporary.
cgTopCTemp :: Located a
           => a
           -> String
           -> C.Type
           -> Maybe C.Initializer
           -> Cg l (CExp l)
cgTopCTemp l s ctau maybe_cinit = do
    (decl, ce) <- cgCTempDecl l s ctau maybe_cinit
    appendTopDecl decl
    return ce

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
      then do newLabelScope
              (stms, x) <- collectStms $ newScope k
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
    C.Id ident l = C.toIdent lbl noLoc

-- | Compile a computation and throw away the result.
cgCompVoid :: IsLabel l
           => Comp l -- ^ Computation to compiled
           -> l      -- ^ Label of our continuation
           -> Cg l ()
cgCompVoid comp klbl = do
    -- We place the generated code in a new block because the generated code may
    -- have a label placed after it, e.g., when we are generating code for a
    -- loop body. That can mess with declaration initializers.
    citems <- inNewBlock_ $
              cgComp comp klbl $
              multishot cgVoid
    appendStm [cstm|{ $items:citems }|]

-- | 'cgComp' compiles a computation and ensures that the continuation label is
-- jumped to. We assume that the continuation labels the code that will be
-- generated immediately after the call to 'cgComp', so if the computation
-- compiles to straight-line code, no @goto@ will be generated.
cgComp :: forall a l . IsLabel l
       => Comp l   -- ^ Computation to compiled
       -> l        -- ^ Label of our continuation
       -> Kont l a -- ^ Continuation accepting the compilation result
       -> Cg l a
cgComp comp klbl = cgSteps (unComp comp)
  where
    cgSteps :: forall a . [Step l] -> Kont l a -> Cg l a
    cgSteps [] _ =
        faildoc $ text "No computational steps to compile!"

    cgSteps [step] k =
        cgStep step klbl k

    cgSteps (LetC l decl _ : steps) k = do
        flags <- askConfig
        cgWithLabel l $
          cgLocalDecl flags decl $
          cgSteps steps k

    cgSteps (step : BindC l WildV tau _ : steps) k =
        cgSeqStep step l $ oneshot tau $ \ce -> do
        cgVoid ce
        cgWithLabel l $ cgSteps steps k

    cgSteps (step : BindC l (TameV v) tau _ : steps) k =
        cgSeqStep step l $
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
              CComp compc -> compc klbl $ multishot k
              _           -> k ce

    cgSteps (step : steps) k = do
        l   <- stepLabel (head steps)
        tau <- inferStep step
        cgSeqStep step l $ oneshot tau $ \ce -> do
            cgVoid ce
            cgSteps steps k

    cgSeqStep :: forall a . Step l -> l -> Kont l a -> Cg l a
    cgSeqStep step klbl k = do
        free <- isFreeRunning
        withFreeRunning False $
          cgStep step klbl $
          mapKont (\f -> withFreeRunning free . f) k

    cgStep :: forall a . Step l -> l -> Kont l a -> Cg l a
    cgStep (VarC l v _) klbl k =
        cgWithLabel l $ do
        compc <- lookupVarCExp v >>= unCComp
        compc klbl k

    cgStep (CallC l f taus args _) klbl k =
        cgWithLabel l $ do
        funcompc <- lookupVarCExp f >>= unCFunComp
        funcompc taus args klbl k

    cgStep (IfC l e thenk elsek _) klbl k =
        cgWithLabel l $ do
        tau <- inferComp thenk
        cgIf tau e (cgComp thenk klbl) (cgComp elsek klbl) k

    cgStep LetC{} _ _k =
        faildoc $ text "Cannot compile let computation step."

    cgStep (WhileC l e_test c_body sloc) _ k = do
        cgLoop (Just l) $
            cgWhile sloc e_test $ do
            l_inner <- gensym "inner_whilek"
            cgCompVoid c_body l_inner
            cgLabel l_inner
        newScope $ runKont k CVoid

    cgStep (ForC l _ v v_tau gint c_body sloc) _ k = do
        cv     <- cvar v
        cv_tau <- cgType v_tau
        extendVars [(v, v_tau)] $
            extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
            appendDecl $ rl sloc [cdecl|$ty:cv_tau $id:cv;|]
            cgLoop (Just l) $ do
                useCId cv
                (ce_start, ce_test) <- cgGenInterval gint
                citems              <- inNewBlock_ $ do
                                       l_inner <- gensym "inner_fork"
                                       cgCompVoid c_body l_inner
                                       cgLabel l_inner
                appendStm $
                  rl sloc [cstm|for ($id:cv = $ce_start;
                                     $(ce_test cv);
                                     $id:cv++) {
                                  $items:citems
                                }|]
        newScope $ runKont k CVoid

    cgStep (LiftC l e _) _ k =
        cgWithLabel l $
        cgExp e k

    -- A 'ReturnC' is a pure value, so we do not need to lower it.
    cgStep (ReturnC l e _) _ k =
        cgWithLabel l $
        cgExp e k

    cgStep BindC{} _ _k =
        faildoc $ text "Cannot compile bind computation step."

    cgStep (TakeC l tau _) klbl k =
        cgWithLabel l $
        cgTake tau klbl $ runKont k

    cgStep (TakesC l n tau _) klbl k =
        cgWithLabel l $
        cgTakes n tau klbl $ runKont k

    cgStep (EmitC l e _) klbl k =
        cgWithLabel l $ do
        tau <- inferExp e
        ce  <- cgExpOneshot e
        cgEmit tau ce klbl $ runKont k CVoid

    cgStep (EmitsC l e _) klbl k =
        cgWithLabel l $ do
        (n, tau) <- inferExp e >>= checkArrT
        ce       <- cgExpOneshot e
        cgEmits n tau ce klbl $ runKont k CVoid

    cgStep (RepeatC l _ c_body sloc) _ k = do
        cgLoop Nothing $ do
            citems <- inNewBlock_ $ do
                      cgCompVoid c_body l
                      cgLabel l
            appendStm $ rl sloc [cstm|for (;;) { $items:citems }|]
        newScope $ runKont k CVoid

    cgStep step@(ParC ann b left right _) _ k =
        withSummaryContext step $ do
        dflags  <- askConfig
        tau_res <- resultType <$> inferStep step
        free    <- isFreeRunning
        if testDynFlag PipelineAll dflags
          then cgParMultiThreaded ForkProducer free tau_res b left right klbl k
          else if free && shouldPipeline dflags ann
          then cgParMultiThreaded ForkConsumer free tau_res b left right klbl k
          else cgParSingleThreaded tau_res b left right klbl k
      where
        shouldPipeline :: Config -> PipelineAnn -> Bool
        shouldPipeline dflags AlwaysPipeline | testDynFlag Pipeline dflags =
            True

        shouldPipeline _ _ =
            False

-- | Compile a par, i.e., a producer/consumer pair, using the simple
-- single-threaded strategy. The take and emit code generators should generate
-- code for the par's take and emit.
cgParSingleThreaded :: forall a l . IsLabel l
                    => Type     -- ^ The type of the result of the par
                    -> Type     -- ^ The type of the par's internal buffer
                    -> Comp l   -- ^ The producer computation
                    -> Comp l   -- ^ The consumer computation
                    -> l        -- ^ The computation's continuation
                    -> Kont l a -- ^ Continuation accepting the compilation result
                    -> Cg l a
cgParSingleThreaded _tau_res b left right klbl k = do
    (s, a, c)          <- askSTIndices
    (omega_l, _, _, _) <- localSTIndices (Just (s, a, b)) $
                          inferComp left >>= checkST
    (omega_r, _, _, _) <- localSTIndices (Just (b, b, c)) $
                          inferComp right >>= checkST
    -- Generate variables to hold the left and right computations'
    -- continuations.
    leftl   <- compLabel left
    useLabel leftl
    rightl  <- compLabel right
    useLabel rightl
    cleftk  <- cgThreadCTemp b "par_leftk"  [cty|typename KONT|] (Just [cinit|LABELADDR($id:leftl)|])
    crightk <- cgThreadCTemp b "par_rightk" [cty|typename KONT|] (Just [cinit|LABELADDR($id:rightl)|])
    -- Generate a pointer to the current element in the buffer.
    ctau    <- cgType b
    ctauptr <- cgBufPtrType b
    cbuf    <- cgThreadCTemp b "par_buf"  [cty|$tyqual:calign $ty:ctau|] Nothing
    cbufp   <- cgThreadCTemp b "par_bufp" ctauptr                        Nothing
    -- The void continuation simply swallows its argument and does nothing. We
    -- use this for transformers since they never return anyway.
    let voidk :: Kont l ()
        voidk = multishot $ const $ return ()
    -- k' is our continuation k suitably modifed to restore the current Cg
    -- environment so that we can call it from within one of the branches of the
    -- par. We need to save/restore the Cg environment so k uses the take/emit
    -- in effect *right here* rather than those in effect within the branches of
    -- the par.
    restore <- saveCgEnv
    let k'  =  mapKont (\f ce -> restore $ f ce) k
    -- Code generators for left and right sides
    let cgLeft, cgRight :: forall a . Kont l a -> Cg l a
        cgLeft k  = localSTIndices (Just (s, a, b)) $
                    withEmitK  (emitk cleftk crightk cbuf cbufp) $
                    withEmitsK (emitsk cleftk crightk cbuf cbufp) $
                    cgComp left klbl k
        cgRight k = localSTIndices (Just (b, b, c)) $
                    withTakeK  (takek cleftk crightk cbuf cbufp) $
                    withTakesK (takesk cleftk crightk cbuf cbufp) $
                    cgComp right klbl k
    -- Generate code for the left and right computations.
    case (omega_l, omega_r) of
      (C{}, _) -> do cgRight voidk
                     cgLeft k'
      (_, C{}) -> do x <- cgRight k'
                     cgLeft voidk
                     return x
      _        -> do cgRight voidk
                     cgLeft voidk
                     runKont k CVoid
  where
    cgBufPtrType :: Type -> Cg l C.Type
    cgBufPtrType (ArrT _ tau _) = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgBufPtrType tau = do
        ctau <- cgType tau
        return [cty|const $ty:ctau*|]

    cgDerefBufPtr :: Type -> CExp l -> CExp l
    cgDerefBufPtr ArrT{} ce = ce
    cgDerefBufPtr _      ce = CExp [cexp|*$ce|]

    takek :: CExp l -> CExp l -> CExp l -> CExp l -> TakeK l
    -- The one element take is easy. We know the element will be in @cbufp@,
    -- so we call @k1@ with @cbufp@ as the argument, which generates a
    -- 'CComp', @ccomp@ that represents the continuation that consumes the
    -- taken value. We then set the right computation's continuation to the
    -- label of @ccomp@, since it is the continuation, generate code to jump
    -- to the left computation's continuation, and then call @k2@ with
    -- @ccomp@ suitably modified to have a required label.
    takek cleftk crightk _cbuf cbufp _tau klbl k = do
        useLabel klbl
        appendStm [cstm|$crightk = LABELADDR($id:klbl);|]
        appendStm [cstm|INDJUMP($cleftk);|]
        k $ cgDerefBufPtr b cbufp

    takesk :: CExp l -> CExp l -> CExp l -> CExp l -> TakesK l
    -- The multi-element take is a bit tricker. We allocate a buffer to hold
    -- all the elements, and then loop, jumping to the left computation's
    -- continuation repeatedly, until the buffer is full. Then we fall
    -- through to the next action, which is why we call @k2@ with @ccomp@
    -- without forcing its label to be required---we don't need the label!
    takesk cleftk crightk _cbuf cbufp n tau _klbl k = do
        ctau_arr <- cgType (arrKnownT n tau)
        carr     <- cgThreadCTemp tau "par_takes_xs" [cty|$tyqual:calign $ty:ctau_arr|] Nothing
        klbl     <- gensym "inner_takesk"
        useLabel klbl
        cgInitAlways carr (arrKnownT n tau)
        appendStm [cstm|$crightk = LABELADDR($id:klbl);|]
        cgFor 0 (fromIntegral n) $ \ci -> do
            appendStm [cstm|INDJUMP($cleftk);|]
            cgWithLabel klbl $
                cgAssign (refT tau) (CIdx tau carr ci) (cgDerefBufPtr b cbufp)
        newScope $ k carr

    emitk :: CExp l -> CExp l -> CExp l -> CExp l -> EmitK l
    -- @tau@ must be a base (scalar) type
    emitk cleftk crightk cbuf cbufp tau ce klbl k = do
        useLabel klbl
        appendStm [cstm|$cleftk = LABELADDR($id:klbl);|]
        cgAssignBufp tau cbuf cbufp ce
        appendStm [cstm|INDJUMP($crightk);|]
        k

    emitsk :: CExp l -> CExp l -> CExp l -> CExp l -> EmitsK l
    emitsk cleftk crightk cbuf cbufp (NatT 1 _) tau ce klbl k = do
        ce' <- cgIdx tau ce 1 0
        emitk cleftk crightk cbuf cbufp tau ce' klbl k

    emitsk cleftk crightk cbuf cbufp n tau ce _klbl k = do
        cn    <- cgNatType n
        loopl <- gensym "emitsk_next"
        useLabel loopl
        appendStm [cstm|$cleftk = LABELADDR($id:loopl);|]
        cgFor 0 cn $ \ci -> do
            celem <- cgIdx tau ce cn ci
            cgAssignBufp tau cbuf cbufp celem
            appendStm [cstm|INDJUMP($crightk);|]
            -- Because we need a statement to label, but the continuation is
            -- the next loop iteration...
            cgLabel loopl
        newScope k

    -- Assign the value @ce@ to the buffer pointer @cbufp@. If @ce@ is not
    -- an lvalue, then stash it in @cbuf@ first and set @cbufp@ to point to
    -- @cbuf@. This ensures that we can always pass buffer elements by
    -- reference.
    cgAssignBufp :: Type -> CExp l -> CExp l -> CExp l -> Cg l ()
    cgAssignBufp tau _ cbufp ce | isLvalue ce = do
        -- We take the address of @ce@, so we need to promote its scope out of
        -- local scope.
        promoteScope ce
        caddr <- cgAddrOf tau ce
        appendStm [cstm|$cbufp = $caddr;|]

    cgAssignBufp tau cbuf cbufp ce = do
        cgAssign tau cbuf ce
        appendStm [cstm|$cbufp = &$cbuf;|]

data ParStrategy = ForkProducer
                 | ForkConsumer
  deriving (Eq, Ord, Show)

-- | Compile a par, i.e., a producer/consumer pair, using the multi-threaded
-- strategy. The take and emit code generators passed as arguments to
-- 'cgParMultiThreaded' should generate code for the outer take and emit---the
-- inner take and emit is done with a producer-consumer buffer.
cgParMultiThreaded :: forall a l . IsLabel l
                   => ParStrategy -- ^ Strategy for compiling par
                   -> Bool        -- ^ 'True' if we are in a free-running context.
                   -> Type        -- ^ The type of the result of the par
                   -> Type        -- ^ The type of the par's internal buffer
                   -> Comp l      -- ^ The producer computation
                   -> Comp l      -- ^ The consumer computation
                   -> l           -- ^ The computation's continuation
                   -> Kont l a    -- ^ Continuation accepting the compilation result
                   -> Cg l a
cgParMultiThreaded strategy free tau_res b left right klbl k = do
    (s, a, c)          <- askSTIndices
    (omega_l, _, _, _) <- localSTIndices (Just (s, a, b)) $
                          inferComp left >>= checkST
    (omega_r, _, _, _) <- localSTIndices (Just (b, b, c)) $
                          inferComp right >>= checkST
    -- Create storage for the result of the par and a continuation to consume
    -- the storage.
    (cres, k') <- splitMultishotBind "par_res" tau_res False k
    -- Generate a temporary to hold the par buffer.
    cb   <- cgType b
    cbuf <- cgTopCTemp b "par_buf" [cty|$tyqual:calign $ty:cb[KZ_BUFFER_SIZE]|] Nothing
    -- Generate a name for the producer thread function
    cf <- gensym "par_threadfun"
    -- Generate a temporary to hold the thread info.
    ctinfo <- cgTopCTemp b "par_tinfo" [cty|typename kz_tinfo_t|] Nothing
    -- Generate a temporary to hold the thread.
    cthread <- cgTopCTemp b "par_thread" [cty|typename kz_thread_t|] Nothing
    -- Record the thread
    addThread Thread { threadInfo = ctinfo
                     , thread     = cthread
                     , threadRes  = cres
                     , threadFun  = cf
                     }
    -- Re-label the consumer computation. We have to do this because we need to
    -- generate code that initializes the par construct, and this initialization
    -- code needs to have the label of the consumer computation because that is
    -- the label that will be jumped to to run the consumer computation.
    l_consumer  <- compLabel right
    l_consumer' <- gensym "consumer"
    let right'  =  setCompLabel l_consumer' right
    -- Create a label for the computation that follows the par.
    l_pardone <- gensym "par_done"
    case strategy of
      ForkProducer -> do
        -- donek will generate code to store the result of the par and exit the the
        -- continuation.
        let donek :: Omega -> Kont l ()
            donek C{} = multishot $ \ce -> do
                        cgAssign tau_res cres ce
                        cgMemoryBarrier
                        cgExit
            donek T   = multishot $ const $
                        cgExit
        -- Generate to start the thread
        cgWithLabel l_consumer $
            cgCheckErr [cexp|kz_thread_post(&$ctinfo)|] "Cannot start thread." right
        -- Generate code for the producer
        localSTIndices (Just (s, a, b)) $
            withExitK (appendStms [cstms|$ctinfo.done = 1; BREAK;|]) $
            cgProducer ctinfo cbuf $
            cgParSpawn cf ctinfo left (donek omega_l)
        -- Generate code for the consumer
        localSTIndices (Just (b, b, c)) $
            withExitK (appendStm [cstm|$ctinfo.done = 1;|] >> cgJump l_pardone) $
            cgConsumer ctinfo cbuf $
            cgComp right' klbl (donek omega_r)
        -- Label the end of the computation
        cgWithLabel l_pardone k'

      ForkConsumer -> do
        setUsesConsumerThread
        -- We save the current codegen environment so we can call k' from within
        -- rightdonek. The right done continuation now calls k' directly.
        restore <- saveCgEnv
        let leftdonek :: Omega -> Kont l ()
            leftdonek C{} = multishot $ \ce -> do
                            appendComment $ text "Left computer done"
                            cgAssign tau_res cres ce
                            cgMemoryBarrier
                            cgExit
            leftdonek T   = multishot $ const $ do
                            appendComment $ text "Left transformer done"
                            cgExit
        let rightdonek :: Omega -> Kont l a
            rightdonek C{} = oneshot tau_res $ \ce -> do
                             appendComment $ text "Right computer done"
                             cgAssign tau_res cres ce
                             appendStm [cstm|$ctinfo.done = 1;|]
                             cgWithLabel l_pardone (restore k')
            rightdonek T   = oneshot tau_res $ \_ce -> do
                             appendComment $ text "Right transformer done"
                             appendStm [cstm|$ctinfo.done = 1;|]
                             cgWithLabel l_pardone (restore k')
        -- Generate to start the thread
        cgWithLabel l_consumer $
            cgCheckErr [cexp|kz_thread_post(&$ctinfo)|] "Cannot start thread." right
        -- Generate code for the producer
        localSTIndices (Just (s, a, b)) $
            withExitK (appendStms [cstms|$ctinfo.done = 1; BREAK;|]) $
            cgProducer ctinfo cbuf $
            cgComp left klbl (leftdonek omega_l)
        -- Generate code for the consumer
        localSTIndices (Just (b, b, c)) $
            withExitK (appendStm [cstm|$ctinfo.done = 1;|] >> cgJump l_pardone) $
            cgConsumer ctinfo cbuf $
            cgParSpawn cf ctinfo right' (rightdonek omega_r)
  where
    -- | Generate code to spawn a thread that is one side of a par construct.
    cgParSpawn :: forall a . C.Id
               -> CExp l
               -> Comp l
               -> Kont l a
               -> Cg l a
    cgParSpawn cf ctinfo comp k = do
        tau <- inferComp comp
        (clabels, (cblock, x)) <-
            collectLabels $
            inNewCodeBlock $ do
            newThreadScope
            cgThread tau comp k
        cgLabels clabels
        appendTopFunDef [cedecl|
static void* $id:cf(void* dummy)
{
    for (;;) {
        kz_check_error(kz_thread_wait(&$ctinfo), $string:(renderLoc comp), "Error waiting for thread to start.");
        {
            $items:(toBlockItems cblock)
        }
    }
    return NULL;
}|]
        return x

    cgProducer :: forall a . CExp l -> CExp l -> Cg l a -> Cg l a
    cgProducer ctinfo cbuf m =
        withGuardTakeK guardtakek $
        withEmitK emitk $
        withEmitsK emitsk m
      where
        -- Before the producer can take, it must wait for the consumer to ask
        -- for data.
        guardtakek :: GuardTakeK l
        guardtakek =
            cgWaitForConsumerRequest ctinfo

        emitk :: EmitK l
        -- @tau@ must be a base (scalar) type
        emitk tau ce _klbl k = do
            cgProduce ctinfo cbuf tau ce
            k

        emitsk :: EmitsK l
        -- Right now we just loop and write the elements one by one---it would
        -- be better to write them all at once.
        emitsk n tau ce _klbl k = do
            cn <- cgNatType n
            cgFor 0 cn $ \ci -> do
                celem <- cgIdx tau ce cn ci
                cgProduce ctinfo cbuf tau celem
            k

        -- | Put a single data element in the buffer.
        cgProduce :: CExp l -> CExp l -> Type -> CExp l -> Cg l ()
        cgProduce ctinfo cbuf tau ce = do
            cgWaitWhileBufferFull ctinfo
            let cidx = CExp [cexp|$ctinfo.prod_cnt % KZ_BUFFER_SIZE|]
            cgAssign (refT tau) (CIdx tau cbuf cidx) ce
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.prod_cnt;|]

        -- | Wait until the consumer requests data
        cgWaitForConsumerRequest :: CExp l -> Cg l ()
        -- A free-running computation does not need to wait for the consumer to
        -- request input.
        cgWaitForConsumerRequest _ | free =
            appendComment $ text "Free running (no need to wait for consumer to request input)"

        cgWaitForConsumerRequest ctinfo = do
            appendComment $ text "Wait for consumer to request input"
            appendStm [cstm|while (!$ctinfo.done && ((int) ($ctinfo.prod_cnt - $ctinfo.cons_req)) >= 0);|]
            cgExitWhenDone ctinfo

        -- | Wait while the buffer is full
        cgWaitWhileBufferFull :: CExp l -> Cg l ()
        -- A free-running computation *does* need to test if the consumer has
        -- exited. It is possible for the consumer to exit leaving the buffer
        -- full, so we perform the test here instead of in
        -- 'cgWaitForConsumerRequest'.
        cgWaitWhileBufferFull ctinfo | free = do
            appendComment $ text "Wait for room in the buffer"
            appendStm [cstm|while (!$ctinfo.done && ($ctinfo.prod_cnt - $ctinfo.cons_cnt == KZ_BUFFER_SIZE));|]
            cgExitWhenDone ctinfo

        cgWaitWhileBufferFull ctinfo = do
            appendComment $ text "Wait for room in the buffer"
            appendStm [cstm|while ($ctinfo.prod_cnt - $ctinfo.cons_cnt == KZ_BUFFER_SIZE);|]

        -- | Exit if the consumer has computed a final value.
        cgExitWhenDone :: CExp l -> Cg l ()
        cgExitWhenDone ctinfo = do
            appendComment $ text "Exit if the consumer has computed a final value"
            if [cexp|$ctinfo.done|]
              then cgExit
              else return ()

    cgConsumer :: forall a . CExp l -> CExp l -> Cg l a -> Cg l a
    cgConsumer ctinfo cbuf m =
        withTakeK takek $
        withTakesK takesk m
      where
        takek :: TakeK l
        takek tau _klbl k = do
            cgRequestData ctinfo 1
            cgConsume ctinfo cbuf tau k

        takesk :: TakesK l
        takesk n tau _klbl k = do
            ctau_arr <- cgType (arrKnownT n tau)
            carr     <- cgThreadCTemp tau "par_takes_xs" [cty|$tyqual:calign $ty:ctau_arr|] Nothing
            cgInitAlways carr (arrKnownT n tau)
            cgRequestData ctinfo (fromIntegral n)
            cgFor 0 (fromIntegral n) $ \ci ->
                cgConsume ctinfo cbuf tau $ \ce ->
                    cgAssign (refT tau) (CIdx tau carr ci) ce
            k carr

        -- | Consume a single data element from the buffer. We take a
        -- consumption continuation because we must be sure that we insert a
        -- memory barrier before incrementing the consumer count.
        cgConsume :: forall a . CExp l -> CExp l -> Type -> (CExp l -> Cg l a) -> Cg l a
        cgConsume ctinfo cbuf tau consumek = do
            appendComment $ text "Mark previous element as consumed"
            cgMemoryBarrier
            appendStm [cstm|++$ctinfo.cons_cnt;|]
            cgWaitWhileBufferEmpty ctinfo
            let cidx = CExp [cexp|$ctinfo.cons_cnt % KZ_BUFFER_SIZE|]
            consumek (CIdx tau cbuf cidx)

        -- | Request @cn@ data elements.
        cgRequestData :: CExp l -> CExp l -> Cg l ()
        cgRequestData ctinfo cn = do
            appendComment $ text "Request" <+> ppr cn <+> text "elements"
            appendStm [cstm|$ctinfo.cons_req += $cn;|]

        -- | Wait while the buffer is empty
        cgWaitWhileBufferEmpty :: CExp l -> Cg l ()
        cgWaitWhileBufferEmpty ctinfo = do
            appendComment $ text "Wait while the buffer is empty"
            appendStm [cstm|while (!$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == 0);|]
            cgExitWhenDone ctinfo

        -- | Exit if the producer has computed a final value and the queue is empty.
        cgExitWhenDone :: CExp l -> Cg l ()
        cgExitWhenDone ctinfo = do
            appendComment $ text "Exit if the producer has computed a final value and the queue is empty"
            if [cexp|$ctinfo.done && $ctinfo.prod_cnt - $ctinfo.cons_cnt == 0|]
              then cgExit
              else return ()

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

isLvalue (CExp C.Var{})       = True
isLvalue (CExp C.Member{})    = True
isLvalue (CExp C.PtrMember{}) = True
isLvalue (CExp C.Index{})     = True
isLvalue (CBitSlice ce)       = isLvalue ce
isLvalue (CAlias _ ce)        = isLvalue ce
isLvalue _                    = False

-- | @'resultType' tau@ returns the type of the result of a computation of
-- type @tau@. If @tau@ is @ST (C tau') s a b@, then the type of the result of
-- the computation is @tau'@. For a pure computation of type @tau@, the result
-- is just of type @tau. For a non-terminating computation of type @ST T s a b@,
-- the result type is the unit type.
resultType :: Type -> Type
resultType (ForallT _ tau@ST{} _) = resultType tau
resultType (ST (C tau) _ _ _ _)   = tau
resultType (ST T _ _ _ l)         = UnitT l
resultType tau                    = tau

-- | Return @True@ is a value of the given type is passed by reference, i.e., if
-- we need to pass the address of the value's corresponding 'CExp'. Note that
-- arrays are always passed by reference, so 'isPassByRef' returns @False@ for
-- array types.
isPassByRef :: Type -> Bool
isPassByRef (RefT ArrT{} _) = False
isPassByRef RefT{}          = True
isPassByRef ST{}            = error "isPassByRef: got ST type"
isPassByRef _               = False

-- | Return @True@ if a value of the given type is passed by reference as an
-- argument when it is the result of a function call.
isReturnedByRef :: Type -> Bool
isReturnedByRef ArrT{} = True
isReturnedByRef _      = False

-- | Insert a memory barrier
cgMemoryBarrier :: Cg l ()
cgMemoryBarrier = appendStm [cstm|kz_memory_barrier();|]

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
cgAssign UnitT{} _ ce =
    appendStm [cstm|$ce;|]

cgAssign tau ce1 ce2 = do
    useCExp ce1
    useCExp ce2
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
    assign _ (RefT tau _) ce1@CIdx{} ce2 | isBitT tau =
        appendStm [cstm|$carr[$cbitIdx] = ($carr[$cbitIdx] & ~$cmask) | $cbit;|]
      where
        carr, cidx :: CExp l
        Just (carr, cidx) = unCIdx ce1

        cbitIdx, cbitOff :: CExp l
        (cbitIdx, cbitOff) = bitArrayIdxOff cidx

        cmask, cbit :: CExp l
        cmask = 1 `shiftL'` cbitOff
        -- Bits are always masked off, so we we can assume ce2 is either 0 or
        -- 1. If we couldn't make this assumption, we would need to use
        -- [cexp|!!$ce2|] here.
        cbit = ce2 `shiftL'` cbitOff

    assign mayAlias tau0 ce1 ce2 | Just (n, tau) <- checkArrOrRefArrT tau0, isBitT tau = do
        clen <- cgNatType n
        cgAssignBitArray ce1 ce2 clen
      where
        cgAssignBitArray :: CExp l -> CExp l -> CExp l -> Cg l ()
        cgAssignBitArray ce1 ce2@CBits{} (CInt i) = do
            appendComment $ text "Bit array (CBits):" <+> ppr ce1 <+> text ":=" <+> ppr ce2
            go i
          where
            go :: Integer -> Cg l ()
            go i | i <= 8    = appendStm [cstm|*((typename uint8_t*) $ce1) = $ce2;|]
                 | i <= 16   = appendStm [cstm|*((typename uint16_t*) $ce1) = $ce2;|]
                 | i <= 32   = appendStm [cstm|*((typename uint32_t*) $ce1) = $ce2;|]
                 | i <= 64   = appendStm [cstm|*((typename uint64_t*) $ce1) = $ce2;|]
                 | otherwise = faildoc $
                               text "Bad bit array assignment:" </>
                               ppr ce1 <+> text ":=" <+> ppr ce2

        cgAssignBitArray ce1 ce2@CBits{} _ =
            faildoc $
            text "Bad bit array assignment:" </>
            ppr ce1 <+> text ":=" <+> ppr ce2

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
            -- | We take the fast path when the source and destination are
            -- aligned on 'bIT_ARRAY_ELEM_BITS' bits.
            fastPath :: CExp l  -- ^ Destination
                     -> CExp l  -- ^ Source
                     -> Integer -- ^ Source/destination index, in bits
                     -> Integer -- ^ Number of bits to copy
                     -> Cg l ()
            fastPath _cdst _csrc _i 0 =
                return ()

            fastPath cdst csrc i n
                | q == 1 = do appendStm [cstm|$cdst[$int:i] = $csrc[$int:i];|]
                              fastPath cdst csrc (i + q) r

                -- Unrolling the assignment loop is slower than calling
                -- memmove/memcpy
                | q /= 0 && False = do forM_ [0..q - 1] $ \j ->
                                           appendStm [cstm|$cdst[$int:(i+j)] = $csrc[$int:(i+j)];|]
                                       fastPath cdst csrc (i + q) r

                | q /= 0 = do incMemCopies
                              if mayAlias
                                  then appendStm [cstm|memmove(&$cdst[$int:i], &$csrc[$int:i], $int:qbytes);|]
                                  else appendStm [cstm|memcpy(&$cdst[$int:i], &$csrc[$int:i], $int:qbytes);|]
                              fastPath cdst csrc (i + q) r
              where
                q, r, qbytes :: Integer
                (q, r) = bitArrayIdxOff n
                qbytes = (q*bIT_ARRAY_ELEM_BITS) `quot` 8

            fastPath cdst0 csrc0 i n | n < bIT_ARRAY_ELEM_BITS =
                maskedAssign (CExp [cexp|$cdst0[$int:i]|]) (CExp [cexp|$csrc0[$int:i]|]) n
              where
                maskedAssign :: CExp l -> CExp l -> Integer -> Cg l ()
                maskedAssign cdst csrc n
                    | needsBitMask cdst0 = appendStm [cstm|$cdst = $(cdst ..&.. cnotmask ..|.. csrc');|]
                    | otherwise          = appendStm [cstm|$cdst = $csrc';|]
                  where
                    cmask, cnotmask :: CExp l
                    cmask    = CExp $ chexconst (2^n - 1)
                    cnotmask = CExp $ [cexp|~$(chexconst (2^n - 1))|]

                    csrc' :: CExp l
                    csrc' | needsBitMask csrc0 = csrc ..&.. cmask
                          | otherwise          = csrc

            fastPath _ _ i _ =
                slowPath cdst (cdstIdx + fromIntegral i) csrc (csrcIdx + fromIntegral i) clen
              where
                cdst, cdstIdx :: CExp l
                (cdst, cdstIdx) = unCSlice ce1

                csrc, csrcIdx :: CExp l
                (csrc, csrcIdx) = unCSlice ce2

            -- | We take the medium path when the source and destination are not
            -- both aligned on 'bIT_ARRAY_ELEM_BITS' bits, but when we
            -- statically know the indices into the source and destination and
            -- the number of bits to copy.
            mediumPath :: CExp l  -- ^ Destination
                       -> Integer -- ^ Destination index
                       -> CExp l  -- ^ Source
                       -> Integer -- ^ Source index
                       -> Integer -- ^ Number of bits to copy
                       -> Cg l ()
            -- If the source and destination are both slices of a single bit
            -- array element, we can copy with a fews shifts and masks.
            mediumPath cdst dstIdx csrc srcIdx n
              | sameBitArrayIdx dstIdx (dstIdx + n - 1) &&
                sameBitArrayIdx srcIdx (srcIdx + n - 1) =
                appendStm [cstm|$cdst' = $cres;|]
              where
                cdst', csrc', cres :: CExp l
                cdst' = CExp [cexp|$cdst[$didx]|]
                csrc' = CExp [cexp|$csrc[$sidx]|]
                cres  = cdst' ..&.. cdstmask ..|..
                        ((csrc' ..&.. csrcmask) `shift` csrcshift)

                cdstmask, csrcmask :: CExp l
                cdstmask  = CExp $ [cexp|~$(chexconst (nbitsMask `shiftL` fromIntegral doff))|]
                csrcmask  = CExp $ chexconst (nbitsMask `shiftL` fromIntegral soff)

                csrcshift :: Int
                csrcshift = fromIntegral (doff - soff)

                -- Bit mask for the low n bits
                nbitsMask :: Integer
                nbitsMask = (1 `shiftL` fromIntegral n) - 1

                -- Source and destination (index, offset) pairs into the source
                -- and destination bit arrays.
                sidx, soff, didx, doff :: Integer
                (sidx, soff) = bitArrayIdxOff srcIdx
                (didx, doff) = bitArrayIdxOff dstIdx

                -- Return 'True' if the two bit indicies are in the same element
                -- of the bit array.
                sameBitArrayIdx :: Integer -> Integer -> Bool
                sameBitArrayIdx i j = bitArrayIdx i == bitArrayIdx j

            mediumPath cdst dstIdx csrc srcIdx n =
                slowPath cdst (CInt dstIdx) csrc (CInt srcIdx) (CInt n)

            slowPath :: CExp l -> CExp l -> CExp l -> CExp l -> CExp l -> Cg l ()
            slowPath cdst cdstIdx csrc csrcIdx clen = do
                csrc' <- cgLower tau0 csrc
                incBitArrayCopies
                warndocWhen WarnBitArrayCopy $
                  nest 4 $
                  text "Bit array copy:" </> ppr ce1 <+> text ":=" <+> ppr ce2
                appendStm [cstm|kz_bitarray_copy($cdst, $cdstIdx, $csrc', $csrcIdx, $clen);|]

    assign mayAlias tau0 ce1 ce2 | Just (nat, tau_elem) <- checkArrOrRefArrT tau0 =
        case nat of
          NatT n _ | not (isArrT tau_elem) -> do
              bytes    <- typeSizeInBytes tau0
              minBytes <- asksConfig minMemcpyBytes
              if bytes >= minBytes
                then cgMemcpyArray nat tau_elem
                else cgAssignArray n tau_elem
          _ -> cgMemcpyArray nat tau_elem
      where
        cgAssignArray :: Int -> Type -> Cg l ()
        cgAssignArray n tau_elem =
            forM_ [0..n-1] $ \i ->
                let cdst_elem = CIdx tau_elem cdst (cdstIdx + fromIntegral i)
                    csrc_elem = CIdx tau_elem csrc (csrcIdx + fromIntegral i)
                in
                  appendStm [cstm|$cdst_elem = $csrc_elem;|]
          where
            cdst, cdstIdx :: CExp l
            (cdst, cdstIdx) = unCSlice ce1

            csrc, csrcIdx :: CExp l
            (csrc, csrcIdx) = unCSlice ce2

        cgMemcpyArray :: Type -> Type -> Cg l ()
        cgMemcpyArray n tau_elem = do
            ctau <- cgType tau_elem
            ce1' <- cgArrayAddr ce1
            ce2' <- cgArrayAddr ce2
            clen <- cgNatType n
            incMemCopies
            if mayAlias
              then appendStm [cstm|memmove($ce1', $ce2', $clen*sizeof($ty:ctau));|]
              else appendStm [cstm|memcpy($ce1', $ce2', $clen*sizeof($ty:ctau));|]
          where
            cgArrayAddr :: CExp l -> Cg l (CExp l)
            cgArrayAddr (CIdx tau carr cidx) | isArrT tau =
                return $ CExp [cexp|&$carr[$cidx]|]

            cgArrayAddr (CSlice tau _ _ _) | isBitT tau =
                panicdoc $ text "cgArrayAddr: the impossible happened!"

            cgArrayAddr (CSlice _ carr cidx _) =
                return $ CExp [cexp|&$carr[$cidx]|]

            cgArrayAddr (CAlias e ce) =
                calias e <$> cgArrayAddr ce

            cgArrayAddr ce =
                return ce

    assign _ tau cv (CStruct flds) = do
        (struct, taus) <- checkStructOrRefStructT tau
        structdef      <- lookupStruct struct
        mapM_ (cgAssignField structdef taus) flds
      where
        cgAssignField :: StructDef -> [Type] -> (Field, CExp l) -> Cg l ()
        cgAssignField structdef taus (fld, ce) = do
            tau <- checkStructFieldT structdef taus fld
            cgAssign tau (CExp [cexp|$cv.$id:(cfield fld)|]) ce

    -- We call 'cgDeref' on @cv@ because the lhs of an assignment is a ref type and
    -- may need to be dereferenced.
    assign _ _ cv ce =
        appendStm [cstm|$(cgDeref cv) = $ce;|]

cgBoundsCheck :: CExp l -> CExp l -> Cg l ()
cgBoundsCheck clen cidx = do
    boundsCheck <- asksConfig (testDynFlag BoundsCheck)
    when boundsCheck $
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
    return $ CExp [cexp|$ce.$id:(cfield fld)|]

-- | Dereference a 'CExp' representing a value with ref type, which may or may
-- not be represented as a pointer.
cgDeref :: CExp l -> CExp l
cgDeref (CPtr ce)     = CExp [cexp|*$ce|]
cgDeref (CAlias e ce) = calias e (cgDeref ce)
cgDeref ce            = ce

-- | Take the address of a 'CExp' representing a value of the given type.
cgAddrOf :: Type -> CExp l -> Cg l (CExp l)
cgAddrOf _ (CPtr ce) = do
    useCExp ce
    return ce

cgAddrOf tau (CAlias _ ce) = do
    useCExp ce
    cgAddrOf tau ce

cgAddrOf tau ce | isArrOrRefArrT tau && isLvalue ce = do
    useCExp ce
    return $ CExp [cexp|$ce|]

cgAddrOf _ ce | isLvalue ce = do
    useCExp ce
    return $ CExp [cexp|&$ce|]

cgAddrOf tau ce | isArrOrRefArrT tau = do
    ctemp <- cgTemp "addrof" tau
    cgAssign tau ctemp ce
    return $ CExp [cexp|$ctemp|]

cgAddrOf tau ce = do
    ctemp <- cgTemp "addrof" tau
    cgAssign tau ctemp ce
    return $ CExp [cexp|&$ctemp|]

cgWhile :: IsLabel l
        => SrcLoc
        -> Exp
        -> Cg l a
        -> Cg l ()
cgWhile l e_test mbody = do
    (citems_test, ce_test) <- inNewBlock $
                              cgExpOneshot e_test
    let cinits_test :: [C.InitGroup]
        cinits_test = map (rl l) [decl | C.BlockDecl decl <- citems_test]

        cstms_test :: [C.Stm]
        cstms_test = map (rl l) [stm | C.BlockStm stm <- citems_test]
    appendDecls cinits_test
    appendStms cstms_test
    -- We need to mark ce_test as used both before and after the loop body so
    -- that any bindings it may use are floated out to the proper scope, e.g.,
    -- if this is a computation while loop, any bindings used in the conditional
    -- will be floated out to thread scope.
    useCExp ce_test
    citems_body <- inNewBlock_ mbody
    useCExp ce_test
    appendStm $ rl l [cstm|while ($ce_test) {
                             $items:citems_body
                             $stms:cstms_test
                           }|]

-- | Generate code for an if statement.
cgIf :: forall l a . IsLabel l
     => Type
     -> Exp
     -> (forall a . Kont l a -> Cg l a)
     -> (forall a . Kont l a -> Cg l a)
     -> Kont l a
     -> Cg l a
cgIf tau e1 me2 me3 k | isPureT tau =
    cgExp e1 $ oneshot tau $ \ce1 -> do
    -- We need to lower ce2 and ce3 in case they are structs...
    ce2 <- me2 $ oneshot tau $ cgLower tau
    ce3 <- me3 $ oneshot tau $ cgLower tau
    runKont k $ CExp [cexp|$ce1 ? $ce2 : $ce3|]

cgIf tau e1 me2 me3 k | isOneshot k = do
    (oneshotk, k') <- splitOneshot k
    cgExp e1 $ oneshot tau $ \ce1 -> do
      citems2 <- inNewBlock_ $ me2 oneshotk
      citems3 <- inNewBlock_ $ me3 oneshotk
      let stm =  cif ce1 citems2 citems3
      appendStm stm
      -- See Note [Declaration Scopes]
      if hasLabel stm
        then newScope k'
        else k'

cgIf tau e1 me2 me3 k =
    cgExp e1 $ oneshot tau $ \ce1 -> do
    (citems2, x) <- inNewBlock $ me2 k
    (citems3, _) <- inNewBlock $ me3 k
    appendStm $ cif ce1 citems2 citems3
    return x

-- | Generate C code for a @for@ loop. @cfrom@ and @cto@ are the loop bounds,
-- and @k@ is a continuation that takes an expression representing the loop
-- index and generates the body of the loop.
cgFor :: IsLabel l => CExp l -> CExp l -> (CExp l -> Cg l ()) -> Cg l ()
cgFor cfrom@(CInt i) (CInt j) k
    | j <= i     = return ()
    | j == i + 1 = k cfrom

cgFor cfrom cto k = do
    ci :: C.Id <- gensym "__i"
    appendDecl [cdecl|int $id:ci;|]
    cgLoop Nothing $ do
        useCId ci
        useCExp cto
        cbody <- inNewBlock_ $
                 k (CExp [cexp|$id:ci|])
        appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) {
                          $items:cbody
                        }|]

-- | Lower a 'CExp' into a form we can use directly in an antiquotation.
cgLower :: Type -> CExp l -> Cg l (CExp l)
cgLower tau = go
  where
    go :: CExp l -> Cg l (CExp l)
    go ce@CStruct{} = do
        cv <- cgTemp "lower" tau
        cgAssign tau cv ce
        return cv

    go ce@CBits{} = do
        cbitElemType <- cgBitElemType
        ctau         <- cgBitcastType tau
        cv           <- cgCTemp ce "bits" ctau Nothing
        appendStm [cstm|$cv = $ce;|]
        return $ CExp [cexp|($ty:cbitElemType *) &$cv|]

    go (CAlias _ ce) =
        go ce

    go ce =
        return ce

-- | Generate code to jump to the specified label.
cgJump :: IsLabel l => l -> Cg l ()
cgJump l = do
    useLabel l
    appendStm [cstm|JUMP($id:l);|]

-- | Append a comment to the list of top-level definitions.
appendTopComment :: Doc -> Cg l ()
appendTopComment doc = appendTopDef [cedecl|$esc:(formatComment doc)|]

-- | Append a comment to the current sequence of statements.
appendComment :: Doc -> Cg l ()
appendComment doc = appendStm [cstm|$escstm:(formatComment doc)|]

formatComment :: Doc -> String
formatComment doc =
    pretty 80 $ group $
    text "/*" <+> align doc </> text "*/"

-- | Reture 'True' if 'CExp' requires a bit mask.
needsBitMask :: CExp l -> Bool
needsBitMask CSlice{}      = True
needsBitMask CPtr{}        = True
needsBitMask CBitSlice{}   = True
needsBitMask (CAlias _ ce) = needsBitMask ce
needsBitMask _             = False

-- | Return a C hex constant.
chexconst :: Integer -> C.Exp
chexconst i = C.Const (C.IntConst ("0x" ++ showHex i "") C.Unsigned i noLoc) noLoc

-- | Return the C identifier corresponding to a value that is an instance of
-- 'Named'.
cvar :: (Located a, Named a) => a -> Cg l C.Id
cvar x = reloc (locOf x) <$> gensym (zencode (namedString x))

cfield :: Field -> C.Id
cfield (Field n) = C.Id (zencode (cname n)) noLoc

cname :: Name -> String
cname n@Name{nameSort = Orig}              = namedString n
cname n@Name{nameSort = Internal (Uniq u)} = namedString n ++ "_" ++ show u

-- | Return the C identifier corresponding to a struct.
cstruct :: Struct -> SrcLoc -> C.Id
cstruct s = C.Id (zencode ((displayS . renderCompact . ppr) s "") ++ "_t")

-- | Construct a prettier if statement
cif :: C.ToExp ce => ce -> [C.BlockItem] -> [C.BlockItem] -> C.Stm
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
rl l = reloc (locOf l)
