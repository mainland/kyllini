{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Target.Standalone
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Target.Standalone (
    compileProgram
  ) where

import Prelude

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Loc
import Data.String (IsString(..))
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Backend.C
import KZC.Backend.C.CExp
import KZC.Backend.C.Monad
import KZC.Backend.C.Util
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Label
import KZC.Monad (KZC)
import KZC.Quote.C
import KZC.Util.Staged
import KZC.Util.Uniq

compileProgram :: IsLabel l => Program l -> KZC [C.Definition]
compileProgram = evalCg . cgProgram

cgProgram :: forall l . IsLabel l => Program l -> Cg l ()
cgProgram (Program _imports decls maybe_main) = do
    Main comp tau <- maybe (fail "No main computation!")
                           return
                           maybe_main
    -- If the top-level computation consists of a single repeat, record that
    -- fact. We use this to test fusion.
    case unComp comp of
      [RepeatC{}] -> topIsRepeat
      _           -> return ()
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
    takek tau _klbl (k :: CExp l -> Cg l a) = do
        cinput   <- cgInput tau (CExp [cexp|$id:in_buf|]) 1
        zeroSize <- hasZeroTypeSize tau
        takeInput zeroSize cinput
      where
        takeInput :: Bool -> CExp l -> Cg l a
        takeInput True cinput = do
            if [cexp|$cinput == 0|]
              then cgExit
              else return ()
            k CVoid

        takeInput False cinput = do
            -- Generate a pointer to the current element in the buffer.
            ctau <- cgType tau
            cbuf <- cgThreadCTemp tau "take_bufp" [cty|$tyqual:calign const $ty:ctau*|] (Just [cinit|NULL|])
            if [cexp|($cbuf = (const $ty:ctau*) $cinput) == NULL|]
              then cgExit
              else return ()
            k $ cgBufElem tau cbuf
          where
            cgBufElem tau cbuf
              | isBitT tau    = CExp [cexp|*$cbuf & 1|]
              | isBitArrT tau = CBitSlice $ CExp [cexp|*$cbuf|]
              | otherwise     = CExp [cexp|*$cbuf|]

    takesk :: TakesK l
    takesk n tau _klbl (k :: CExp l -> Cg l a) = do
        cinput   <- cgInput tau (CExp [cexp|$id:in_buf|]) (fromIntegral n)
        zeroSize <- hasZeroTypeSize tau
        takeInput zeroSize cinput
      where
        takeInput :: Bool -> CExp l -> Cg l a
        takeInput True cinput = do
            if [cexp|$cinput == 0|]
              then cgExit
              else return ()
            k CVoid

        takeInput False cinput = do
            -- Generate a pointer to the current element in the buffer.
            ctau <- cgType tau
            cbuf <- cgThreadCTemp tau "take_bufp" [cty|$tyqual:calign const $ty:ctau*|] (Just [cinit|NULL|])
            if [cexp|($cbuf = (const $ty:ctau*) $cinput) == NULL|]
              then cgExit
              else return ()
            k $ cgBufElem tau cbuf
          where
            cgBufElem tau cbuf
              | isBitT tau = CBitSlice $ CExp [cexp|$cbuf|]
              | otherwise  = CExp [cexp|$cbuf|]

    emitk :: EmitK l
    emitk tau ce _klbl k = do
        zeroSize <- hasZeroTypeSize tau
        ceElem   <- if zeroSize then return CVoid else cgAddrOf tau ce
        cgOutput tau (CExp [cexp|$id:out_buf|]) 1 ceElem
        k

    emitsk :: EmitsK l
    emitsk n tau ce _klbl k = do
        zeroSize <- hasZeroTypeSize tau
        emitOutput zeroSize
        k
      where
        emitOutput :: Bool -> Cg l ()
        emitOutput True = do
            cn <- cgNatType n
            cgOutput tau (CExp [cexp|$id:out_buf|]) cn CVoid

        emitOutput False = do
            ceAddr <- cgAddrOf (arrT n tau) ce
            cgOutput (arrT n tau) (CExp [cexp|$id:out_buf|]) 1 ceAddr

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
    cgBufferConfig appStm f tau cp cbuf = do
        zeroSize <- hasZeroTypeSize tau
        if zeroSize
          then appStm [cstm|$id:(fname "unit")($cp, &$cbuf);|]
          else go tau
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
              Just tau | tau == intT   -> appStm [cstm|$id:(fname "complex")($cp, &$cbuf);|]
                       | tau == int16T -> appStm [cstm|$id:(fname "complex16")($cp, &$cbuf);|]
                       | tau == int32T -> appStm [cstm|$id:(fname "complex32")($cp, &$cbuf);|]
              _                        -> appStm [cstm|$id:(fname "bytes")($cp, &$cbuf);|]

        go _ =
            appStm [cstm|$id:(fname "bytes")($cp, &$cbuf);|]

        fname :: String -> C.Id
        fname t = fromString (f ++ "_" ++ t)

    cgInput :: Type -> CExp l -> CExp l -> Cg l (CExp l)
    cgInput tau cbuf cn = do
        zeroSize <- hasZeroTypeSize tau
        if zeroSize
          then return $ CExp [cexp|kz_input_unit(&$cbuf, $cn)|]
          else go tau
      where
        go :: Type -> Cg l (CExp l)
        go (ArrT nat tau _)  = do ci <- cgNatType nat
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
              Just tau | tau == intT   -> return $ CExp [cexp|kz_input_complex(&$cbuf, $cn)|]
                       | tau == int16T -> return $ CExp [cexp|kz_input_complex16(&$cbuf, $cn)|]
                       | tau == int32T -> return $ CExp [cexp|kz_input_complex32(&$cbuf, $cn)|]
              _                        -> do ctau <- cgType tau
                                             return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

        go tau = do
            ctau <- cgType tau
            return $ CExp [cexp|kz_input_bytes(&$cbuf, $cn*sizeof($ty:ctau))|]

    cgOutput :: Type -> CExp l -> CExp l -> CExp l -> Cg l ()
    cgOutput tau cbuf cn cval = do
        zeroSize <- hasZeroTypeSize tau
        if zeroSize
          then appendStm [cstm|kz_output_unit(&$cbuf, $cn);|]
          else go tau
      where
        go :: Type -> Cg l ()
        go (ArrT nat tau _)   = do ci <- cgNatType nat
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
              Just tau | tau == intT   -> appendStm [cstm|kz_output_complex(&$cbuf, $cval, $cn);|]
                       | tau == int16T -> appendStm [cstm|kz_output_complex16(&$cbuf, $cval, $cn);|]
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

    -- | Generate code to check return value of a function call at thread
    -- initialization time.
    cgInitCheckErr :: Located a => C.Exp -> String -> a -> Cg l ()
    cgInitCheckErr ce msg x =
        appendThreadInitStm [cstm|kz_check_error($ce, $string:(renderLoc x), $string:msg);|]

cgTimed :: Cg l a -> Cg l a
cgTimed k = do
    flags <- askConfig
    withTimers flags $
      withCycles flags
      k
  where
    withTimers :: Config -> Cg l a -> Cg l a
    withTimers flags k | testDynFlag Timers flags = do
        cpu_time_start  :: C.Id <- gensym "cpu_time_start"
        cpu_time_end    :: C.Id <- gensym "cpu_time_end"
        real_time_start :: C.Id <- gensym "real_time_start"
        real_time_end   :: C.Id <- gensym "real_time_end"
        appendTopDecl [cdecl|static long double $id:cpu_time_start, $id:cpu_time_end;|]
        appendTopDecl [cdecl|static long double $id:real_time_start, $id:real_time_end;|]
        appendStm [cstm|$id:cpu_time_start = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_start = kz_get_real_time();|]
        x <- k
        appendStm [cstm|$id:cpu_time_end = kz_get_cpu_time();|]
        appendStm [cstm|$id:real_time_end = kz_get_real_time();|]
        appendStm [cstm|printf("Time elapsed (usec): %d\n", (int) (($id:cpu_time_end - $id:cpu_time_start) * 1000000));|]
        appendStm [cstm|printf("Elapsed cpu time (sec): %Le\n", $id:cpu_time_end - $id:cpu_time_start);|]
        appendStm [cstm|printf("Elapsed real time (sec): %Le\n", $id:real_time_end - $id:real_time_start);|]
        return x

    withTimers _flags k =
        k

    withCycles :: Config -> Cg l a -> Cg l a
    withCycles flags k | testDynFlag Cycles flags = do
        cycles_start :: C.Id <- gensym "cycles_start"
        cycles_end   :: C.Id <- gensym "cycles_end"
        appendTopDecl [cdecl|static typename cycles $id:cycles_start, $id:cycles_end;|]
        appendStm [cstm|$id:cycles_start = kz_cycles_start();|]
        x <- k
        appendStm [cstm|$id:cycles_end = kz_cycles_end();|]
        appendStm [cstm|printf("Elapsed cycles: %ld\n", $id:cycles_end - $id:cycles_start);|]
        return x

    withCycles _flags k =
        k
