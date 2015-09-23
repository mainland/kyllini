{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Cg
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg (
    evalCg,

    compileProgram
  ) where

import Control.Applicative ((<$>))
import Control.Monad (liftM)
import Control.Monad.Free (Free(..))
import Data.Char (ord)
import Data.Foldable (toList)
import Data.List (sort)
import Data.Loc
import Data.Monoid (mempty)
import qualified Language.C.Quote as C
import Language.C.Quote.C
import Numeric (showHex)
import Text.PrettyPrint.Mainland

import KZC.Cg.Monad
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Lint
import KZC.Lint.Monad
import KZC.Name
import KZC.Summary

cUR_KONT :: C.Id
cUR_KONT = C.Id "curk" noLoc

compileProgram :: [Decl] -> Cg ()
compileProgram decls = do
    appendTopDef [cedecl|$esc:("#include <kzc.h>")|]
    cgDecls decls $ do
    ST _ _ _ a b _ <- lookupVar "main"
    ca     <- cgType a
    cb     <- cgType b
    comp   <- cgExp (varE "main") >>= unCComp
    citems <- inNewBlock_ $ do
              -- Keep track of the current continuation. This is only used when
              -- we do not have first class labels.
              appendDecl [cdecl|typename KONT $id:cUR_KONT = LABELADDR($id:(ccompLabel comp));|]
              -- Generate code for the computation
              cgThread $ cgCComp take emit done (requireLabel comp)
    cgLabels
    appendTopDef [cedecl|
int main(int argc, char **argv)
{
    $ty:ca in[1];
    int i = 0;
    $ty:cb out[1];
    int j = 0;

    $items:citems
}|]
  where
    take :: TakeK
    take l 1 tau k1 k2 = do
        -- Generate a pointer to the current element in the buffer.
        ctau <- cgType tau
        cbuf <- cgCTemp "bufp" [cty|$ty:ctau *|] (Just [cinit|NULL|])
        cgWithLabel l $ do
        appendStm [cstm|$cbuf = &in[i++];|]
        k2 $ k1 $ CExp [cexp|*$cbuf|]

    take l n tau k1 k2 = do
        -- Generate a pointer to the current element in the buffer.
        ctau <- cgType tau
        cbuf <- cgCTemp "bufp" [cty|$ty:ctau *|] (Just [cinit|NULL|])
        cgWithLabel l $ do
        appendStm [cstm|$cbuf = &in[i];|]
        appendStm [cstm|i += $int:n;|]
        k2 $ k1 $ CExp [cexp|*$cbuf|]

    emit :: EmitK
    emit l (ConstI 1 _) ce ccomp k =
        cgWithLabel l $ do
        appendStm [cstm|out[j++] = $ce;|]
        k ccomp

    emit l iota ce ccomp k =
        cgWithLabel l $ do
        cn <- cgIota iota
        appendStm [cstm|memcpy(&out[j], $ce, $cn*sizeof(double));|]
        appendStm [cstm|j += $cn;|]
        k ccomp

    done :: DoneK
    done _ce =
        return ()

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
    let cds   =  (toList . decls) code
    let css   =  (toList . stmts) code
    appendDecls cds
    appendStms [cstms|BEGIN_DISPATCH; $stms:css END_DISPATCH;|]
    return x

cgDecls :: [Decl] -> Cg a -> Cg a
cgDecls [] k =
    k

cgDecls (decl:decls) k =
    cgDecl decl $ cgDecls decls k

cgDecl :: Decl -> Cg a -> Cg a
cgDecl decl@(LetD v tau e _) k = do
    cv <- withSummaryContext decl $ do
          let ce_comp = CDelay $
                        liftM CComp $
                        collectComp $
                        inSTScope tau $
                        cgExp e >>= unCComp
          ce <- if isComp tau
                then return ce_comp
                else inSTScope tau $ cgExp e
          cval v ce tau
    extendVars [(v, tau)] $ do
    extendVarCExps [(v, cv)] $ do
    k

cgDecl decl@(LetFunD f iotas vbs tau_ret e l) k = do
    cf <- cvar f
    extendVars [(f, tau)] $ do
    extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
    withSummaryContext decl $ do
        inSTScope tau_ret $ do
        extendIVars (iotas `zip` repeat IotaK) $ do
        extendVars vbs $ do
        citems <- inNewBlock_ $
                  inSTScope tau $ do
                  ciotas <- mapM cgIVarParam iotas
                  cvbs   <- mapM cgParam vbs
                  extendIVarCExps (iotas `zip` ciotas) $ do
                  extendVarCExps (map fst vbs `zip` cvbs) $ do
                  ce <- cgExp e
                  appendStm [cstm|return $ce;|]
        cparams1 <- mapM cgIVar iotas
        cparams2 <- mapM cgVarBind vbs
        ctau_ret <- cgType tau_ret
        appendTopDef [cedecl|$ty:ctau_ret $id:cf($params:(cparams1 ++ cparams2)) { $items:citems }|]
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

    cgIVarParam :: IVar -> Cg CExp
    cgIVarParam iv = do
        civ <- cvar iv
        return $ CExp [cexp|$id:civ|]

    cgParam :: (Var, Type) -> Cg CExp
    cgParam (v, RefT {}) = do
        cv <- cvar v
        return $ CPtr (CExp [cexp|$id:cv|])

    cgParam (v, _) = do
        cv <- cvar v
        return $ CExp [cexp|$id:cv|]

cgDecl decl@(LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $ do
    extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
    withSummaryContext decl $ do
        cparams1 <- mapM cgIVar iotas
        cparams2 <- mapM cgVarBind vbs
        ctau_ret <- cgType tau_ret
        appendTopDef [cedecl|$ty:ctau_ret $id:cf($params:(cparams1 ++ cparams2));|]
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

    cf :: C.Id
    cf = C.Id (namedString f) l

cgDecl decl@(LetRefD v tau maybe_e _) k = do
    cv <- cvar v
    withSummaryContext decl $ do
        ctau     <- cgType tau
        maybe_ce <- case maybe_e of
                      Nothing -> return Nothing
                      Just e -> Just <$> cgExp e
        appendDecl [cdecl|$ty:ctau $id:cv;|]
        case maybe_ce of
          Nothing -> return ()
          Just ce -> appendStm [cstm|$id:cv = $ce;|]
    extendVars [(v, refT tau)] $ do
    extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
    k

cgDecl decl _ =
    faildoc $ nest 2 $
    text "cgDecl: cannot compile:" <+/> ppr decl

cgExp :: Exp -> Cg CExp
cgExp e@(ConstE c _) =
    cgConst c
  where
    cgConst :: Const -> Cg CExp
    cgConst UnitC         = return CVoid
    cgConst (BoolC False) = return $ CExp [cexp|0|]
    cgConst (BoolC True)  = return $ CExp [cexp|1|]
    cgConst (BitC False)  = return $ CExp [cexp|0|]
    cgConst (BitC True)   = return $ CExp [cexp|1|]
    cgConst (IntC _ i)    = return $ CExp [cexp|$int:i|]
    cgConst (FloatC _ r)  = return $ CExp [cexp|$double:r|]
    cgConst (StringC s)   = return $ CExp [cexp|$string:s|]

    cgConst (ArrayC cs) = do
        tau    <- inferExp e
        cinits <- mapM cgConstInit cs
        carr   <- cgTemp "const_arr" tau (Just [cinit|{ $inits:cinits }|])
        return $ CArray (CInt (fromIntegral (length cs))) carr

    cgConstInit :: Const -> Cg C.Initializer
    cgConstInit c = do
        ce <- cgConst c
        return $ C.ExpInitializer (toExp ce l) l

    l :: SrcLoc
    l = srclocOf e

cgExp (VarE v _) =
    lookupVarCExp v

cgExp e0@(UnopE op e _) = do
    ce <- cgExp e
    cgUnop ce op
  where
    cgUnop :: CExp -> Unop -> Cg CExp
    cgUnop ce Lnot =
        return $ CExp [cexp|!$ce|]

    cgUnop ce Bnot =
        return $ CExp [cexp|~$ce|]

    cgUnop ce Neg =
        return $ CExp [cexp|-$ce|]

    cgUnop ce (Cast tau) = do
        ctau <- cgType tau
        return $ CExp [cexp|($ty:ctau) $ce|]

    cgUnop (CArray i _) Len =
        return i

    cgUnop ce Len =
        faildoc $ nest 2 $
        text "cgUnop: cannot compile:" <+/> ppr e0 </>
        text "sub-expression compiled to:" <+> ppr ce

cgExp (BinopE op e1 e2 _) = do
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    return $ CExp $ cgBinop ce1 ce2 op
  where
    cgBinop :: CExp -> CExp -> Binop -> C.Exp
    cgBinop ce1 ce2 Lt   = [cexp|$ce1 <  $ce2|]
    cgBinop ce1 ce2 Le   = [cexp|$ce1 <= $ce2|]
    cgBinop ce1 ce2 Eq   = [cexp|$ce1 == $ce2|]
    cgBinop ce1 ce2 Ge   = [cexp|$ce1 >= $ce2|]
    cgBinop ce1 ce2 Gt   = [cexp|$ce1 >  $ce2|]
    cgBinop ce1 ce2 Ne   = [cexp|$ce1 != $ce2|]
    cgBinop ce1 ce2 Land = [cexp|$ce1 && $ce2|]
    cgBinop ce1 ce2 Lor  = [cexp|$ce1 || $ce2|]
    cgBinop ce1 ce2 Band = [cexp|$ce1 &  $ce2|]
    cgBinop ce1 ce2 Bor  = [cexp|$ce1 |  $ce2|]
    cgBinop ce1 ce2 Bxor = [cexp|$ce1 ^  $ce2|]
    cgBinop ce1 ce2 LshL = [cexp|$ce1 << $ce2|]
    cgBinop ce1 ce2 LshR = [cexp|$ce1 >> $ce2|]
    cgBinop ce1 ce2 AshR = [cexp|((unsigned int) $ce1) >> $ce2|]
    cgBinop ce1 ce2 Add  = [cexp|$ce1 + $ce2|]
    cgBinop ce1 ce2 Sub  = [cexp|$ce1 - $ce2|]
    cgBinop ce1 ce2 Mul  = [cexp|$ce1 * $ce2|]
    cgBinop ce1 ce2 Div  = [cexp|$ce1 / $ce2|]
    cgBinop ce1 ce2 Rem  = [cexp|$ce1 % $ce2|]
    cgBinop ce1 ce2 Pow  = [cexp|pow($ce1, $ce2)|]

cgExp e@(IfE e1 e2 e3 _) = do
    inferExp e >>= go
  where
    go :: Type -> Cg CExp
    go tau | isPureish tau = do
        cv <- cgTemp "cond" cv_tau Nothing
        cif (cgExp e1)
            (cgExp e2 >>= cassign cv_tau cv)
            (cgExp e3 >>= cassign cv_tau cv)
        return cv
      where
        cv_tau :: Type
        cv_tau = computedType tau

    go tau = do
        ce1       <- cgExp e1
        comp2     <- collectComp $ cgExp e2 >>= unCComp
        comp3     <- collectComp $ cgExp e3 >>= unCComp
        cv        <- cgTemp "cond" cv_tau Nothing
        ifl       <- genLabel "ifk"
        bindthl   <- genLabel "then_bindk"
        donethl   <- genLabel "then_donek"
        bindell   <- genLabel "else_bindk"
        doneell   <- genLabel "else_donek"
        return $ CComp $
            ifC ifl cv ce1
                (comp2 >>= bindC bindthl cv_tau cv >> doneC donethl)
                (comp3 >>= bindC bindell cv_tau cv >> doneC doneell)
      where
        cv_tau :: Type
        cv_tau = computedType tau

cgExp (LetE decl e _) =
    cgDecl decl $ cgExp e

cgExp (CallE f iotas es _) = do
    cf     <- cgExp f
    ciotas <- mapM cgIota iotas
    ces    <- mapM cgExp es
    return $ CExp [cexp|$cf($args:ciotas, $args:ces)|]

cgExp (DerefE e _) = do
    ce <- cgExp e
    case ce of
      CPtr {} -> return $ CExp [cexp|*$ce|]
      _       -> return ce

cgExp (AssignE e1 e2 _) = do
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    appendStm [cstm|$ce1 = $ce2;|]
    return CVoid

cgExp e0@(WhileE e_test e_body _) = do
    inferExp e0 >>= go
  where
    go :: Type -> Cg CExp
    -- This case will only be invoked when the surrounding computation is
    -- pureish since @tau@ is always instantiated with the surrounding
    -- function's ST index variables.
    go tau | isPureish tau = do
        ce_test <- cgExp e_test
        ce_body <- cgExp e_body
        appendStm [cstm|while ($ce_test) { $ce_body; }|]
        return CVoid

    go _ = do
        ce_test <- cgExp e_test
        bodyc   <- collectComp $ cgExp e_body >>= unCComp
        whilel  <- genLabel "whilek"
        donel   <- genLabel "whiledone"
        return $ CComp $ requireLabel $
            ifC whilel CVoid ce_test
                (bodyc >> gotoC whilel)
                (doneC donel)

{-
cgExp e0@(ForE _ v v_tau e_start e_end e_body _) = do
    tau    <- inferExp e0
    ce_body  <- cgExp e_body
    go tau
  where
    go :: Type -> Cg CExp
    go tau | isPureish tau = do
        cv     <- cvar v
        cv_tau <- cgType tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendDecl [cdecl|$ty:ctau $id:cv;|]
        ce_start <- cgExp e_start
        ce_end   <- cgExp e_end
        citems   <- inNewBlock_ $ cgExp e_body
        appendStm [cstm|for ($id:cv = $ce_start; $id:cv < $ce_end; $id:cv++) { $items:citems }|]
        return CVoid

    go _ = do
        cv     <- cvar v
        cv_tau <- cgType tau
        extendVars     [(v, v_tau)] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        appendDecl [cdecl|$ty:ctau $id:cv;|]
        ce_start <- cgExp e_start
        ce_end   <- cgExp e_end
        appendStm  [cstm|$id:cv = $ce_start|]


        citems   <- inNewBlock_ $ cgExp e_body
        appendStm [cstm|for ($id:cv = $ce_start; $id:cv < $ce_end; $id:cv++) { $items:citems }|]
        return CVoid
-}

cgExp (IdxE e1 e2 Nothing _) = do
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    return $ CExp [cexp|$ce1[$ce2]|]

cgExp (ReturnE _ e _) = do
    ce <- cgExp e
    return $ CComp $ return ce

cgExp (BindE bv@(BindV v tau) e1 e2 _) = do
    comp1 <- collectComp (cgExp e1 >>= unCComp)
    cve   <- cgVar v tau
    -- We create a CComp containing all the C code needed to define and bind @v@
    -- and then execute @e2@.
    comp2 <- collectCompBind $
             extendBindVars [bv] $
             extendVarCExps [(v, cve)] $ do
             bindl <- genLabel "bindk"
             comp2 <- collectComp (cgExp e2 >>= unCComp)
             return $ \ce -> bindC bindl tau cve ce >> comp2
    return $ CComp $ comp1 >>= comp2

cgExp (BindE WildV e1 e2 _) = do
    comp1 <- collectComp (cgExp e1 >>= unCComp)
    comp2 <- collectComp (cgExp e2 >>= unCComp)
    return $ CComp $ comp1 >> comp2

cgExp (TakeE tau _) = do
    l <- genLabel "takek"
    return $ CComp $ takeC l tau

cgExp (TakesE i tau _) = do
    l <- genLabel "takesk"
    return $ CComp $ takesC l i tau

cgExp (EmitE e _) = liftM CComp $ collectComp $ do
    l  <- genLabel "emitk"
    ce <- cgExp e
    return $ emitC l ce

cgExp (EmitsE e _) = liftM CComp $ collectComp $ do
    l         <- genLabel "emitsk"
    (iota, _) <- inferExp e >>= splitArrT
    ce        <- cgExp e
    return $ emitsC l iota ce

cgExp (RepeatE _ e _) = do
    ccomp  <- cgExp e >>= unCComp
    let l  =  ccompLabel ccomp
    return $ CComp $ requireLabel ccomp >> gotoC l

cgExp (ParE _ tau e1 e2 _) = do
    comp1 <- cgExp e1 >>= unCComp
    comp2 <- cgExp e2 >>= unCComp
    return $ CComp $ parC tau comp1 comp2

cgExp e =
    faildoc $ nest 2 $
    text "cgExp: cannot compile:" <+/> ppr e

collectComp :: Cg CComp -> Cg CComp
collectComp m = do
    l            <- genLabel "codek"
    (comp, code) <- collect m
    return $ codeC l code >> comp

collectCompBind :: Cg (CExp -> CComp) -> Cg (CExp -> CComp)
collectCompBind m = do
    l             <- genLabel "codek"
    (compf, code) <- collect m
    return $ \ce -> codeC l code >> compf ce

cgIVar :: IVar -> Cg C.Param
cgIVar iv = do
    civ <- cvar iv
    return $ [cparam|int $id:civ|]

cgVarBind :: (Var, Type) -> Cg C.Param
cgVarBind (v, tau) = do
    ctau <- cgType tau
    cv   <- cvar v
    return $ [cparam|$ty:ctau $id:cv|]

cgIota :: Iota -> Cg CExp
cgIota (ConstI i _) = return $ CInt (fromIntegral i)
cgIota (VarI iv _)  = lookupIVarCExp iv

{-
unCArray :: CExp -> Cg (CExp, CExp)
unCArray (CArray ce1 ce2) =
    return (ce1, ce2)

unCArray ce =
    panicdoc $
    text "unCArray: not a compiled array:" <+> ppr ce
-}

unCComp :: CExp -> Cg CComp
unCComp (CComp comp) =
    return comp

unCComp (CDelay m) =
    m >>= unCComp

unCComp ce =
    return $ return ce

cgType :: Type -> Cg C.Type
cgType (UnitT {}) =
    return [cty|void|]

cgType (BoolT {}) =
    return [cty|int|]

cgType (BitT {}) =
    return [cty|int|]

cgType (IntT W8 _) =
    return [cty|typename int8_t|]

cgType (IntT W16 _) =
    return [cty|typename int16_t|]

cgType (IntT W32 _) =
    return [cty|typename int32_t|]

cgType (IntT W64 _) =
    return [cty|typename int64_t|]

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

cgType (StructT s _) =
    return [cty|typename $id:(namedString s ++ "_struct_t")|]

cgType (ArrT _ tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (ST _ (C tau) _ _ _ _) =
    cgType tau

cgType (ST _ T _ _ _ _)=
    return [cty|void|]

cgType (RefT tau _) = do
    ctau <- cgType tau
    return [cty|$ty:ctau*|]

cgType (FunT ivs args ret _) = do
    let ivTys =  replicate (length ivs) [cparam|int|]
    argTys    <- mapM cgParam args
    retTy     <- cgType ret
    return [cty|$ty:retTy (*)($params:(ivTys ++ argTys))|]

cgType (TyVarT {}) =
    return [cty|void|]

cgParam :: Type -> Cg C.Param
cgParam tau = do
    ctau <- cgType tau
    return [cparam|$ty:ctau|]

cgVar :: Var -> Type -> Cg CExp
cgVar _ (UnitT {}) =
    return CVoid

cgVar v tau = do
    ctau <- cgType tau
    cv   <- cvar v
    appendDecl [cdecl|$ty:ctau $id:cv;|]
    return $ CExp [cexp|$id:cv|]

cgTemp :: String -> Type -> Maybe C.Initializer -> Cg CExp
cgTemp _ (UnitT {}) _ =
    return CVoid

cgTemp s tau maybe_cinit = do
    ctau <- cgType tau
    cgCTemp s ctau maybe_cinit

cgCTemp :: String -> C.Type -> Maybe C.Initializer -> Cg CExp
cgCTemp s ctau maybe_cinit = do
    cv <- gensym s
    case maybe_cinit of
      Nothing    -> appendDecl [cdecl|$ty:ctau $id:cv;|]
      Just cinit -> appendDecl [cdecl|$ty:ctau $id:cv = $init:cinit;|]
    return $ CExp [cexp|$id:cv|]

cvar :: Named a => a -> Cg C.Id
cvar x = gensym (concatMap zencode (namedString x))
  where
    -- | Implementation of Z-encoding. See:
    -- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
    zencode :: Char -> [Char]
    zencode c | 'a' <= c && c <= 'y' = [c]
              | 'A' <= c && c <= 'Y' = [c]
              | '0' <= c && c <= '9' = [c]
    zencode 'z'  = "zz"
    zencode 'Z'  = "ZZ"
    zencode '('  = "ZL"
    zencode ')'  = "ZR"
    zencode '['  = "ZM"
    zencode ']'  = "ZN"
    zencode ':'  = "ZC"
    zencode '&'  = "za"
    zencode '|'  = "zb"
    zencode '^'  = "zc"
    zencode '$'  = "zd"
    zencode '='  = "ze"
    zencode '>'  = "zg"
    zencode '#'  = "zh"
    zencode '.'  = "zi"
    zencode '<'  = "zl"
    zencode '-'  = "zm"
    zencode '!'  = "zn"
    zencode '+'  = "zp"
    zencode '\'' = "zq"
    zencode '\\' = "zr"
    zencode '/'  = "zs"
    zencode '*'  = "zt"
    zencode '_'  = "zu"
    zencode '%'  = "zv"
    zencode c    = "z" ++ hexOf c ++ "U"

    hexOf :: Char -> String
    hexOf c =
        case showHex (ord c) "" of
          [] -> []
          h@(c : _) | 'a' <= c && c <= 'f' -> '0' : h
                    | otherwise            -> h

isComp :: Type -> Bool
isComp (ST {}) = True
isComp _       = False

isPureish :: Type -> Bool
isPureish (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) | sort [s,a,b] == sort [s',a',b'] =
    True

isPureish (ST {}) =
    False

isPureish _ =
    True

cfor :: CExp -> CExp -> (CExp -> Cg a) -> Cg a
cfor cfrom cto k = do
    ci <- gensym "i"
    appendDecl [cdecl|int $id:ci;|]
    (cbody, x) <- inNewBlock $
                  k (CExp [cexp|$id:ci|])
    appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) { $items:cbody }|]
    return x

{-
cidx :: CExp -> CExp -> CExp
cidx carr cidx = CExp [cexp|$carr[$cidx]|]
-}

cval :: Var -> CExp -> Type -> Cg CExp
cval _ ce@(CComp {}) _ =
    return ce

cval _ ce@(CDelay {}) _ =
    return ce

cval v ce tau = do
    cv   <- cvar v
    ctau <- cgType tau
    appendDecl [cdecl|$ty:ctau $id:cv;|]
    appendStm [cstm|$id:cv = $ce;|]
    return $ CExp [cexp|$id:cv|]

-- | Label the statements generated by the continuation @k@ with the specified
-- label. We only generate a C label when the label is 'Required'.
cgWithLabel :: Required Label -> Cg a -> Cg a
cgWithLabel (Required lbl@(C.Id ident l)) k = do
    useLabel lbl
    (stms, x) <- collectStms k
    case stms of
      []     -> panicdoc $ text "cgWithLabel: no statements!"
      [s]    -> appendStm [cstm|$id:lblMacro: $stm:s|]
      (s:ss) -> appendStms [cstms|$id:lblMacro: $stm:s $stms:ss|]
    return x
  where
    -- We need to use the @LABEL@ macro on the label. Gross, but what can ya
    -- do...
    lblMacro :: Label
    lblMacro = C.Id ("LABEL(" ++ ident ++ ")") l

cgWithLabel (Required (C.AntiId {})) _ =
    panicdoc $ text "cgWithLabel saw C.AntiId!"

cgWithLabel _ k =
    k

-- | A 'TakeK' continuation takes a label, the number of elements to take, the type of the
-- elements, a continuation that computes a 'CComp' from the 'CExp' representing
-- the taken elements, and a continuation that generates code corresponding to
-- the 'CComp' returned by the first continuation. Why not one continuation of
-- type @CExp -> Cg ()@ instead of two that we have to manually chain together?
-- In general, we may want look inside the 'CComp' to see what it does with the
-- taken values. In particular, we need to see the label of the 'CComp' so that
-- we can save it as a continuation.
type TakeK = Required Label -> Int -> Type -> (CExp -> CComp) -> (CComp -> Cg ()) -> Cg ()

-- | A 'EmitK' continuation takes a label, an 'Iota' representing the number of elements
-- to emit, a 'CExp' representing the elements to emit, a 'CComp' representing
-- the emit's continuation, and a continuation that generates code corresponding
-- to the 'CComp'. We split the continuation into two parts just as we did for
-- 'TakeK' for exactly the same reason.
type EmitK = Required Label -> Iota -> CExp -> CComp -> (CComp -> Cg ()) -> Cg ()

-- | A 'DoneK' continuation takes a 'CExp' representing the returned value and
-- generates the appropriate code.
type DoneK = CExp -> Cg ()

cgCComp :: TakeK
        -> EmitK
        -> DoneK
        -> CComp
        -> Cg ()
cgCComp take emit done ccomp =
    cgFree ccomp
  where
    cgFree :: CComp -> Cg ()
    cgFree (Pure ce) = done ce
    cgFree (Free x)  = cgComp x

    cgComp :: Comp Label CComp -> Cg ()
    cgComp (CodeC l c k) = cgWithLabel l $ do
        tell c
        cgFree k

    cgComp (TakeC l tau k) =
        take l 1 tau k cgFree

    cgComp (TakesC l n tau k) =
        take l n tau k cgFree

    cgComp (EmitC l ce k) =
        emit l (ConstI 1 noLoc) ce k cgFree

    cgComp (EmitsC l iota ce k) =
        emit l iota ce k cgFree

    cgComp (IfC l cv ce thenk elsek k) = cgWithLabel l $ do
        cif (return ce) (cgFree thenk) (cgFree elsek)
        cgFree (k cv)

    cgComp (ParC tau left right) =
        cgParSingleThreaded tau left right

    cgComp (BindC l tau cv ce k) = cgWithLabel l $ do
        cassign tau cv ce
        cgFree k

    cgComp (DoneC {}) =
        done CVoid

    cgComp (GotoC l) =
        appendStm [cstm|JUMP($id:(unRequired l));|]

    cgParSingleThreaded :: Type -> CComp -> CComp -> Cg ()
    cgParSingleThreaded tau left right = do
        -- Generate variables to hold the left and right computations'
        -- continuations.
        cleftk  <- cgCTemp "leftk"  [cty|typename KONT|] (Just [cinit|LABELADDR($id:(ccompLabel left))|])
        crightk <- cgCTemp "rightk" [cty|typename KONT|] (Just [cinit|LABELADDR($id:(ccompLabel right))|])
        -- Generate a pointer to the current element in the buffer.
        ctau <- cgType tau
        cbuf <- cgCTemp "bufp" [cty|$ty:ctau *|] (Just [cinit|NULL|])
        -- Generate code for the left and right computations.
        cgCComp (take' cleftk crightk cbuf) emit                        done (requireLabel right)
        cgCComp take                        (emit' cleftk crightk cbuf) done (requireLabel left)
      where
        take' :: CExp -> CExp -> CExp -> TakeK
        -- The one element take is easy. We know the element will be in @cbuf@,
        -- so we call @k1@ with @cbuf@ as the argument, which generates a
        -- 'CComp', @ccomp@ that represents the continuation that consumes the
        -- taken value. We then set the right computation's continuation to the
        -- label of @ccomp@, since it is the continuation, generate code to jump
        -- to the left computation's continuation, and then call @k2@ with
        -- @ccomp@ suitably modified to have a required label.
        take' cleftk crightk cbuf l 1 _tau k1 k2 = cgWithLabel l $ do
            let ccomp = k1 $ CExp [cexp|*$cbuf|]
            let lbl   = ccompLabel ccomp
            appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
            appendStm [cstm|INDJUMP($cleftk);|]
            k2 (requireLabel ccomp)

        -- The multi-element take is a bit tricker. We allocate a buffer to hold
        -- all the elements, and then loop, jumping to the left computation's
        -- continuation repeatedly, until the buffer is full. Then we fall
        -- through to the next action, which is why we call @k2@ with @ccomp@
        -- without forcing its label to be required---we don't need the label!
        take' cleftk crightk cbuf l n tau k1 k2 = cgWithLabel l $ do
            ctau      <- cgType tau
            carr      <- cgCTemp "xs" [cty|$ty:ctau[$int:n]|] Nothing
            lbl       <- genLabel "inner_takesk"
            let ccomp =  k1 carr
            appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
            cfor 0 (fromIntegral n) $ \ci -> do
                appendStm [cstm|INDJUMP($cleftk);|]
                cgWithLabel (Required lbl) $
                    appendStm [cstm|$carr[$ci] = *$cbuf;|]
            k2 ccomp

        emit' :: CExp -> CExp -> CExp -> EmitK
        emit' cleftk crightk cbuf l (ConstI 1 _) ce ccomp k = cgWithLabel l $ do
            let lbl = ccompLabel ccomp
            appendStm [cstm|$cleftk = LABELADDR($id:lbl);|]
            appendStm [cstm|$cbuf = &$ce;|]
            appendStm [cstm|INDJUMP($crightk);|]
            k (requireLabel ccomp)

        emit' cleftk crightk cbuf l iota ce ccomp k = do
            let lbl =  unRequired l
            cn      <- cgIota iota
            appendStm [cstm|$cleftk = LABELADDR($id:lbl);|]
            cfor 0 cn $ \ci -> do
                appendStm [cstm|$cbuf = &($ce[$ci]);|]
                appendStm [cstm|INDJUMP($crightk);|]
                -- Because we need a statement to label, but the continuation is
                -- the next loop iteration...
                cgWithLabel (require l) $
                    appendStm [cstm|continue;|]
            k (requireLabel ccomp)

cassign :: Type -> CExp -> CExp -> Cg ()
cassign (UnitT {}) _ _ =
    return ()

cassign _ cv ce =
    appendStm [cstm|$cv = $ce;|]

cif :: Cg CExp -> Cg () -> Cg () -> Cg ()
cif e1 e2 e3 = do
    ce1     <- e1
    citems2 <- inNewBlock_ e2
    citems3 <- inNewBlock_ e3
    if citems3 == mempty
      then appendStm [cstm|if ($ce1) { $items:citems2 }|]
      else appendStm [cstm|if ($ce1) { $items:citems2 } else { $items:citems3 }|]

computedType :: Type -> Type
computedType (ST _ (C tau) _ _ _ _) = tau
computedType tau                    = tau
