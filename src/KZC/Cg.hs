{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  KZC.Cg
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg (
    evalCg,
    cgCComp,

    compileProgram
  ) where

import Control.Applicative ((<$>))
import Control.Monad (void)
import Control.Monad.Free (Free(..),
                           liftF)
import Data.Char (ord)
import Data.List (sort)
import Data.Loc
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
import KZC.Uniq

compileProgram :: [Decl] -> Cg ()
compileProgram decls =
    cgDecls decls $ do
    comp <- cgExp (varE "main") >>= unCComp
    let take    = return $ CExp [cexp|buf[i++]|]
    let emit ce = appendStm [cstm|emit($ce);|]
    (citems, _) <- inNewBlock $ cgCComp take emit comp
    appendTopDef [cedecl|
int main(int argc, char **argv)
{
    int buf[1];
    int i = 0;

    $items:citems
}|]


cgDecls :: [Decl] -> Cg a -> Cg a
cgDecls [] k =
    k

cgDecls (decl:decls) k =
    cgDecl decl $ cgDecls decls k

cgDecl :: Decl -> Cg a -> Cg a
cgDecl (LetD v tau e _) k =
    inSTScope tau $ do
    ce <- cgExp e
    cv <- cval v ce tau
    extendVars [(v, tau)] $ do
    extendVarCExps [(v, cv)] $ do
    k

cgDecl (LetFunD f iotas vbs tau_ret e l) k =
    extendVars [(f, tau)] $ do
    cf <- cvar f
    extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
    citems <- inNewBlock_ $
              extendIVars (iotas `zip` repeat IotaK) $
              extendVars vbs $ do
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

cgDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $ do
    let cf = C.Id (namedString f) l
    extendVarCExps [(f, CExp [cexp|$id:cf|])] $ do
    cparams1 <- mapM cgIVar iotas
    cparams2 <- mapM cgVarBind vbs
    ctau_ret <- cgType tau_ret
    appendTopDef [cedecl|$ty:ctau_ret $id:cf($params:(cparams1 ++ cparams2));|]
    k
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

cgDecl (LetRefD v tau maybe_e _) k = do
    cv       <- cvar v
    ctau     <- cgType tau
    maybe_ce <- case maybe_e of
                  Nothing -> return Nothing
                  Just e -> Just <$> cgExp e
    appendDecl [cdecl|$ty:ctau $id:cv;|]
    extendVars [(v, refT tau)] $ do
    extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
    case maybe_ce of
      Nothing -> return ()
      Just ce -> appendStm [cstm|$id:cv = $ce;|]
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
    tau <- inferExp e
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    ce3 <- cgExp e3
    go tau ce1 ce2 ce3
  where
    go :: Type -> CExp -> CExp -> CExp -> Cg CExp
    go tau ce1 ce2 ce3 | isPureish tau = do
        cv <- cgTemp "cond" tau Nothing
        appendStm [cstm|if ($ce1) { $cv = $ce2; } else { $cv = $ce3;}|]
        return cv

    go tau ce1 ce2 ce3 = do
        comp2 <- unCComp ce2
        comp3 <- unCComp ce3
        return $ CComp $ Free $ IfC tau ce1 comp2 comp3 (\_ -> return CVoid)

cgExp (LetE decl e _) =
    cgDecl decl $ cgExp e

cgExp (CallE f iotas es _) = do
    cf     <- cgExp f
    ciotas <- mapM cgIota iotas
    ces    <- mapM cgExp es
    return $ CExp [cexp|$cf($args:ciotas, $args:ces)|]

cgExp (DerefE e _) =
    cgExp e

cgExp (AssignE e1 e2 _) = do
    ce1 <- cgExp e1
    ce2 <- cgExp e2
    appendStm [cstm|$ce1 = $ce2;|]
    return CVoid

cgExp (ReturnE _ e _) = do
    ce <- cgExp e
    return $ CComp $ return ce
{-
cgExp (BindE bv e1 e2 _) =
    return $ CComp ccomp
  where
    ccomp :: CComp
    ccomp takek emitk donek = do
        ccomp1 <- cgExp e1 >>= unCComp
        ccomp1 takek emitk $ \ce -> do
            cv   <- cvar v
            ctau <- cgType tau
            appendDecl [cdecl|$ty:ctau $id:cv;|]
            appendStm [cstm|$id:cv = $ce;|]
            extendBindVars [bv] $ do
            extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
            ccomp2 <- cgExp e2 >>= unCComp
            ccomp2 takek emitk donek

cgExp (BindE WildV e1 e2 _) =
    return $ CComp ccomp
  where
    ccomp :: CComp
    ccomp takek emitk donek = do
        ccomp1 <- cgExp e1 >>= unCComp
        ccomp2 <- cgExp e2 >>= unCComp
        ccomp1 takek emitk $ \_ ->
            ccomp2 takek emitk donek
-}

cgExp (TakeE _ _) =
    return $ CComp $ liftF $ TakeC id

{-
cgExp (TakesE i _ _) =
    return $ CComp ccomp
  where
    ccomp :: CComp
    ccomp takek _ donek =
        takek (CInt (fromIntegral i)) donek
-}

cgExp (EmitE e _) = do
    ce <- cgExp e
    return $ CComp $ liftF $ EmitC ce CVoid

{-
cgExp (EmitsE e _) =
    return $ CComp ccomp
  where
    ccomp :: CComp
    ccomp _ emitk donek = do
        (clen, carr) <- cgExp e >>= unCArray
        cfor (CInt 0) clen $ \ci ->
            emitk (cidx carr ci)
        donek CVoid
-}

cgExp (RepeatE _ e _) = do
    comp <- cgExp e >>= unCComp
    return $ CComp $ Free $ RepeatC comp

{-
cgExp (ArrE _ _ e1 e2 _) = do
    return $ CComp ccomp
  where
    ccomp :: CComp
    ccomp takek emitk donek = do
        ccomp1 <- cgExp e1 >>= unCComp
        ccomp2 <- cgExp e2 >>= unCComp
        let takek2 _ k1 = do
            let emitk1 ce _ = k1 ce
            ccomp1 takek emitk1 donek
        ccomp2 takek2 emitk donek
-}

cgExp e =
    faildoc $ nest 2 $
    text "cgExp: cannot compile:" <+/> ppr e

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

gensym :: String -> Cg C.Id
gensym s = do
    Uniq u <- newUnique
    return $ C.Id (s ++ show u) noLoc

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

unCComp ce =
    panicdoc $
    text "unCComp: not a computation:" <+> ppr ce

cgType :: Type -> Cg C.Type
cgType (UnitT {}) =
    return [cty|void|]

cgType (BoolT {}) =
    return [cty|int|]

cgType (BitT {}) =
    return [cty|int|]

cgType (IntT W8 _) =
    return [cty|typename int8|]

cgType (IntT W16 _) =
    return [cty|typename int16|]

cgType (IntT W32 _) =
    return [cty|typename int32|]

cgType (IntT W64 _) =
    return [cty|typename int64|]

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
    return [cty|$ty:ctau[]|]

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
    panicdoc $ text "cgType: cannot compile type variable"

cgParam :: Type -> Cg C.Param
cgParam tau = do
    ctau <- cgType tau
    return [cparam|$ty:ctau|]

cgTemp :: String -> Type -> Maybe C.Initializer -> Cg CExp
cgTemp s tau maybe_cinit = do
    ctau <- cgType tau
    cv   <- gensym s
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

isPureish :: Type -> Bool
isPureish (ST [s,a,b] _ (TyVarT s' _) (TyVarT a' _) (TyVarT b' _) _) | sort [s,a,b] == sort [s',a',b'] =
    True

isPureish (ST {}) =
    False

isPureish _ =
    True

{-
cfor :: CExp -> CExp -> (CExp -> Cg a) -> Cg a
cfor cfrom cto k = do
    ci <- gensym "i"
    appendDecl [cdecl|int $id:ci;|]
    (cbody, x) <- inNewBlock $
                  k (CExp [cexp|$id:ci|])
    appendStm [cstm|for ($id:ci = $cfrom; $id:ci < $cto; ++$id:ci) { $items:cbody }|]
    return x

cidx :: CExp -> CExp -> CExp
cidx carr cidx = CExp [cexp|$carr[$cidx]|]
-}

cval :: Var -> CExp -> Type -> Cg CExp
cval _ ce@(CComp {}) _ =
    return ce

cval v ce tau = do
    cv   <- cvar v
    ctau <- cgType tau
    appendDecl [cdecl|$ty:ctau $id:cv;|]
    appendStm [cstm|$id:cv = $ce;|]
    return $ CExp [cexp|$id:cv|]

cgCComp :: Cg CExp
        -> (CExp -> Cg ())
        -> CComp
        -> Cg CExp
cgCComp take emit comp =
    cgFree comp
  where
    cgFree :: Free Comp CExp -> Cg CExp
    cgFree (Pure ce) = return ce
    cgFree (Free x)  = cgComp x

    cgComp :: Comp (Free Comp CExp) -> Cg CExp
    cgComp (BindC bv@(BindV v tau) k1 k2) = do
        ce   <- cgFree k1
        cv   <- cvar v
        ctau <- cgType tau
        appendDecl [cdecl|$ty:ctau $id:cv;|]
        appendStm [cstm|$id:cv = $ce;|]
        extendBindVars [bv] $ do
        extendVarCExps [(v, CExp [cexp|$id:cv|])] $ do
        cgFree k2

    cgComp (BindC WildV k1 k2) = do
        void $ cgFree k1
        cgFree k2

    cgComp (TakeC k) = do
        ce <- take
        cgFree (k ce)

    cgComp (EmitC ce k) = do
        emit ce
        cgFree k

    cgComp (IfC tau ce thenk elsek k) = do
        (cdone, donek) <- mkDoneK
        cthen          <- inNewBlock_ $ cgFree thenk >>= donek
        celse          <- inNewBlock_ $ cgFree elsek >>= donek
        appendStm [cstm|if ($ce) { $items:cthen } else { $items:celse }|]
        cgFree (k cdone)
      where
        mkDoneK :: Cg (CExp, CExp -> Cg ())
        mkDoneK | isSTUnitT tau =
            return (CVoid, \_ -> return ())
                | otherwise = do
            cdone <- cgTemp "done" tau Nothing
            let donek ce = appendStm [cstm|$cdone= $ce;|]
            return (cdone, donek)

    cgComp (RepeatC k) = do
        (citems, _) <- inNewBlock $ cgFree k
        appendStm [cstm|for (;;) { $items:citems }|]
        return CVoid
        -- cgFree (k >> Free (RepeatC k))

    cgComp (ArrC {}) =
        panicdoc $ text "cgComp: cannot compile ArrC"
