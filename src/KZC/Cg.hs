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
import Control.Monad.Free (Free(..),
                           liftF)
import Data.Char (ord)
import Data.Foldable (toList)
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

cUR_KONT :: C.Id
cUR_KONT = C.Id "curk" noLoc

compileProgram :: [Decl] -> Cg ()
compileProgram decls = do
    appendTopDef [cedecl|$esc:("#include <kzc.h>")|]
    cgDecls decls $ do
    comp <- cgExp (varE "main") >>= unCComp
    let take :: TakeK
        take _ k1 k2 = do
        appendStm [cstm|++i;|]
        let ccomp = k1 $ CExp [cexp|in[i]|]
        k2 ccomp
    let emit :: EmitK
        emit _ ce ccomp k = do
            appendStm [cstm|out[j++] = $ce;|]
            k ccomp
    let done _  =  return ()
    citems <- inNewBlock_ $ do
              appendDecl [cdecl|typename KONT $id:cUR_KONT = LABELADDR($id:(ccompLabel comp));|]
              cgThread $ cgCComp take emit done comp
    cgLabels
    appendTopDef [cedecl|
int main(int argc, char **argv)
{
    int in[1];
    int i = 0;
    int out[1];
    int j = 0;

    $items:citems
}|]

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
cgDecl (LetD v tau e _) k =
    inSTScope tau $ do
    ce <- if isComp tau then return (CDelay (cgExp e)) else cgExp e
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
        comp2     <- unCComp ce2
        comp3     <- unCComp ce3
        cv        <- cgTemp "cond" tau Nothing
        ifl       <- genLabel "ifk"
        donel     <- genLabel "donek"
        bindk     <- cgBind cv
        let donek =  liftF $ DoneC donel
        return $ CComp $ Free $
            IfC ifl cv ce1
                (comp2 >>= bindk >> donek)
                (comp3 >>= bindk >> donek)
                return

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

cgExp (BindE bv@(BindV v tau) e1 e2 _) = do
    comp1   <- collectComp (cgExp e1 >>= unCComp)
    cv      <- cvar v
    let cve =  CExp [cexp|$id:cv|]
    bindc   <- collectCompBind $ mkBind cv
    comp2   <- extendBindVars [bv] $
               extendVarCExps [(v, cve)] $
               collectComp (cgExp e2 >>= unCComp)
    return $ CComp $ comp1 >>= bindc >> comp2
  where
    mkBind :: C.Id -> Cg (CExp -> CComp)
    mkBind cv = do
        let cve =  CExp [cexp|$id:cv|]
        ctau    <- cgType tau
        appendDecl [cdecl|$ty:ctau $id:cv;|]
        cgBind cve

cgExp (BindE WildV e1 e2 _) = do
    comp1 <- collectComp (cgExp e1 >>= unCComp)
    comp2 <- collectComp (cgExp e2 >>= unCComp)
    return $ CComp $ comp1 >> comp2

cgExp (TakeE _ _) = do
    l <- genLabel "takek"
    return $ CComp $ liftF $ TakeC l id

cgExp (TakesE i _ _) = do
    l <- genLabel "takesk"
    return $ CComp $ liftF $ TakesC l i id

cgExp (EmitE e _) = liftM CComp $ collectComp $ do
    l  <- genLabel "emitk"
    ce <- cgExp e
    return $ liftF $ EmitC l ce CVoid

cgExp (EmitsE e _) = liftM CComp $ collectComp $ do
    l         <- genLabel "emitsk"
    (iota, _) <- inferExp e >>= splitArrT
    ce        <- cgExp e
    return $ liftF $ EmitsC l iota ce CVoid

cgExp (RepeatE _ e _) = do
    l      <- genLabel "repeatk"
    ccomp  <- cgExp e >>= unCComp
    return $ CComp $ liftF (LabelC l CVoid) >> ccomp >> Free (GotoC l)

cgExp (ParE _ tau e1 e2 _) = do
    comp1 <- cgExp e1 >>= unCComp
    comp2 <- cgExp e2 >>= unCComp
    return $ CComp $ Free $ ParC tau comp1 comp2

cgExp e =
    faildoc $ nest 2 $
    text "cgExp: cannot compile:" <+/> ppr e

collectComp :: Cg CComp -> Cg CComp
collectComp m = do
    l            <- genLabel "codek"
    (comp, code) <- collect m
    return $ liftF (CodeC l code ()) >> comp

collectCompBind :: Cg (CExp -> CComp) -> Cg (CExp -> CComp)
collectCompBind m = do
    l             <- genLabel "codek"
    (compf, code) <- collect m
    return $ \ce -> liftF (CodeC l code ()) >> compf ce

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
    cgCTemp s ctau maybe_cinit

cgCTemp :: String -> C.Type -> Maybe C.Initializer -> Cg CExp
cgCTemp s ctau maybe_cinit = do
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

cval _ ce@(CDelay {}) _ =
    return ce

cval v ce tau = do
    cv   <- cvar v
    ctau <- cgType tau
    appendDecl [cdecl|$ty:ctau $id:cv;|]
    appendStm [cstm|$id:cv = $ce;|]
    return $ CExp [cexp|$id:cv|]

-- | Generate code for the specified 'CComp' using the given code-generating
-- continuation and label the resulting code with the label belonging to the
-- 'CComp'.
cgCCompWithLabel :: CComp -> (CComp -> Cg a) -> Cg a
cgCCompWithLabel ccomp@(Free (GotoC _)) k =
    k ccomp

cgCCompWithLabel ccomp k =
    cgWithLabel (ccompLabel ccomp) (k ccomp)

-- | Label the statements generated by the continuation @k@ with the specified
-- label.
cgWithLabel :: Label -> Cg a -> Cg a
cgWithLabel (C.Id ident l) k = do
    (stms, x) <- collectStms k
    case stms of
      []     -> panicdoc $ text "cgWithLabel: no statements!"
      [s]    -> appendStm [cstm|$id:lbl: $stm:s|]
      (s:ss) -> appendStms [cstms|$id:lbl: $stm:s $stms:ss|]
    return x
  where
    lbl :: Label
    lbl = C.Id ("LABEL(" ++ ident ++ ")") l

cgWithLabel (C.AntiId {}) _ =
    panicdoc $ text "cgWithLabel saw C.AntiId!"

type TakeK = Int -> (CExp -> CComp) -> (CComp -> Cg ()) -> Cg ()
type EmitK = Iota -> CExp -> CComp -> (CComp -> Cg ()) -> Cg ()
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
    cgComp (CodeC _ c k) = do
        tell c
        cgFree k

    cgComp (TakeC _ k) = do
        take 1 k cgFree

    cgComp (TakesC _ i k) = do
        take i k cgFree

    cgComp (EmitC _ ce k) = do
        emit (ConstI 1 noLoc) ce k cgFree

    cgComp (EmitsC _ iota ce k) = do
        emit iota ce k cgFree

    cgComp (IfC _ cv ce thenk elsek k) = do
        (cthen, _) <- inNewBlock $ cgFree thenk
        (celse, _) <- inNewBlock $ cgFree elsek
        appendStm [cstm|if ($ce) { $items:cthen } else { $items:celse }|]
        cgFree (k cv)

    cgComp (ParC tau left right) = do
        ctau    <- cgType tau
        cleftk  <- cgCTemp "leftk"  [cty|typename KONT|] (Just [cinit|LABELADDR($id:(ccompLabel left))|])
        crightk <- cgCTemp "rightk" [cty|typename KONT|] (Just [cinit|LABELADDR($id:(ccompLabel right))|])
        cbuf    <- cgCTemp "bufp"   [cty|$ty:ctau *|] (Just [cinit|NULL|])
        let take' :: TakeK
            take' _ k1 k2 = do
                let ccomp = k1 $ CExp [cexp|*$cbuf|]
                let lbl   = ccompLabel ccomp
                appendStm [cstm|$crightk = LABELADDR($id:lbl);|]
                appendStm [cstm|CALLKONT($cleftk);|]
                cgCCompWithLabel ccomp k2
        let emit' :: EmitK
            emit' _ ce ccomp k = do
                let lbl = ccompLabel ccomp
                appendStm [cstm|$cbuf = &$ce;|]
                appendStm [cstm|$cleftk = LABELADDR($id:lbl);|]
                appendStm [cstm|CALLKONT($crightk);|]
                cgCCompWithLabel ccomp k
        cgCComp take' emit  done right
        cgCComp take  emit' done left

    cgComp (BindC _ cv ce k) = do
        appendStm [cstm|$cv = $ce;|]
        cgFree k

    cgComp (DoneC {}) =
        done CVoid

    cgComp (LabelC l k) =
        cgWithLabel l (cgFree k)

    cgComp (GotoC l) =
        appendStm [cstm|GOTO($id:l);|]

cgBind :: CExp -> Cg (CExp -> CComp)
cgBind cv = do
    lbl <- genLabel "bindk"
    return $ \ce -> liftF $ BindC lbl cv ce CVoid
