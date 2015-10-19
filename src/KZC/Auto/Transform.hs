{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Auto.Transform
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Auto.Transform (
    T,
    runT,

    transformProgram,

    (.>>.),
    (.>>=.),
    varC,
    callC,
    ifC,
    ifC',
    letC,
    letC',
    returnC,
    bindC,
    labelC,
    gotoC,
    takeC,
    takesC,
    emitC,
    parC,
    endC,
    doneC,
    compLabel,
    genLabel
  ) where

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.Free
import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland

import KZC.Auto.Smart
import KZC.Auto.Syntax
import qualified KZC.Core.Syntax as C
import KZC.Lint
import KZC.Lint.Monad
import KZC.Monad
import KZC.Summary
import KZC.Staged
import KZC.Uniq

-- | The 'T' monad.
type T a = Tc () () a

runT :: T a -> KZC a
runT m = withTc () () m

infixl 1 .>>., .>>=.

(.>>.) :: T (LComp c) -> T (LComp c) -> T (LComp c)
m1 .>>. m2 = do
    m1' <- m1
    m2' <- m2
    return $ m1' >> m2'

(.>>=.) :: T (LComp c) -> T (c -> LComp c) -> T (LComp c)
m .>>=. k = do
    m' <- m
    k' <- k
    return $ m' >>= k'

varC :: Located a => Var -> a -> Tc r s (LComp c)
varC v a = do
    l <- genLabel "vark"
    return $ liftF $ VarC l v id (srclocOf a)

callC :: Located a => Var -> [Iota] -> [Exp] -> a -> Tc r s (LComp c)
callC f is es a = do
    l <- genLabel "callk"
    return $ liftF $ CallC l f is es id (srclocOf a)

ifC :: Located a => Exp -> LComp c -> LComp c -> a -> Tc r s (LComp c)
ifC ce thenc elsec a = do
    l      <- genLabel "ifk"
    end_th <- endC a
    end_el <- endC a
    return $ wrap $ IfC l ce (thenc >>= end_th) (elsec >>= end_el) return (srclocOf a)

ifC' :: Located a => Label -> Exp -> LComp c -> LComp c -> a -> LComp c
ifC' l ce thenc elsec a =
    wrap $ IfC l ce thenc elsec return (srclocOf a)

letC :: Located a => LocalDecl -> a -> Tc r s (LComp c)
letC decl a = do
    l <- genLabel "letk"
    return $ liftF $ LetC l decl undefined (srclocOf a)

letC' :: Located a => Label -> LocalDecl -> a -> LComp c
letC' l decl a = liftF $ LetC l decl undefined (srclocOf a)

returnC :: Located a => Exp -> a -> Tc r s (LComp c)
returnC e a = do
    l <- genLabel "returnk"
    return $ liftF $ ReturnC l e id (srclocOf a)

bindC :: Located a => BindVar -> a -> Tc r s (c -> LComp c)
bindC bv a = do
    l <- genLabel "bindk"
    return $ \c -> liftF $ BindC l bv c undefined (srclocOf a)

labelC :: Located a => a -> Label -> LComp c
labelC a l = liftF $ LabelC l undefined (srclocOf a)

gotoC :: Located a => Label -> a -> Tc r s (LComp c)
gotoC l a =
    return $ wrap $ GotoC l (srclocOf a)

takeC :: Located a => Type -> a -> Tc r s (LComp c)
takeC tau a = do
    l <- genLabel "takek"
    return $ liftF $ TakeC l tau id (srclocOf a)

takesC :: Located a => Int -> Type -> a -> Tc r s (LComp c)
takesC i tau a = do
    l <- genLabel "takesk"
    return $ liftF $ TakesC l i tau id (srclocOf a)

emitC :: Located a => Exp -> a -> Tc r s (LComp c)
emitC e a = do
    l <- genLabel "emitk"
    return $ liftF $ EmitC l e undefined (srclocOf a)

parC :: Located a => PipelineAnn -> Type -> LComp c -> LComp c -> a -> Tc r s (LComp c)
parC ann tau c1 c2 a = do
    end_left  <- doneC a
    end_right <- doneC a
    return $ wrap $ ParC ann tau (c1 >>= end_left) (c2 >>= end_right) return (srclocOf a)

endC :: Located a => a -> Tc r s (c -> LComp c)
endC a = do
  l <- genLabel "endk"
  return $ \c -> liftF $ EndC l c (srclocOf a)

doneC :: Located a => a -> Tc r s (c -> LComp c)
doneC a = do
  l <- genLabel "donek"
  return $ \c -> liftF $ DoneC l c (srclocOf a)

compLabel :: forall c r s . LComp c -> Tc r s Label
compLabel (Pure {})   = fail "compLabel: saw Pure"
compLabel (Free comp) = comp0Label comp
  where
    comp0Label :: Comp0 Label c (Comp Label c) -> Tc r s Label
    comp0Label (VarC l _ _ _)         = return l
    comp0Label (CallC l _ _ _ _ _)    = return l
    comp0Label (IfC l _ _ _ _ _)      = return l
    comp0Label (LetC l _ _ _)         = return l
    comp0Label (ReturnC l _ _ _)      = return l
    comp0Label (BindC l _ _ _ _)      = return l
    comp0Label (LabelC l (Pure {}) _) = return l
    comp0Label (LabelC _ k _)         = compLabel k
    comp0Label (GotoC l _)            = return l
    comp0Label (TakeC l _ _ _)        = return l
    comp0Label (TakesC l _ _ _ _)     = return l
    comp0Label (EmitC l _ _ _)        = return l
    comp0Label (ParC _ _ _ right _ _) = compLabel right
    comp0Label (EndC l _ _)           = return l
    comp0Label (DoneC l _ _)          = return l

genLabel :: String -> Tc r s Label
genLabel s = do
    Uniq u <- newUnique
    return $ Label (intern (s ++ "__" ++ show u))

transformProgram :: [C.Decl] -> T (LProgram c)
transformProgram cdecls =
    transDecls cdecls $ \decls -> do
    (comp, tau) <- findMain decls
    return $ Program (filter (not . isMain) decls) comp tau
  where
    findMain :: [LDecl c] -> T (LComp c, Type)
    findMain decls =
        case filter isMain decls of
          [] -> faildoc $ text "Cannot find main computation."
          [LetCompD _ tau comp _] -> return (comp, tau)
          _ -> faildoc $ text "More than one main computation!"

    isMain :: LDecl c -> Bool
    isMain (LetCompD v _ _ _) = v == "main"
    isMain _                  = False

transDecls :: forall a c . [C.Decl] -> ([LDecl c] -> T a) -> T a
transDecls [] k =
    k []

transDecls (cdecl:cdecls) k =
    transDecl  cdecl  $ \decl ->
    transDecls cdecls $ \decls ->
    k (decl:decls)

transDecl :: C.Decl -> (LDecl c -> T a) -> T a
transDecl decl@(C.LetD v tau e l) k
  | isPureishT tau = do
    e' <- withSummaryContext decl $ transExp e
    extendVars [(v,tau)] $ do
    k $ LetD v tau e' l

  | otherwise = do
    c <- withSummaryContext decl $ transComp e
    extendVars [(v,tau)] $ do
    k $ LetCompD v tau c l

transDecl decl@(C.LetFunD f iotas vbs tau_ret e l) k
  | isPureishT tau_ret = do
    extendVars [(f, tau)] $ do
    e' <- withSummaryContext decl $
          withFvContext e $
          extendIVars (iotas `zip` repeat IotaK) $
          extendVars vbs $
          transExp e
    k $ LetFunD f iotas vbs tau_ret e' l
  | otherwise = do
    extendVars [(f, tau)] $ do
    c <- withSummaryContext decl $
         withFvContext e $
         extendIVars (iotas `zip` repeat IotaK) $
         extendVars vbs $
         transComp e
    k $ LetFunCompD f iotas vbs tau_ret c l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl (C.LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $
    k $ LetExtFunD f iotas vbs tau_ret l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl (C.LetRefD v tau Nothing l) k =
    extendVars [(v, refT tau)] $
    k $ LetRefD v tau Nothing l

transDecl decl@(C.LetRefD v tau (Just e) l) k = do
    e' <- withSummaryContext decl $
          inLocalScope $
          transExp e
    extendVars [(v, refT tau)] $ do
    k $ LetRefD v tau (Just e') l

transDecl (C.LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k $ LetStructD s flds l

transLocalDecl :: C.Decl -> (LocalDecl -> T a) -> T a
transLocalDecl decl@(C.LetD v tau e l) k | isPureishT tau = do
    e' <- withSummaryContext decl $ transExp e
    extendVars [(v,tau)] $ do
    k $ LetLD v tau e' l

transLocalDecl (C.LetRefD v tau Nothing l) k =
    extendVars [(v, refT tau)] $
    k $ LetRefLD v tau Nothing l

transLocalDecl decl@(C.LetRefD v tau (Just e) l) k = do
    e' <- withSummaryContext decl $
          inLocalScope $
          transExp e
    extendVars [(v, refT tau)] $ do
    k $ LetRefLD v tau (Just e') l

transLocalDecl decl _ =
    withSummaryContext decl $
    faildoc $ text "Local declarations must be let's or letref's."

transExp :: C.Exp -> T Exp
transExp (C.ConstE c l) =
    return $ ConstE c l

transExp (C.VarE v l) =
    return $ VarE v l

transExp (C.UnopE op e l) =
    UnopE op <$> transExp e <*> pure l

transExp (C.BinopE op e1 e2 l) =
    BinopE op <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.IfE e1 e2 e3 l) =
    IfE <$> transExp e1 <*> transExp e2 <*> transExp e3 <*> pure l

transExp (C.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    LetE decl <$> transExp e <*> pure l

transExp (C.CallE f iotas es l) =
    CallE f iotas <$> mapM transExp es <*> pure l

transExp (C.DerefE e l) =
    DerefE <$> transExp e <*> pure l

transExp (C.AssignE e1 e2 l) =
    AssignE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.WhileE e1 e2 l) =
    WhileE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.ForE ann v tau e1 e2 e3 l) =
    ForE ann v tau <$> transExp e1 <*> transExp e2 <*> transExp e3 <*> pure l

transExp (C.ArrayE es l) =
    ArrayE <$> mapM transExp es <*> pure l

transExp (C.IdxE e1 e2 i l) =
    IdxE <$> transExp e1 <*> transExp e2 <*> pure i <*> pure l

transExp (C.StructE s flds l) =
    StructE s <$> mapM transField flds <*> pure l
  where
    transField :: (Field, C.Exp) -> T (Field, Exp)
    transField (f, e) = (,) <$> pure f <*> transExp e

transExp (C.ProjE e f l) =
    ProjE <$> transExp e <*> pure f <*> pure l

transExp (C.PrintE nl es l) =
    PrintE nl <$> mapM transExp es <*> pure l

transExp (C.ErrorE tau s l) =
    return $ ErrorE tau s l

transExp (C.ReturnE ann e l) =
    ReturnE ann <$> transExp e <*> pure l

transExp (C.BindE bv e1 e2 l) =
    BindE bv <$> transExp e1 <*> transExp e2 <*> pure l

transExp e@(C.TakeE {}) =
    withSummaryContext e $
    faildoc $ text "take expression seen in pure-ish computation"

transExp e@(C.TakesE {}) =
    withSummaryContext e $
    faildoc $ text "takes expression seen in pure-ish computation"

transExp e@(C.EmitE {}) =
    withSummaryContext e $
    faildoc $ text "emit expression seen in pure-ish computation"

transExp e@(C.EmitsE {}) =
    withSummaryContext e $
    faildoc $ text "emits expression seen in pure-ish computation"

transExp e@(C.RepeatE {}) =
    withSummaryContext e $
    faildoc $ text "repeat expression seen in pure-ish computation"

transExp e@(C.ParE {}) =
    withSummaryContext e $
    faildoc $ text "par expression seen in pure-ish computation"

transComp :: C.Exp -> T (LComp c)
transComp (C.VarE v l) =
    varC v l

transComp (C.IfE e1 e2 e3 l) = do
    e1' <- transExp e1
    e2' <- transComp e2
    e3' <- transComp e3
    ifC e1' e2' e3' l

transComp (C.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    letC decl l .>>. transComp e

transComp (C.CallE f iotas es l) = do
    es' <- mapM transExp es
    callC f iotas es' l

transComp (C.WhileE e1 e2 l) = do
    test    <- transExp e1
    l_start <- genLabel "whilek"
    body    <- transComp e2 .>>. gotoC l_start l
    done    <- returnC unitE l .>>=. endC l
    return $ ifC' l_start test body done l

transComp (C.ForE _ v v_tau e_start e_len e_body l) =
    transLocalDecl (C.LetRefD v v_tau (Just e_start) l) $ \decl -> do
    l_start    <- genLabel "for_start"
    l_test     <- genLabel "for_test"
    e_start'   <- transExp e_start
    e_len'     <- transExp e_len
    let e_test =  varE v .<. e_start' + e_len'
    body       <- transComp e_body .>>.
                  returnC (v .:=. varE v + 1) l .>>.
                  gotoC l_test l
    done       <-  returnC unitE l .>>=. endC l
    return $ letC' l_start decl l >> ifC' l_test e_test body done l

transComp (C.ReturnE _ e l) = do
    e <- transExp e
    returnC e l .>>=. return return

transComp (C.BindE bv e1 e2 l) =
    transComp e1 .>>=. bindC bv l .>>. transComp e2

transComp (C.TakeE tau l) =
    takeC tau l

transComp (C.TakesE i tau l) =
    takesC i tau l

transComp (C.EmitE e l) = do
    e' <- transExp e
    emitC e' l

transComp (C.EmitsE e l) = do
    e' <- transExp e
    emitC e' l

transComp (C.RepeatE _ e l) = do
    c        <- transComp e
    l_repeat <- compLabel c
    return c .>>. gotoC l_repeat l

transComp (C.ParE ann b e1 e2 l) = do
    c1 <- transComp e1
    c2 <- transComp e2
    parC ann b c1 c2 l

transComp e = do
    e' <- transExp e
    returnC e' e
