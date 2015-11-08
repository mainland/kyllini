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

    transformProgram
  ) where

import Control.Applicative ((<$>), (<*>), pure)
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Smart
import KZC.Auto.Syntax
import qualified KZC.Core.Syntax as C
import KZC.Label
import KZC.Lint
import KZC.Lint.Monad
import KZC.Monad
import KZC.Name
import KZC.Summary
import KZC.Staged

-- | The 'T' monad.
type T a = Tc a

runT :: T a -> KZC a
runT m = withTc m

transformProgram :: [C.Decl] -> T LProgram
transformProgram cdecls = do
    transDecls cdecls $ \decls -> do
    (comp, tau) <- findMain decls
    return $ Program (filter (not . isMain) decls) comp tau
  where
    findMain :: [LDecl] -> T (LComp, Type)
    findMain decls =
        case filter isMain decls of
          [] -> faildoc $ text "Cannot find main computation."
          [LetCompD _ tau comp _] -> return (comp, tau)
          _ -> faildoc $ text "More than one main computation!"

    isMain :: LDecl -> Bool
    isMain (LetCompD v _ _ _) = v == "main"
    isMain _                  = False

transDecls :: [C.Decl] -> ([LDecl] -> T a) -> T a
transDecls [] k =
    k []

transDecls (cdecl:cdecls) k =
    transDecl  cdecl  $ \decl ->
    transDecls cdecls $ \decls ->
    k (decl:decls)

transDecl :: C.Decl -> (LDecl -> T a) -> T a
transDecl decl@(C.LetD v tau e l) k
  | isPureishT tau = do
    e' <- withSummaryContext decl $
          withFvContext e $
          inSTScope tau $
          inLocalScope $
          transExp e
    extendVars [(v,tau)] $ do
    k $ LetD v tau e' l

  | otherwise = do
    c <- withSummaryContext decl $
         withFvContext e $
         inSTScope tau $
         inLocalScope $
         transComp e
    extendVars [(v,tau)] $ do
    k $ LetCompD v tau c l

transDecl decl@(C.LetFunD f iotas vbs tau_ret e l) k
  | isPureishT tau_ret = do
    extendVars [(f, tau)] $ do
    e' <- withSummaryContext decl $
          withFvContext e $
          extendIVars (iotas `zip` repeat IotaK) $
          extendVars vbs $
          inSTScope tau_ret $
          inLocalScope $
          transExp e
    k $ LetFunD f iotas vbs tau_ret e' l
  | otherwise = do
    extendVars [(f, tau)] $ do
    c <- withSummaryContext decl $
         withFvContext e $
         extendIVars (iotas `zip` repeat IotaK) $
         extendVars vbs $
         inSTScope tau_ret $
         inLocalScope $
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
    extendVars [(v, tau)] $ do
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
    faildoc $ text "Local declarations must be a let or letref, but this is a" <+> pprDeclType decl
  where
    pprDeclType :: C.Decl -> Doc
    pprDeclType (C.LetD _ tau _ _)
        | isPureishT tau          = text "let"
        | otherwise               = text "letcomp"
    pprDeclType (C.LetFunD {})    = text "letfun"
    pprDeclType (C.LetExtFunD {}) = text "letextfun"
    pprDeclType (C.LetRefD {})    = text "letref"
    pprDeclType (C.LetStructD {}) = text "letstruct"

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

transExp (C.ForE ann v tau e1 e2 e3 l) = do
    e1' <- withFvContext e1 $ transExp e1
    e2' <- withFvContext e2 $ transExp e2
    e3' <- withFvContext e3 $
           extendVars [(v, tau)] $
           transExp e3
    return $ ForE ann v tau e1' e2' e3' l

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

transExp (C.BindE bv e1 e2 l) = do
    e1' <- transExp e1
    e2' <- extendBindVars [bv] $
           transExp e2
    return $ BindE bv e1' e2' l

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

infixl 1 .>>.
(.>>.) :: T LComp -> T LComp -> T LComp
m1 .>>. m2 = do
    m1' <- m1
    m2' <- m2
    return $ m1' <> m2'

transComp :: C.Exp -> T LComp
transComp e@(C.VarE v l) = do
    tau <- lookupVar v
    if isPureishT tau
      then do e' <- transExp e
              liftC e' l
      else varC v l

transComp (C.IfE e1 e2 e3 l) = do
    e1' <- transExp e1
    e2' <- transComp e2
    e3' <- transComp e3
    ifC e1' e2' e3' l

transComp (C.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    letC decl l.>>. transComp e

transComp e@(C.CallE f iotas es l) = do
    (_, _, tau_res) <- lookupVar f >>= checkFunT
    if isPureishT tau_res
      then do e' <- transExp e
              liftC e' l
      else do es' <- mapM transExp es
              callC f iotas es' l

transComp (C.WhileE e1 e2 l) = do
    test    <- transExp e1
    l_head <- genLabel "while_head"
    body    <- transComp e2 .>>. gotoC l_head l
    done    <- returnC unitE l
    return $ ifC' l_head test body done l

transComp e0@(C.ForE _ v v_tau e_start e_len e_body l) =
    withFvContext e0 $ do
    i <- mkUniqVar (namedString v) l
    transLocalDecl (C.LetRefD i v_tau (Just e_start) l) $ \decl -> do
    e_start'   <- transExp e_start
    e_len'     <- transExp e_len
    let e_test =  varE v .<. e_start' + e_len'
    head       <- transComp (C.DerefE (C.VarE i l) l) .>>.
                  bindC (BindV v v_tau) l
    l_head     <- compLabel head
    body       <- extendVars [(v, v_tau)] $
                  transComp e_body .>>.
                  liftC (i .:=. varE v + castE v_tau 1) l .>>.
                  gotoC l_head l
    done       <- returnC unitE l
    letC decl l .>>. return head .>>. ifC e_test body done l

transComp (C.ReturnE _ e l) = do
    e <- transExp e
    returnC e l

transComp (C.BindE bv e1 e2 l) =
    transComp e1 .>>. bindC bv l .>>. (extendBindVars [bv] $ transComp e2)

transComp (C.TakeE tau l) =
    takeC tau l

transComp (C.TakesE i tau l) =
    takesC i tau l

transComp (C.EmitE e l) = do
    e' <- transExp e
    emitC e' l

transComp (C.EmitsE e l) = do
    e' <- transExp e
    emitsC e' l

transComp (C.RepeatE _ e l) = do
    c        <- transComp e
    l_repeat <- compLabel c
    return c .>>. repeatC l_repeat l

transComp (C.ParE ann b e1 e2 l) = do
    (s, a, c) <- askSTIndTypes
    c1        <- withFvContext e1 $
                 localSTIndTypes (Just (s, a, b)) $
                 transComp e1
    c2        <- withFvContext e2 $
                 localSTIndTypes (Just (b, b, c)) $
                 transComp e2
    parC ann b c1 c2 l

transComp e = do
    tau <- inferExp e
    e'  <- transExp e
    if isCompT tau
      then liftC e' e
      else returnC e' e
