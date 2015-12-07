{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Transform.Auto
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Transform.Auto (
    Auto,
    runAuto,

    autoProgram
  ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Ref (MonadRef(..),
                          MonadAtomicRef(..))
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Text.PrettyPrint.Mainland

import KZC.Auto.Comp
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Core.Lint
import qualified KZC.Core.Syntax as C
import KZC.Error
import KZC.Flags
import KZC.Monad
import KZC.Name
import KZC.Summary
import KZC.Trace
import KZC.Uniq

data AutoEnv = AutoEnv
    { autoTcEnv :: TcEnv
    , autoSubst :: Map Var Var
    }

defaultAutoEnv :: TcEnv -> AutoEnv
defaultAutoEnv tcenv = AutoEnv tcenv mempty

newtype Auto a = Auto { unAuto :: ReaderT AutoEnv KZC a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadRef IORef, MonadAtomicRef IORef,
              MonadReader AutoEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace)

runAuto :: Auto a -> TcEnv -> KZC a
runAuto m tcenv = runReaderT (unAuto m) (defaultAutoEnv tcenv)

instance MonadTc Auto where
    askTc       = Auto $ asks autoTcEnv
    localTc f m = Auto $ local (\env -> env { autoTcEnv = f (autoTcEnv env) }) (unAuto m)

isInScope :: Var -> Auto Bool
isInScope v = asks (Map.member v . autoSubst)

lookupVarSubst :: Var -> Auto Var
lookupVarSubst v = maybe v id <$> asks (Map.lookup v . autoSubst)

ensureUnique :: Var -> (Var -> Auto a) -> Auto a
ensureUnique v k = do
     inscope <- isInScope v
     if inscope
       then do v' <- mkUniq v
               local (\env -> env { autoSubst = Map.insert v v' (autoSubst env) }) (k v')
       else k v

autoProgram :: [C.Decl] -> Auto LProgram
autoProgram cdecls = do
    transDecls cdecls $ \decls -> do
    (comp, tau) <- findMain decls
    return $ Program (filter (not . isMain) decls) comp tau
  where
    findMain :: [LDecl] -> Auto (LComp, Type)
    findMain decls =
        case filter isMain decls of
          [] -> faildoc $ text "Cannot find main computation."
          [LetCompD _ tau comp _] -> return (comp, tau)
          _ -> faildoc $ text "More than one main computation!"

    isMain :: LDecl -> Bool
    isMain (LetCompD v _ _ _) = v == "main"
    isMain _                  = False

transDecls :: [C.Decl] -> ([LDecl] -> Auto a) -> Auto a
transDecls [] k =
    k []

transDecls (cdecl:cdecls) k =
    transDecl  cdecl  $ \decl ->
    transDecls cdecls $ \decls ->
    k (decl:decls)

transDecl :: C.Decl -> (LDecl -> Auto a) -> Auto a
transDecl decl@(C.LetD v tau e l) k
  | isPureT tau =
    transLocalDecl decl $ \decl' ->
    k $ LetD decl' l

  | otherwise = ensureUnique v $ \v' -> do
    c <- withSummaryContext decl $
         withFvContext e $
         inSTScope tau $
         inLocalScope $
         transComp e
    extendVars [(v,tau)] $ do
    k $ LetCompD (mkBoundVar v') tau c l

transDecl decl@(C.LetRefD _ _ _ l) k =
    transLocalDecl decl $ \decl' ->
    k $ LetD decl' l

transDecl decl@(C.LetFunD f iotas vbs tau_ret e l) k
  | isPureishT tau_ret = ensureUnique f $ \f' -> do
    extendVars [(f, tau)] $ do
    e' <- withSummaryContext decl $
          withFvContext e $
          extendIVars (iotas `zip` repeat IotaK) $
          extendVars vbs $
          inSTScope tau_ret $
          inLocalScope $
          transExp e
    k $ LetFunD (mkBoundVar f') iotas vbs tau_ret e' l
  | otherwise = ensureUnique f $ \f' -> do
    extendVars [(f, tau)] $ do
    c <- withSummaryContext decl $
         withFvContext e $
         extendIVars (iotas `zip` repeat IotaK) $
         extendVars vbs $
         inSTScope tau_ret $
         inLocalScope $
         transComp e
    k $ LetFunCompD (mkBoundVar f') iotas vbs tau_ret c l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl (C.LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $
    k $ LetExtFunD (mkBoundVar f) iotas vbs tau_ret l
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

transDecl (C.LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    k $ LetStructD s flds l

transLocalDecl :: C.Decl -> (LocalDecl -> Auto a) -> Auto a
transLocalDecl decl@(C.LetD v tau e l) k | isPureT tau =
    ensureUnique v $ \v' -> do
    e' <- withSummaryContext decl $ transExp e
    extendVars [(v, tau)] $ do
    k $ LetLD (mkBoundVar v') tau e' l

transLocalDecl (C.LetRefD v tau Nothing l) k =
    ensureUnique v $ \v' ->
    extendVars [(v, refT tau)] $
    k $ LetRefLD (mkBoundVar v') tau Nothing l

transLocalDecl decl@(C.LetRefD v tau (Just e) l) k =
    ensureUnique v $ \v' -> do
    e' <- withSummaryContext decl $
          inLocalScope $
          transExp e
    extendVars [(v, refT tau)] $ do
    k $ LetRefLD (mkBoundVar v') tau (Just e') l

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

transExp :: C.Exp -> Auto Exp
transExp (C.ConstE c l) =
    return $ ConstE c l

transExp (C.VarE v l) = do
    v' <- lookupVarSubst v
    return $ VarE v' l

transExp (C.UnopE op e l) =
    UnopE op <$> transExp e <*> pure l

transExp (C.BinopE op e1 e2 l) =
    BinopE op <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.IfE e1 e2 e3 l) =
    IfE <$> transExp e1 <*> transExp e2 <*> transExp e3 <*> pure l

transExp (C.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    LetE decl <$> transExp e <*> pure l

transExp (C.CallE f iotas es l) = do
    f' <- lookupVarSubst f
    CallE f' iotas <$> mapM transExp es <*> pure l

transExp (C.DerefE e l) =
    DerefE <$> transExp e <*> pure l

transExp (C.AssignE e1 e2 l) =
    AssignE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.WhileE e1 e2 l) =
    WhileE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (C.ForE ann v tau e1 e2 e3 l) =
    ensureUnique v $ \v' -> do
    e1' <- withFvContext e1 $ transExp e1
    e2' <- withFvContext e2 $ transExp e2
    e3' <- withFvContext e3 $
           extendVars [(v, tau)] $
           transExp e3
    return $ ForE ann v' tau e1' e2' e3' l

transExp (C.ArrayE es l) =
    ArrayE <$> mapM transExp es <*> pure l

transExp (C.IdxE e1 e2 i l) =
    IdxE <$> transExp e1 <*> transExp e2 <*> pure i <*> pure l

transExp (C.StructE s flds l) =
    StructE s <$> mapM transField flds <*> pure l
  where
    transField :: (Field, C.Exp) -> Auto (Field, Exp)
    transField (f, e) = (,) <$> pure f <*> transExp e

transExp (C.ProjE e f l) =
    ProjE <$> transExp e <*> pure f <*> pure l

transExp (C.PrintE nl es l) =
    PrintE nl <$> mapM transExp es <*> pure l

transExp (C.ErrorE tau s l) =
    return $ ErrorE tau s l

transExp (C.ReturnE ann e l) =
    ReturnE ann <$> transExp e <*> pure l

transExp (C.BindE C.WildV tau e1 e2 l) = do
    e1' <- transExp e1
    e2' <- transExp e2
    return $ BindE WildV tau e1' e2' l

transExp (C.BindE (C.TameV v) tau e1 e2 l) =
    ensureUnique v $ \v' -> do
    e1' <- transExp e1
    e2' <- extendVars [(v, tau)] $
           transExp e2
    return $ BindE (TameV (mkBoundVar v')) tau e1' e2' l

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

transComp :: C.Exp -> Auto LComp
transComp e@(C.VarE v l) = do
    v'  <- lookupVarSubst v
    tau <- lookupVar v
    if isPureishT tau
      then do e' <- transExp e
              liftC e' l
      else varC v' l

transComp (C.IfE e1 e2 e3 l) = do
    e1' <- transExp e1
    e2' <- transComp e2
    e3' <- transComp e3
    ifC e1' e2' e3' l

transComp (C.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    letC decl l.>>. transComp e

transComp e@(C.CallE f iotas es l) = do
    f'              <- lookupVarSubst f
    (_, _, tau_res) <- lookupVar f >>= checkFunT
    if isPureishT tau_res
      then do e' <- transExp e
              liftC e' l
      else do args <- mapM transArg es
              callC f' iotas args l
  where
    transArg :: C.Exp -> Auto LArg
    transArg e = do
        tau <- inferExp e
        if isPureT tau
          then ExpA  <$> transExp e
          else CompA <$> transComp e

transComp (C.WhileE e c l) = do
    e' <- transExp e
    c' <- transComp c
    whileC e' c' l

transComp (C.ForE ann v tau e1 e2 e3 l) =
    ensureUnique v $ \v' -> do
    e1' <- withFvContext e1 $ transExp e1
    e2' <- withFvContext e2 $ transExp e2
    c'  <- withFvContext e3 $
           extendVars [(v, tau)] $
           transComp e3
    forC ann v' tau e1' e2' c' l

transComp (C.ReturnE _ e l) = do
    e <- transExp e
    returnC e l

transComp (C.BindE C.WildV tau e1 e2 l) =
    transComp e1 .>>. bindC WildV tau l .>>. transComp e2

transComp (C.BindE (C.TameV v) tau e1 e2 l) =
    ensureUnique v $ \v' -> do
    transComp e1
        .>>. bindC (TameV (mkBoundVar v')) tau l
        .>>. (extendVars [(v, tau)] $ transComp e2)

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

transComp (C.RepeatE ann e l) = do
    c <- transComp e
    repeatC ann c l

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
