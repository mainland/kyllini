{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Expr.ToCore
-- Copyright   :  (c) 2014-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Expr.ToCore (
    runTC,

    exprToCore
  ) where

import Control.Monad.Exception (MonadException(..))
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Comp
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Expr.Lint
import qualified KZC.Expr.Syntax as E
import KZC.Fuel
import KZC.Label
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq

data TCEnv = TCEnv { tcSubst :: Map Var Var }

defaultTCEnv :: TCEnv
defaultTCEnv = TCEnv mempty

newtype TC m a = TC { unTC :: ReaderT TCEnv m a }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadFail
             , MonadIO
             , MonadReader TCEnv
             , MonadException
             , MonadUnique
             , MonadErr
             , MonadConfig
             , MonadFuel
             , MonadPlatform
             , MonadTrace
             , MonadTc)

instance MonadTrans TC where
    lift m = TC $ lift m

runTC :: TC m a -> m a
runTC m = runReaderT (unTC m) defaultTCEnv

isInScope :: MonadTc m => Var -> TC m Bool
isInScope v = asks (Map.member v . tcSubst)

lookupVarSubst :: MonadTc m => Var -> TC m Var
lookupVarSubst v = fromMaybe v <$> asks (Map.lookup v . tcSubst)

ensureUnique :: MonadTc m => Var -> (Var -> TC m a) -> TC m a
ensureUnique v k = do
     inscope <- isInScope v
     if inscope
       then do v' <- uniquify v
               local (\env -> env { tcSubst = Map.insert v v' (tcSubst env) }) (k v')
       else k v

exprToCore :: forall l m . (IsLabel l, MonadTc m)
           => E.Program
           -> TC m (Program l)
exprToCore (E.Program eimports edecls) =
    transDecls edecls $ \decls -> do
    let topdecls = filter (not . isMain) decls
    let imports  = [Import mod | E.Import mod <- eimports]
    Program imports topdecls <$> findMain decls
  where
    findMain :: [Decl l] -> TC m (Maybe (Main l))
    findMain decls =
        case filter isMain decls of
          [] -> return Nothing
          [LetCompD _ tau comp _] -> return $ Just $ Main comp tau
          _ -> faildoc $ text "More than one main computation!"

    isMain :: Decl l -> Bool
    isMain (LetCompD v _ _ _) = v == "main"
    isMain _                  = False

transDecls :: (IsLabel l, MonadTc m)
           => [E.Decl]
           -> ([Decl l] -> TC m a)
           -> TC m a
transDecls [] k =
    k []

transDecls (cdecl:cdecls) k =
    transDecl  cdecl  $ \decl ->
    transDecls cdecls $ \decls ->
    k (decl:decls)

transDecl :: (IsLabel l, MonadTc m)
          => E.Decl
          -> (Decl l -> TC m a)
          -> TC m a
transDecl (E.StructD struct l) k =
    extendStructs [struct] $
    k $ StructD struct l

transDecl decl@(E.LetD v tau e l) k
  | isPureT tau =
    transLocalDecl decl $ \decl' ->
    k $ LetD decl' l

  | otherwise = ensureUnique v $ \v' -> do
    c <- extendLet v tau $
         withSummaryContext decl $
         withFvContext e $
         transComp e
    extendVars [(v,tau)] $
      k $ LetCompD (mkBoundVar v') tau c l

transDecl decl@(E.LetTypeD _ _ _ l) k =
    transLocalDecl decl $ \decl' ->
    k $ LetD decl' l

transDecl decl@(E.LetRefD _ _ _ l) k =
    transLocalDecl decl $ \decl' ->
    k $ LetD decl' l

transDecl decl@(E.LetFunD f ns vbs tau_ret e l) k
  | isPureishT tau_ret =
    ensureUnique f $ \f' ->
    extendVars [(f, tau)] $ do
    e' <- withSummaryContext decl $
          withFvContext e $
          extendLetFun f ns vbs tau_ret $
          transExp e
    k $ LetFunD (mkBoundVar f') ns vbs tau_ret e' l
  | otherwise =
    ensureUnique f $ \f' ->
    extendVars [(f, tau)] $ do
    c <- withSummaryContext decl $
         withFvContext e $
         extendLetFun f ns vbs tau_ret $
         transComp e
    k $ LetFunCompD (mkBoundVar f') ns vbs tau_ret c l
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

transDecl (E.LetExtFunD f ns vbs tau_ret l) k =
    extendExtFuns [(f, tau)] $
    k $ LetExtFunD (mkBoundVar f) ns vbs tau_ret l
  where
    tau :: Type
    tau = funT ns (map snd vbs) tau_ret l

transLocalDecl :: MonadTc m
               => E.Decl
               -> (LocalDecl -> TC m a)
               -> TC m a
transLocalDecl decl@(E.LetD v tau e l) k | isPureT tau =
    ensureUnique v $ \v' -> do
    e' <- withSummaryContext decl $ transExp e
    extendVars [(v, tau)] $
      k $ LetLD (mkBoundVar v') tau e' l

transLocalDecl (E.LetRefD v tau Nothing l) k =
    ensureUnique v $ \v' ->
    extendVars [(v, refT tau)] $
    k $ LetRefLD (mkBoundVar v') tau Nothing l

transLocalDecl decl@(E.LetRefD v tau (Just e) l) k =
    ensureUnique v $ \v' -> do
    e' <- withSummaryContext decl $
          inLocalScope $
          transExp e
    extendVars [(v, refT tau)] $
      k $ LetRefLD (mkBoundVar v') tau (Just e') l

transLocalDecl (E.LetTypeD alpha kappa tau l) k =
    extendTyVars [(alpha, kappa)] $
      k $ LetTypeLD alpha kappa tau l

transLocalDecl decl _ =
    withSummaryContext decl $
    faildoc $ text "Local declarations must be a let or letref, but this is a" <+> pprDeclType decl
  where
    pprDeclType :: E.Decl -> Doc
    pprDeclType E.StructD{}    = text "struct"
    pprDeclType E.LetD{}       = text "let"
    pprDeclType E.LetRefD{}    = text "let ref"
    pprDeclType E.LetTypeD{}   = text "let type"
    pprDeclType E.LetFunD{}    = text "fun"
    pprDeclType E.LetExtFunD{} = text "fun external"

transExp :: forall m . MonadTc m
         => E.Exp
         -> TC m Exp
transExp (E.ConstE c l) =
    return $ ConstE c l

transExp (E.VarE v l) = do
    v' <- lookupVarSubst v
    return $ VarE v' l

transExp (E.UnopE op e l) =
    UnopE op <$> transExp e <*> pure l

transExp (E.BinopE op e1 e2 l) =
    BinopE op <$> transExp e1 <*> transExp e2 <*> pure l

transExp (E.IfE e1 e2 e3 l) =
    IfE <$> transExp e1 <*> transExp e2 <*> transExp e3 <*> pure l

transExp (E.LetE cdecl e l) =
    transLocalDecl cdecl $ \decl ->
    LetE decl <$> transExp e <*> pure l

transExp (E.CallE f taus es l) = do
    f' <- lookupVarSubst f
    CallE f' taus <$> mapM transExp es <*> pure l

transExp (E.DerefE e l) =
    DerefE <$> transExp e <*> pure l

transExp (E.AssignE e1 e2 l) =
    AssignE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (E.LowerE tau l) =
    pure $ LowerE tau l

transExp (E.WhileE e1 e2 l) =
    WhileE <$> transExp e1 <*> transExp e2 <*> pure l

transExp (E.ForE ann v tau gint e l) =
    ensureUnique v $ \v' -> do
    gint' <- traverse (\e -> withFvContext e $ transExp e) gint
    e'    <- withFvContext e $
             extendVars [(v, tau)] $
             transExp e
    return $ ForE ann v' tau gint' e' l

transExp (E.ArrayE es l) =
    ArrayE <$> mapM transExp es <*> pure l

transExp (E.IdxE e1 e2 i l) =
    IdxE <$> transExp e1 <*> transExp e2 <*> pure i <*> pure l

transExp (E.StructE s taus flds l) =
    StructE s taus <$> mapM transField flds <*> pure l
  where
    transField :: (Field, E.Exp) -> TC m (Field, Exp)
    transField (f, e) = (,) <$> pure f <*> transExp e

transExp (E.ProjE e f l) =
    ProjE <$> transExp e <*> pure f <*> pure l

transExp (E.CastE tau e l) =
    CastE tau <$> transExp e <*> pure l

transExp (E.BitcastE tau e l) =
    BitcastE tau <$> transExp e <*> pure l

transExp (E.PrintE nl es l) =
    PrintE nl <$> mapM transExp es <*> pure l

transExp (E.ErrorE tau s l) =
    return $ ErrorE tau s l

transExp (E.ReturnE ann e l) =
    ReturnE ann <$> transExp e <*> pure l

transExp (E.BindE E.WildV tau e1 e2 l) = do
    e1' <- transExp e1
    e2' <- transExp e2
    return $ BindE WildV tau e1' e2' l

transExp (E.BindE (E.TameV v) tau e1 e2 l) =
    ensureUnique v $ \v' -> do
    e1' <- transExp e1
    e2' <- extendVars [(v, tau)] $
           transExp e2
    return $ BindE (TameV (mkBoundVar v')) tau e1' e2' l

transExp e@E.TakeE{} =
    withSummaryContext e $
    faildoc $ text "take expression seen in pure-ish computation"

transExp e@E.TakesE{} =
    withSummaryContext e $
    faildoc $ text "takes expression seen in pure-ish computation"

transExp e@E.EmitE{} =
    withSummaryContext e $
    faildoc $ text "emit expression seen in pure-ish computation"

transExp e@E.EmitsE{} =
    withSummaryContext e $
    faildoc $ text "emits expression seen in pure-ish computation"

transExp e@E.RepeatE{} =
    withSummaryContext e $
    faildoc $ text "repeat expression seen in pure-ish computation"

transExp e@E.ParE{} =
    withSummaryContext e $
    faildoc $ text "par expression seen in pure-ish computation"

transComp :: forall l m . (IsLabel l, MonadTc m)
          => E.Exp
          -> TC m (Comp l)
transComp e@(E.VarE v _) = do
    v'  <- lookupVarSubst v
    tau <- lookupVar v
    if isPureishT tau
      then liftC =<< transExp e
      else varC v'

transComp e@(E.IfE e1 e2 e3 l) = do
    tau <- inferExp e
    e1' <- transExp e1
    go tau e1'
  where
    go :: Type -> Exp -> TC m (Comp l)
    go tau e1' | isPureishT tau = do
        e2' <- transExp e2
        e3' <- transExp e3
        liftC $ IfE e1' e2' e3' l

    go _tau e1' = do
        e2' <- transComp e2
        e3' <- transComp e3
        ifC e1' e2' e3'

transComp (E.LetE cdecl e _) =
    transLocalDecl cdecl $ \decl ->
    localdeclC decl .>>. transComp e

transComp e@(E.CallE f taus es _) = do
    f'              <- lookupVarSubst f
    (_, _, tau_res) <- lookupVar f >>= checkFunT
    if isPureishT tau_res
      then liftC =<< transExp e
      else do args <- mapM transArg es
              callC f' taus args
  where
    transArg :: E.Exp -> TC m (Arg l)
    transArg e = do
        tau <- inferExp e
        if isPureT tau
          then ExpA  <$> transExp e
          else CompA <$> transComp e

transComp (E.WhileE e c _) = do
    e' <- transExp e
    c' <- transComp c
    whileC e' c'

transComp (E.ForE ann v tau gint e _) =
    ensureUnique v $ \v' -> do
    gint' <- traverse (\e -> withFvContext e $ transExp e) gint
    c'    <- withFvContext e $
             extendVars [(v, tau)] $
             transComp e
    forGenC ann v' tau gint' c'

transComp (E.ReturnE _ e _) = do
    e <- transExp e
    returnC e

transComp (E.BindE E.WildV tau e1 e2 _) =
    transComp e1 .>>. bindC WildV tau .>>. transComp e2

transComp (E.BindE (E.TameV v) tau e1 e2 _) =
    ensureUnique v $ \v' ->
    transComp e1
        .>>. bindC (TameV (mkBoundVar v')) tau
        .>>. (extendVars [(v, tau)] $ transComp e2)

transComp (E.TakeE tau _) =
    takeC tau

transComp (E.TakesE n tau _) =
    takesC n tau

transComp (E.EmitE e _) = do
    e' <- transExp e
    emitC e'

transComp (E.EmitsE e _) = do
    e' <- transExp e
    emitsC e'

transComp (E.RepeatE ann e _) = do
    c <- transComp e
    repeatC ann c

transComp (E.ParE ann b e1 e2 _) = do
    (s, a, c) <- askSTIndices
    c1        <- withFvContext e1 $
                 localSTIndices (Just (s, a, b)) $
                 transComp e1
    c2        <- withFvContext e2 $
                 localSTIndices (Just (b, b, c)) $
                 transComp e2
    parC ann b c1 c2

transComp e = do
    tau <- inferExp e
    e'  <- transExp e
    if isCompT tau
      then liftC e'
      else returnC e'
