{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Rename
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Rename (
    runRn,

    renameProgram
  ) where

import Prelude hiding (mapM)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader (asks)
import qualified Data.Map as Map
import Data.Traversable
import Text.PrettyPrint.Mainland

import Language.Ziria.Syntax

import KZC.Rename.Monad
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Uniq

renameProgram :: [CompLet] -> Rn [CompLet]
renameProgram = rnCompLets

extendVars :: Doc -> [Var] -> Rn a -> Rn a
extendVars desc vs m = do
    checkDuplicates desc vs
    vs' <- mapM ensureUniq vs
    extendEnv vars (\env x -> env { vars = x }) (vs `zip` vs') m

lookupVar :: Var -> Rn Var
lookupVar v =
    lookupEnv vars onerr v
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

extendCompVars :: Doc -> [Var] -> Rn a -> Rn a
extendCompVars desc vs m = do
    checkDuplicates desc vs
    vs' <- mapM ensureUniq vs
    extendEnv compVars (\env x -> env { compVars = x }) (vs `zip` vs') m

lookupMaybeCompVar :: Var -> Rn Var
lookupMaybeCompVar v = do
    incs     <- asks compScope
    maybe_v' <- if incs
                then asks (Map.lookup v . compVars)
                else asks (Map.lookup v . vars)
    case maybe_v' of
      Just v' -> return v'
      Nothing -> do maybe_v' <- asks (Map.lookup v . vars)
                    case maybe_v' of
                      Nothing -> onerr
                      Just v' -> return v'
  where
    onerr = faildoc $ text "Variable" <+> ppr v <+> text "not in scope"

ensureUniq :: Var -> Rn Var
ensureUniq v = do
    ins <- inscope v
    if ins then uniquify v else return v

inscope :: Var -> Rn Bool
inscope v = do
    member_vars <- asks (Map.member v . vars)
    if member_vars
       then return True
       else asks (Map.member v . compVars)

class Rename a where
    rn :: a -> Rn a

instance (Rename a, Traversable f) => Rename (f a) where
    rn = mapM rn

instance Rename Var where
    rn = lookupVar

instance Rename VarBind where
    rn (VarBind v tau isRef) = VarBind <$> rn v <*> pure tau <*> pure isRef

instance Rename Exp where
    rn e@ConstE{} =
        pure e

    rn (VarE v l) =
        VarE <$> rn v <*> pure l

    rn (UnopE op e l) =
        UnopE op <$> rn e <*> pure l

    rn (BinopE op e1 e2 l) =
        BinopE op <$> rn e1 <*> rn e2 <*> pure l

    rn (IfE e1 e2 e3 l) =
        IfE <$> rn e1 <*> rn e2 <*> rn e3 <*> pure l

    rn (LetE v tau e1 e2 l) =
        extendVars (text "definition") [v] $
        LetE <$> rn v <*> pure tau <*> rn e1 <*> rn e2 <*> pure l

    rn (CallE f es l) =
        CallE <$> lookupMaybeCompVar f <*> rn es <*> pure l

    rn (LetRefE v tau e1 e2 l) =
        extendVars (text "definition") [v] $
        LetRefE <$> rn v <*> pure tau <*> rn e1 <*> rn e2 <*> pure l

    rn (AssignE e1 e2 l) =
        AssignE <$> rn e1 <*> rn e2 <*> pure l

    rn (WhileE e1 e2 l) =
        WhileE <$> rn e1 <*> rn e2 <*> pure l

    rn (UntilE e1 e2 l) =
        UntilE <$> rn e1 <*> rn e2 <*> pure l

    rn (TimesE ann e1 e2 l) =
        TimesE <$> pure ann <*> rn e1 <*> rn e2 <*> pure l

    rn (ForE ann v tau e1 e2 e3 l) =
        extendVars (text "variable") [v] $
        ForE <$> pure ann <*> rn v <*> pure tau <*>
             rn e1 <*> rn e2 <*> rn e3 <*> pure l

    rn (ArrayE es l) =
        ArrayE <$> rn es <*> pure l


    rn (IdxE e1 e2 len l) =
        IdxE <$> rn e1 <*> rn e2 <*> pure len <*> pure l

    rn (StructE s flds l) =
        StructE <$> pure s <*> mapM rnField flds <*> pure l
      where
        rnField (f, e) = (,) <$> pure f <*> rn e

    rn (ProjE e f l) =
        ProjE <$> rn e <*> pure f <*> pure l

    rn (PrintE nl es l) =
        PrintE nl <$> rn es <*> pure l

    rn (ErrorE msg l) =
        pure $ ErrorE msg l

    rn (ReturnE ann e l) =
        ReturnE ann <$> rn e <*> pure l

    rn (TakeE l) =
        pure $ TakeE l

    rn (TakesE n l) =
        pure $ TakesE n l

    rn (EmitE e l) =
        EmitE <$> rn e <*> pure l

    rn (EmitsE e l) =
        EmitsE <$> rn e <*> pure l

    rn (RepeatE ann e l) =
        RepeatE ann <$> inCompScope (rn e) <*> pure l

    rn (ParE ann e1 e2 l) =
        ParE ann <$> inCompScope (rn e1) <*> inCompScope (rn e2) <*> pure l

    rn (ReadE tau l) =
        pure $ ReadE tau l

    rn (WriteE tau l) =
        pure $ WriteE tau l

    rn (StandaloneE e l) =
        StandaloneE <$> rn e <*> pure l

    rn (MapE ann f tau l) =
        -- @f@ may be a computation, so look there first. This fixes #15
        MapE ann <$> lookupMaybeCompVar f <*> pure tau <*> pure l

    rn (FilterE v tau l) =
        FilterE <$> rn v <*> pure tau <*> pure l

    rn (CompLetE cl e l) =
        rnCompLet cl $ \cl' -> do
        e' <- rn e
        return $ CompLetE cl' e' l

    rn (StmE stms l) =
        StmE <$> rnStms stms <*> pure l

    rn (CmdE cmds l) =
        CmdE <$> rnCmds cmds <*> pure l

rnCompLet :: CompLet -> (CompLet -> Rn a) -> Rn a
rnCompLet cl@(LetCL v tau e l) k =
    extendVars (text "variable") [v] $ do
    cl' <- withSummaryContext cl $
           LetCL <$> rn v <*> pure tau <*> inPureScope (rn e) <*> pure l
    k cl'

rnCompLet cl@(LetRefCL v tau e l) k =
    extendVars (text "mutable variable") [v] $ do
    cl' <-withSummaryContext cl $
            LetRefCL <$> rn v <*> pure tau <*> inPureScope (rn e) <*> pure l
    k cl'

rnCompLet cl@(LetFunCL v tau vbs e l) k =
    extendVars (text "function") [v] $ do
    cl' <- withSummaryContext cl $
           extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
           LetFunCL <$> rn v <*> pure tau <*> rn vbs <*> rn e <*> pure l
    k cl'

rnCompLet cl@(LetFunExternalCL v vbs tau isPure l) k =
    extendVars (text "external function") [v] $ do
    cl' <- withSummaryContext cl $
           extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
           LetFunExternalCL <$> rn v <*> rn vbs  <*> pure tau <*> pure isPure <*> pure l
    k cl'

rnCompLet cl@(LetStructCL s l) k = do
    cl' <- withSummaryContext cl $
           LetStructCL <$> pure s <*> pure l
    k cl'

rnCompLet cl@(LetCompCL v tau range e l) k =
    extendVars (text "computation") [v] $ do
    cl' <- withSummaryContext cl $
           LetCompCL <$> rn v <*> pure tau <*> pure range <*> inCompScope (rn e) <*> pure l
    k cl'

rnCompLet cl@(LetFunCompCL f tau range vbs e l) k =
    extendCompVars (text "computation function") [f] $ do
    cl' <- withSummaryContext cl $
           extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
           LetFunCompCL <$> inCompScope (lookupMaybeCompVar f) <*>
               pure tau <*> pure range <*> rn vbs <*> rn e <*> pure l
    k cl'

rnCompLets :: [CompLet] -> Rn [CompLet]
rnCompLets [] =
    return []

rnCompLets (cl:cls) =
    rnCompLet cl $ \cl' -> do
    cls' <- rnCompLets cls
    return (cl':cls')

rnStm :: Stm -> (Stm -> Rn a) -> Rn a
rnStm (LetS v tau e l) k =
    extendVars (text "definition") [v] $ do
    stm' <- LetS <$> rn v <*> pure tau <*> rn e <*> pure l
    k stm'

rnStm (LetRefS v tau e l) k =
    extendVars (text "definition") [v] $ do
    stm' <- LetRefS <$> rn v <*> pure tau <*> rn e <*> pure l
    k stm'

rnStm (ExpS e l) k = do
    stm' <- ExpS <$> rn e <*> pure l
    k stm'

rnStms :: [Stm] -> Rn [Stm]
rnStms [] =
    return []

rnStms (stm:stms) =
    rnStm stm $ \stm' -> do
    stms' <- rnStms stms
    return (stm':stms')

rnCmd :: Cmd -> (Cmd -> Rn a) -> Rn a
rnCmd (LetC cl l) k =
    rnCompLet cl $ \cl' ->
      k (LetC cl' l)

rnCmd (BindC v tau e l) k =
    extendVars (text "definition") [v] $ do
    cmd' <- BindC <$> rn v <*> pure tau <*> inCompScope (rn e) <*> pure l
    k cmd'

rnCmd (ExpC e l) k = do
    cmd' <- ExpC <$> inCompScope (rn e) <*> pure l
    k cmd'

rnCmds :: [Cmd] -> Rn [Cmd]
rnCmds [] =
    return []

rnCmds (cmd:cmds) =
    rnCmd cmd $ \cmd' -> do
    cmds' <- rnCmds cmds
    return (cmd':cmds')
