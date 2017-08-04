{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Rename
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Rename (
    liftRn,

    renameProgram
  ) where

import Data.Loc (locOf,
                 reloc)
import Text.PrettyPrint.Mainland

import Language.Ziria.Syntax

import KZC.Rename.Monad
import KZC.Util.Error
import KZC.Util.Summary

renameProgram :: Program -> (Program -> Rn a) -> Rn a
renameProgram prog k =
    rnModule prog $ \imports decls ->
    k $ Program imports decls

rnModule :: Program
         -> ([Import] -> [Decl] -> Rn a)
         -> Rn a
rnModule (Program imports decls) k =
    rnDecls decls $ \decls' ->
    k imports decls'

class Rename a where
    rn :: a -> Rn a

instance Rename a => Rename [a] where
    rn = mapM rn

instance Rename a => Rename (Maybe a) where
    rn = mapM rn

instance Rename TyVar where
    rn alpha = reloc (locOf alpha) <$> lookupTyVar alpha

instance Rename Var where
    rn v = reloc (locOf v) <$> lookupVar v

instance Rename VarBind where
    rn (VarBind v tau isRef) = VarBind <$> rn v <*> pure tau <*> pure isRef

instance Rename Type where
    rn tau@UnitT{}  = pure tau
    rn tau@BoolT{}  = pure tau
    rn tau@IntT{}   = pure tau
    rn tau@FixT{}   = pure tau
    rn tau@FloatT{} = pure tau

    rn (ArrT tau1 tau2 l) =
        ArrT <$> rn tau1 <*> rn tau2 <*> pure l

    rn (StructT s taus l) =
        StructT s <$> traverse rn taus <*> pure l

    rn (C tau l) =
        C <$> rn tau <*> pure l

    rn tau@T{} =
        pure tau

    rn (ST tau1 tau2 tau3 l) =
        ST <$> rn tau1 <*> rn tau2 <*> rn tau3 <*> pure l

    rn tau@NatT{} =
        pure tau

    rn (LenT v l) =
        LenT <$> rn v <*> pure l

    rn (UnopT op tau l) =
        UnopT op <$> rn tau <*> pure l

    rn (BinopT op tau1 tau2 l) =
        BinopT op <$> rn tau1 <*> rn tau2 <*> pure l

    rn tau@UnknownT{} =
        pure tau

    rn (ForallT tvks tau l) =
        extendTyVars (text "type variable") (map fst tvks) $
        ForallT <$> rn tvks <*> rn tau <*> pure l

    rn (TyVarT alpha l) =
        TyVarT <$> rn alpha <*> pure l

instance Rename Exp where
    rn e@ConstE{} =
        pure e

    rn (VarE v@(Var n) l) = do
        maybe_v' <- maybeLookupVar v
        case maybe_v' of
          Just v' -> return $ VarE v' l
          Nothing -> do maybe_alpha <- maybeLookupTyVar (TyVar n)
                        case maybe_alpha of
                          Just alpha -> return $ TyVarE alpha l
                          Nothing    -> notInScope (text "Variable") v

    rn (TyVarE alpha l) =
        TyVarE <$> rn alpha <*> pure l

    rn (UnopE op e l) =
        UnopE op <$> rn e <*> pure l

    rn (BinopE op e1 e2 l) =
        BinopE op <$> rn e1 <*> rn e2 <*> pure l

    rn (IfE e1 e2 e3 l) =
        IfE <$> rn e1 <*> rn e2 <*> rn e3 <*> pure l

    rn (LetE v tau e1 e2 l) =
        extendVars (text "definition") [v] $
        LetE <$> rn v <*> rn tau <*> rn e1 <*> rn e2 <*> pure l

    rn (LetRefE v tau e1 e2 l) =
        extendVars (text "definition") [v] $
        LetRefE <$> rn v <*> rn tau <*> rn e1 <*> rn e2 <*> pure l

    rn (LetTypeE alpha tau e l) =
        extendTyVars (text "definition") [alpha] $
        LetTypeE <$> rn alpha <*> rn tau <*> rn e <*> pure l

    rn (LetDeclE decl e l) =
        rnDecl decl $ \decl' -> do
        e' <- rn e
        return $ LetDeclE decl' e' l

    rn (CallE f taus es l) =
        CallE <$> lookupMaybeCompVar f <*> traverse rn taus <*> rn es <*> pure l

    rn (AssignE e1 e2 l) =
        AssignE <$> rn e1 <*> rn e2 <*> pure l

    rn (WhileE e1 e2 l) =
        WhileE <$> rn e1 <*> rn e2 <*> pure l

    rn (UntilE e1 e2 l) =
        UntilE <$> rn e1 <*> rn e2 <*> pure l

    rn (TimesE ann e1 e2 l) =
        TimesE <$> pure ann <*> rn e1 <*> rn e2 <*> pure l

    rn (ForE ann v tau int e l) =
        extendVars (text "variable") [v] $
        ForE <$> pure ann <*> rn v <*> rn tau <*> rn int <*> rn e <*> pure l

    rn (ArrayE es l) =
        ArrayE <$> rn es <*> pure l

    rn (IdxE e1 e2 len l) =
        IdxE <$> rn e1 <*> rn e2 <*> pure len <*> pure l

    rn (StructE s taus flds l) =
        StructE s <$> traverse rn taus <*> traverse rnField flds <*> pure l
      where
        rnField (f, e) = (,) <$> pure f <*> rn e

    rn (ProjE e f l) =
        ProjE <$> rn e <*> pure f <*> pure l

    rn (CastE tau e l) =
        CastE <$> rn tau <*> rn e <*> pure l

    rn (BitcastE tau e l) =
        BitcastE <$> rn tau <*> rn e <*> pure l

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
        MapE ann <$> lookupMaybeCompVar f <*> rn tau <*> pure l

    rn (FilterE v tau l) =
        FilterE <$> rn v <*> rn tau <*> pure l

    rn (StmE stms l) =
        StmE <$> rnStms stms <*> pure l

instance Rename GenInterval where
    rn (FromToInclusive e1 e2 l) =
        FromToInclusive <$> rn e1 <*> rn e2 <*> pure l

    rn (FromToExclusive e1 e2 l) =
        FromToExclusive <$> rn e1 <*> rn e2 <*> pure l

    rn (StartLen e1 e2 l) =
        StartLen <$> rn e1 <*> rn e2 <*> pure l

instance Rename (TyVar, Maybe Kind) where
    rn (alpha, kappa) = (,) <$> rn alpha <*> pure kappa

instance Rename (Field, Type) where
    rn (fld, tau) = (,) <$> pure fld <*> rn tau

rnDecl :: Decl -> (Decl -> Rn a) -> Rn a
rnDecl decl@(StructD s tvks flds l) k = do
    decl' <- withSummaryContext decl $
             extendTyVars (text "type variable") (map fst tvks) $
             StructD s <$> rn tvks <*> rn flds <*> pure l
    k decl'

rnDecl decl@(TypeD s tvks tau l) k = do
    decl' <- withSummaryContext decl $
             extendTyVars (text "type variable") (map fst tvks) $
             TypeD s <$> rn tvks <*> rn tau <*> pure l
    k decl'

rnDecl decl@(LetD v tau e l) k =
    extendVars (text "variable") [v] $ do
    decl' <- withSummaryContext decl $
             LetD <$> rn v <*> rn tau <*> inPureScope (rn e) <*> pure l
    k decl'

rnDecl decl@(LetRefD v tau e l) k =
    extendVars (text "mutable variable") [v] $ do
    decl' <- withSummaryContext decl $
             LetRefD <$> rn v <*> rn tau <*> inPureScope (rn e) <*> pure l
    k decl'

rnDecl decl@(LetTypeD alpha kappa tau l) k =
    extendTyVars (text "nat variable") [alpha] $ do
    decl' <- withSummaryContext decl $
             LetTypeD <$> rn alpha <*> pure kappa <*> rn tau <*> pure l
    k decl'

rnDecl decl@(LetFunD v tvks vbs tau_ret e l) k =
    extendVars (text "function") [v] $ do
    decl' <- withSummaryContext decl $
             extendTyVars (text "type variable") (map fst tvks) $
             extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
             LetFunD <$> rn v <*> rn tvks <*> rn vbs <*> rn tau_ret <*> rn e <*> pure l
    k decl'

rnDecl decl@(LetFunExternalD v vbs tau isPure l) k =
    extendVars (text "external function") [v] $ do
    decl' <- withSummaryContext decl $
             extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
             LetFunExternalD <$> rn v <*> rn vbs <*> rn tau <*> pure isPure <*> pure l
    k decl'

rnDecl decl@(LetCompD v tau range e l) k =
    extendVars (text "computation") [v] $ do
    decl' <- withSummaryContext decl $
             LetCompD <$> rn v <*> rn tau <*> pure range <*> inCompScope (rn e) <*> pure l
    k decl'

rnDecl decl@(LetFunCompD f range tvks vbs tau_ret e l) k =
    extendCompVars (text "computation function") [f] $ do
    decl' <- withSummaryContext decl $
             extendTyVars (text "type variable") (map fst tvks) $
             extendVars (text "parameters") [v | VarBind v _ _ <- vbs] $
             LetFunCompD <$> inCompScope (lookupMaybeCompVar f) <*>
                 pure range <*> rn tvks <*> rn vbs <*> rn tau_ret <*> rn e <*> pure l
    k decl'

rnDecls :: [Decl]
        -> ([Decl] -> Rn a)
        -> Rn a
rnDecls [] k =
    k []

rnDecls (decl:decls) k =
    rnDecl  decl  $ \decl'  ->
    rnDecls decls $ \decls' ->
    k (decl':decls')

rnStm :: Stm -> (Stm -> Rn a) -> Rn a
rnStm (LetS cl l) k =
    rnDecl cl $ \cl' ->
      k (LetS cl' l)

rnStm (BindS v tau e l) k =
    extendVars (text "definition") [v] $ do
    stm' <- BindS <$> rn v <*> rn tau <*> inCompScope (rn e) <*> pure l
    k stm'

rnStm (ExpS e l) k = do
    stm' <- ExpS <$> inCompScope (rn e) <*> pure l
    k stm'

rnStms :: [Stm] -> Rn [Stm]
rnStms [] =
    return []

rnStms (stm:stms) =
    rnStm stm $ \stm' -> do
    stms' <- rnStms stms
    return (stm':stms')
