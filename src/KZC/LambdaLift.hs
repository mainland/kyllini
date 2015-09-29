-- |
-- Module      :  KZC.LambdaLift
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.LambdaLift (
    runLift,

    liftProgram
  ) where

import Control.Applicative ((<$>), (<*>), pure)
import qualified Data.Set as Set

import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.LambdaLift.Monad
import KZC.Lint.Monad hiding (extendVars)
import KZC.Name
import KZC.Summary
import KZC.Uniq
import KZC.Vars
import KZC.Util.SetLike

liftProgram :: [Decl] -> Lift [Decl]
liftProgram decls = do
    [] <- liftDecls decls $ return []
    getTopDecls

liftDecls :: [Decl] -> Lift [Decl] -> Lift [Decl]
liftDecls [] k =
    k

liftDecls (decl:decls) k =
    liftDecl decl k'
  where
    k' :: Maybe Decl -> Lift [Decl]
    k' Nothing     = liftDecls decls k
    k' (Just decl) = (decl :) <$> liftDecls decls k

liftDecl :: Decl -> (Maybe Decl -> Lift a) -> Lift a
liftDecl decl@(LetD v tau e l) k = do
    e' <- withSummaryContext decl $
          withExpContext e $
          inSTScope tau $
          inLocalScope $
          liftExp e
    extendVars [(v, tau)] $ do
    withDecl (LetD v tau e' l) k

liftDecl decl@(LetFunD f iotas vbs tau_ret e l) k =
    extendVars [(f, tau)] $ do
    f'   <- uniquify f
    fvbs <- nonFunFvs decl
    extendFunFvs [(f, (f', map fst fvbs))] $ do
    e' <- withSummaryContext decl $
          extendIVars (iotas `zip` repeat IotaK) $
          extendVars vbs $
          withExpContext e $
          inSTScope tau_ret $
          inLocalScope $
          liftExp e
    appendTopDecl $ LetFunD f' iotas (fvbs ++ vbs) tau_ret e' l
    k Nothing
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

    nonFunFvs :: Decl -> Lift [(Var, Type)]
    nonFunFvs decl = do
        vs        <- (fvs decl <\\>) <$> askTopVars
        recurFvs  <- mapM lookupFvs (Set.toList vs)
        let allVs =  Set.toList $ Set.unions (vs : recurFvs)
        tau_allVs <- mapM lookupVar allVs
        return $ [(v, tau) | (v, tau) <- allVs `zip` tau_allVs, not (isFunT tau)]

    uniquify :: Var -> Lift Var
    uniquify f@(Var n) = do
        inLocalScope <- isInSTScope
        if inLocalScope
          then do u <- newUnique
                  return $ Var $ n { nameSort = Internal u }
          else return f

liftDecl (LetExtFunD f iotas vbs tau_ret l) k =
    extendVars [(f, tau)] $ do
    extendFunFvs [(f, (f, []))] $ do
    appendTopDecl $ LetExtFunD f iotas vbs tau_ret l
    k Nothing
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

liftDecl decl@(LetRefD v tau maybe_e l) k = do
    maybe_e' <-  withSummaryContext decl $
                 case maybe_e of
                   Nothing -> return Nothing
                   Just e -> Just <$> liftExp e
    extendVars [(v, refT tau)] $ do
    withDecl (LetRefD v tau maybe_e' l) k

liftDecl (LetStructD s flds l) k =
    extendStructs [StructDef s flds l] $
    withDecl (LetStructD s flds l) k

liftExp :: Exp -> Lift Exp
liftExp e@(ConstE {}) =
    pure e

liftExp e@(VarE {}) =
    pure e

liftExp e@(UnopE {}) =
    pure e

liftExp e@(BinopE {}) =
    pure e

liftExp (IfE e1 e2 e3 l) =
    IfE <$> liftExp e1 <*> liftExp e2 <*> liftExp e3 <*> pure l

liftExp (LetE d e l) =
    liftDecl d k
  where
    k :: Maybe Decl -> Lift Exp
    k Nothing     = liftExp e
    k (Just decl) = LetE decl <$> liftExp e <*> pure l

liftExp (CallE f iotas args l) = do
    (f', fvs) <- lookupFunFvs f
    return $ CallE f' iotas (map varE fvs ++ args) l

liftExp (DerefE e l) =
    DerefE <$> liftExp e <*> pure l

liftExp (AssignE e1 e2 l) =
    AssignE <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp (WhileE e1 e2 l) =
    WhileE <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp (ForE ann v tau e1 e2 e3 l) =
    ForE ann v tau <$> liftExp e1 <*> liftExp e2 <*> extendVars [(v, tau)] (liftExp e3) <*> pure l

liftExp (ArrayE es l) =
    ArrayE <$> mapM liftExp es <*> pure l

liftExp (IdxE e1 e2 len l) =
    IdxE <$> liftExp e1 <*> liftExp e2 <*> pure len <*> pure l

liftExp (StructE s flds l) =
    StructE s <$> mapM liftField flds <*> pure l
  where
    liftField :: (Field, Exp) -> Lift (Field, Exp)
    liftField (f, e) = (,) <$> pure f <*> liftExp e

liftExp (ProjE e f l) =
    ProjE <$> liftExp e <*> pure f <*> pure l

liftExp (PrintE nl es l) =
    PrintE nl <$> mapM liftExp es <*> pure l

liftExp e@(ErrorE {}) =
    pure e

liftExp (ReturnE ann e l) =
    ReturnE ann <$> liftExp e <*> pure l

liftExp (BindE v e1 e2 l) =
    BindE v <$> liftExp e1 <*> liftExp e2 <*> pure l

liftExp e@(TakeE {}) =
    pure e

liftExp e@(TakesE {}) =
    pure e

liftExp (EmitE e l) =
    EmitE <$> liftExp e <*> pure l

liftExp (EmitsE e l) =
    EmitsE <$> liftExp e <*> pure l

liftExp (RepeatE ann e l) =
    RepeatE ann <$> liftExp e <*> pure l

liftExp (ParE ann tau e1 e2 l) =
    ParE ann  tau <$> liftExp e1 <*> liftExp e2 <*> pure l
