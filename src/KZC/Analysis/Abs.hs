{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Abs
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Abs (
    FunArg(..),
    Ref(..),
    ValDom(..),
    MonadAbs(..),

    absEval,
    inferRef,
    joinA,
    joinBranchA
  ) where

import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.State
import Data.Loc
import Text.PrettyPrint.Mainland hiding (empty)

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Util.Lattice

-- | A function argument. May be either a value of a reference.
data FunArg v = ValA v
              | RefA (Ref v)
  deriving (Eq, Ord, Show, Functor)

-- | A reference. References are either variables, an index of a reference, or a
-- projection of a reference.
data Ref v = VarR Var
           | IdxR (Ref v) v (Maybe Int)
           | ProjR (Ref v) Field
  deriving (Eq, Ord, Show, Functor)

-- | Infer the type of a @'Ref' v@.
inferRef :: forall m v . MonadTc m => Ref v -> m Type
inferRef (VarR v) =
    lookupVar v

inferRef (IdxR r _ len) =
    inferRef r >>= go
  where
    go :: Type -> m Type
    go (RefT (ArrT _ tau _) _) =
        return $ RefT (mkArrSlice tau len) noLoc

    go (ArrT _ tau _) = do
        return $ mkArrSlice tau len

    go tau =
        faildoc $ nest 2 $ group $
        text "Expected array type but got:" <+/> ppr tau

    mkArrSlice :: Type -> Maybe Int -> Type
    mkArrSlice tau Nothing  = tau
    mkArrSlice tau (Just i) = ArrT (ConstI i noLoc) tau noLoc

inferRef (ProjR r f) =
    inferRef r >>= go
  where
    go :: Type -> m Type
    go (RefT tau _) = do
        sdef  <- checkStructT tau >>= lookupStruct
        tau_f <- checkStructFieldT sdef f
        return $ RefT tau_f noLoc

    go tau = do
        sdef  <- checkStructT tau >>= lookupStruct
        tau_f <- checkStructFieldT sdef f
        return tau_f

-- | Value domain
class ValDom v where
    constDom  :: Const -> v
    unopDom   :: Unop -> v -> v
    binopDom  :: Binop -> v -> v -> v

    arrayDom  :: [v] -> v
    idxDom    :: Type -> v -> v -> Maybe Int -> v

    structDom :: Struct -> [(Field, v)] -> v
    projDom   :: Type -> v -> Field -> v

-- | Abstract interpreter monad
class ( Lattice s
      , Functor m
      , Applicative m
      , MonadTc m
      , BoundedLattice v
      , ValDom v)
    => MonadAbs s iv v m | m -> v, m -> iv, m -> s where
    iotaDom :: Iota -> m iv

    varDom :: Var -> m v

    ifDom :: v -> m v -> m v -> m v
    ifDom av_cond m1 m2 =
        joinA (withCond av_cond m1) (withCond (unopDom Lnot av_cond) m2)

    letDom    :: Var -> v -> m v -> m v
    letrefDom :: Var -> m v -> m v

    callDom   :: Var -> [iv] -> [FunArg v] -> m v

    derefDom  :: Ref v -> m v
    assignDom :: Ref v -> v -> m ()

    whileDom :: m v -> m v -> m v
    whileDom m_cond m_body = fixA $ do
        av_cond <- m_cond
        widenA av_cond (withCond av_cond m_body) (withCond (unopDom Lnot av_cond) skipA)

    forDom :: Var -> v -> v -> m v -> m v
    forDom i av_start av_len m_body = do
        letrefDom i $ do
        let r_i = VarR i
        assignDom r_i av_start
        let m_cond = do
            av_i <- derefDom r_i
            return $ binopDom Lt av_i av_bound
        let m_body' = do
            void $ m_body
            av_i <- derefDom r_i
            assignDom r_i (binopDom Add av_i (constDom (intC (1 :: Integer))))
            return $ constDom UnitC
        whileDom m_cond m_body'
      where
        av_bound :: v
        av_bound = binopDom Add av_start av_len

    printDom  :: Bool -> [v] -> m v
    errorDom  :: m ()

    returnDom :: v -> m v
    bindDom   :: WildVar -> v -> m v -> m v

    -- | Get abstract state
    getA :: m s

    -- | Put abstract state
    putA :: s -> m ()

    -- | Do nothing
    skipA :: m v
    skipA = return bot

    widenA :: v -> m v -> m v -> m v
    widenA v m1 m2 = joinA (withCond v m1) m2

    withCond :: v -> m v -> m v

-- | Join sequential control flow.
joinA :: (Lattice s, Lattice v, MonadAbs s iv v m)
      => m v -> m v -> m v
joinA m1 m2 = do
    (val1, post1) <- runA m1
    (val2, post2) <- runA m2
    putA $ post1 `lub` post2
    return $ val1 `lub` val2

-- | Join  control flow branches.
joinBranchA :: (BranchLattice s, BranchLattice v, MonadAbs s iv v m)
             => m v -> m v -> m v
joinBranchA m1 m2 = do
    (val1, post1) <- runA m1
    (val2, post2) <- runA m2
    putA $ post1 `bub` post2
    return $ val1 `bub` val2

-- | Run an abstract action without modifying the underlying abstract state,
-- returning the new abstract state produced by running the action.
runA :: MonadAbs s iv v m => m a -> m (a, s)
runA m = do
    pre  <- getA
    x    <- m
    post <- getA
    putA pre
    return (x, post)

fixA :: forall s iv v m a . MonadAbs s iv v m
     => m a -> m a
fixA m =
    loop
  where
    loop :: m a
    loop = do
        pre  <- getA
        x    <- m
        post <- getA
        if post <= pre then return x else loop

absEvalRef :: forall s iv v m . MonadAbs s iv v m => Exp -> m (Ref v)
absEvalRef e = go e
  where
    go :: Exp -> m (Ref v)
    go (VarE v _) =
        return $ VarR v

    go (IdxE e1 e2 len _) = do
        r   <- absEvalRef e1
        val <- absEval e2
        return $ IdxR r val len

    go (ProjE e f _) = do
        r <- absEvalRef e
        return $ ProjR r f

    go e =
        faildoc $ nest 2$
        text "Non-reference expression evaluated in reference context:" </> ppr e

absEvalArg :: forall s iv v m . MonadAbs s iv v m => Exp -> m (FunArg v)
absEvalArg e = do
    tau <- inferExp e
    case tau of
      RefT {} -> RefA <$> absEvalRef e
      _       -> ValA <$> absEval e

absEval :: forall s iv v m . MonadAbs s iv v m => Exp -> m v
absEval e = go e
  where
    go :: Exp -> m v
    go (ConstE c _) =
        return $ constDom c

    go (VarE v _) =
        varDom v

    go (UnopE op e _) =
        unopDom op <$> go e

    go (BinopE op e1 e2 _) =
        binopDom op <$> go e1 <*> go e2

    go (IfE e1 e2 e3 _) = do
        av1 <- go e1
        ifDom av1 (go e2) (go e3)

    go (LetE (LetLD v tau e1 _) e2 _) = do
        e1' <- go e1
        extendVars [(bVar v, refT tau)] $ do
        letDom (bVar v) e1' $ do
        go e2

    go (LetE (LetRefLD v tau Nothing _) e2 _) =
        extendVars [(bVar v, tau)] $
        letrefDom (bVar v) $
        go e2

    go (LetE (LetRefLD v tau (Just e1) _) e2 _) = do
        e1' <- go e1
        extendVars [(bVar v, tau)] $ do
        letrefDom (bVar v) $ do
        assignDom (VarR (bVar v)) e1'
        go e2

    go (CallE v iotas es _) = do
        ivs <- mapM iotaDom iotas
        vs  <- mapM absEvalArg es
        callDom v ivs vs

    go (DerefE e _) =
        absEvalRef e >>= derefDom

    go (AssignE e1 e2 _) = do
        r  <- absEvalRef e1
        av <- go e2
        assignDom r av
        return $ constDom UnitC

    go (WhileE e1 e2 _) =
        whileDom (go e1) (go e2)

    go (ForE _ v tau e_start e_len e_body _) = do
        v_start <- go e_start
        v_len   <- go e_len
        extendVars [(v, tau)] $ do
        forDom v v_start v_len (go e_body)

    go (ArrayE es _) =
        arrayDom <$> mapM go es

    go e0@(IdxE e1 e2 len _) = do
        tau <- inferExp e0
        idxDom <$> pure tau <*> go e1 <*> go e2 <*> pure len

    go (StructE s flds _) = do
        vs <- mapM go es
        return $ structDom s (fs `zip` vs)
      where
        (fs, es) = unzip flds

    go e0@(ProjE e f _) = do
        tau <- inferExp e0
        projDom <$> pure tau <*> go e <*> pure f

    go (PrintE nl es _) = do
        vs <- mapM go es
        printDom nl vs

    go (ErrorE _ _ _) = do
        errorDom
        return $ constDom UnitC

    go (ReturnE _ e _) = do
        v <- go e
        returnDom v

    go (BindE wv tau e1 e2 _) = do
        v_e1 <- go e1
        extendWildVars [(wv, tau)] $ do
        bindDom wv v_e1 (go e2)
