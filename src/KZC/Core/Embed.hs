{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Embed
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Core.Embed (
    K,
    runK,

    letC,
    letrefC,

    identityC,
    compC,
    varC,
    forC,
    forC',
    timesC,
    liftC,
    returnC,

    takeC,
    takesC,
    emitC,
    emitsC,

    repeatC,

    parC,
    parC'
  ) where

import Data.Loc
import Data.Monoid
import qualified Data.Set as Set

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Label
import KZC.Monad.KT
import KZC.Util.Summary
import KZC.Util.Uniq
import KZC.Vars

type K l m a = KT (Comp l) m a

runK :: MonadTc m => K l m a -> m (Comp l)
runK m = runKT (m >> return mempty)

-- | Sequence a computation with the continuation's computation.
seqC :: MonadTc m
     => Comp l
     -> K l m ()
seqC c1 =
    shift $ \k -> do
    c2 <- k ()
    return $ c1 <> c2

-- | Bind the result of a computation in the continuation's computation.
bindC :: (IsLabel l, MonadTc m)
      => Comp l
      -> Type
      -> K l m Exp
bindC c1 UnitT{} =
    shift $ \k -> do
    c2 <- k unitE
    return $ c1 <> c2

bindC c1 tau = do
    l <- gensym "bindk"
    v <- gensym "v"
    shift $ \k -> do
      c2 <- extendVars [(v, tau)] $
            k (varE v)
      return $
        if v `Set.member` fvs c2
        then c1 <> mkComp (BindC l (TameV (mkBoundVar v)) tau s : unComp c2)
        else c1 <> c2
  where
    s :: SrcLoc
    s = srclocOf tau

-- | Run a computation in the 'K' monad and obtain a representation of the
-- underlying 'Comp l'.
runComp :: MonadTc m
        => K l m a
        -> K l m (Comp l)
runComp m = reset $ m >> return mempty

letC :: (IsLabel l, MonadTc m)
     => String -> Type -> Exp -> (Exp -> K l m a) -> K l m a
letC v tau e f = do
    v'       <- gensym v
    let decl =  LetLD (mkBoundVar v') tau e (srclocOf tau)
    l        <- gensym "letk"
    shift $ \k -> do
        c <- runComp $ do
             x <- extendVars [(v', tau)] $
                  f (varE v')
             k x
        return $ mkComp (LetC l decl (srclocOf decl) : unComp c)

letrefC :: (IsLabel l, MonadTc m)
        => String -> Type -> (Exp -> K l m a) -> K l m a
letrefC v tau f = do
    v'       <- gensym v
    let decl =  LetRefLD (mkBoundVar v') tau Nothing (srclocOf tau)
    l        <- gensym "letrefk"
    shift $ \k -> do
        c <- runComp $ do
             x <- extendVars [(v', refT tau)] $
                  f (varE v')
             k x
        return $ mkComp (LetC l decl (srclocOf decl) : unComp c)

-- | Assert that a generated computation is the identity computation.
identityC :: (IsLabel l, MonadTc m)
          => Int
          -> K l m a
          -> K l m Exp
identityC n k = do
    comp <- runComp k
    compC $ tagIdentityC n comp

-- | Lift a 'Comp l' into the 'K' monad.
compC :: (IsLabel l, MonadTc m) => Comp l -> K l m Exp
compC c1 = do
    (omega, _, _, _) <- withSummaryContext c1 $
                        inferComp c1 >>= checkST
    -- If c1 is a transformer, throw away the continuation.
    case omega of
      C tau -> bindC c1 tau
      T{}   -> shift $ \_k -> return c1

varC :: (IsLabel l, MonadTc m) => Var -> K l m Exp
varC v = do
    l <- gensym "varC"
    compC $ mkComp [VarC l v s]
  where
    s :: SrcLoc
    s = srclocOf v

forC :: (Integral a, IsLabel l, MonadTc m)
     => a
     -> a
     -> (Exp -> K l m b)
     -> K l m ()
forC = forC' AutoUnroll

forC' :: (Integral a, IsLabel l, MonadTc m)
      => UnrollAnn
      -> a
      -> a
      -> (Exp -> K l m b)
      -> K l m ()
forC' _ann _i 0 _f =
    shift $ \k -> k ()

forC' _ann i 1 f =
    shift $ \k -> do
      c1 <- runComp $
            f (fromIntegral i)
      c2 <- k ()
      return $ c1 <> c2

forC' ann i len f = do
    v <- gensym "i"
    l <- gensym "fork"
    shift $ \k -> do
      c1 <- runComp $
            extendVars [(v, intT)] $
            f (varE v)
      c2 <- k ()
      return $ mkComp $ ForC l ann v intT (intE i) (intE len) c1 (srclocOf c1) : unComp c2

timesC :: (Integral a, IsLabel l, MonadTc m)
       => a
       -> K l m ()
       -> K l m ()
timesC n body = forC 0 n (const body)

liftC :: (IsLabel l, MonadTc m) => Exp -> K l m Exp
liftC e = do
    l                 <- gensym "liftk"
    (_, tau, _, _, _) <- withSummaryContext e $
                         inferExp e >>= checkPureishSTC
    bindC (mkComp [LiftC l e s]) tau
  where
    s :: SrcLoc
    s = srclocOf e

returnC :: (IsLabel l, MonadTc m) => Exp -> K l m Exp
returnC e = do
    l              <- gensym "returnk"
    (tau, _, _, _) <- withSummaryContext e $
                      inferExp e >>= checkSTC
    bindC (mkComp [ReturnC l e s]) tau
  where
    s :: SrcLoc
    s = srclocOf e

takeC :: (IsLabel l, MonadTc m) => Type -> K l m Exp
takeC tau = do
    l <- gensym "takek"
    bindC (mkComp [TakeC l tau s]) tau
  where
    s :: SrcLoc
    s = srclocOf tau

takesC :: (IsLabel l, MonadTc m) => Int -> Type -> K l m Exp
takesC n tau = do
    l <- gensym "takesk"
    bindC (mkComp [TakesC l n tau s]) (arrKnownT n tau)
  where
    s :: SrcLoc
    s = srclocOf tau

emitC :: (IsLabel l, MonadTc m) => Exp -> K l m ()
emitC e = do
    l <- gensym "emitk"
    seqC (mkComp [EmitC l e (srclocOf e)])

emitsC :: (IsLabel l, MonadTc m) => Exp -> K l m ()
emitsC e = do
    l <- gensym "emitsk"
    seqC (mkComp [EmitsC l e (srclocOf e)])

repeatC :: (IsLabel l, MonadTc m) => K l m a -> K l m Exp
repeatC body = do
    l <- gensym "repeatk"
    -- We don't call our continuation since the repeat never terminates
    shift $ \_k -> do
      c <- runComp body
      return $ mkComp [RepeatC l AutoVect c (srclocOf c)]

parC :: (IsLabel l, MonadTc m)
     => Type
     -> K l m a
     -> K l m b
     -> K l m Exp
parC = parC' AutoPipeline

parC' :: (IsLabel l, MonadTc m)
     => PipelineAnn
     -> Type
     -> K l m a
     -> K l m b
     -> K l m Exp
parC' ann b m1 m2 = do
    (s, a, c) <- askSTIndices
    c1        <- runComp $ localSTIndices (Just (s, a, b)) m1
    c2        <- runComp $ localSTIndices (Just (b, b, c)) m2
    compC $
      case (identityRateC c1, identityRateC c2) of
        (Just n, _) | hasLeftIdentity  c2 == Just n -> c2
        (_, Just n) | hasRightIdentity c1 == Just n -> c1
        _ -> mkComp [ParC ann b c1 c2 (c1 `srcspan` c2)]
  where
    hasLeftIdentity :: Comp l -> Maybe Int
    hasLeftIdentity Comp{unComp=[ParC _ _ c _ _]} =
      hasLeftIdentity c

    hasLeftIdentity c =
      identityRateC c

    hasRightIdentity :: Comp l -> Maybe Int
    hasRightIdentity Comp{unComp=[ParC _ _ _ c _]} =
      hasRightIdentity c

    hasRightIdentity c =
      identityRateC c
