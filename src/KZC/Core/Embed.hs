{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Core.Embed
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Core.Embed (
    K(..),
    runK,

    letref,

    varC,
    forC,
    timesC,
    liftC,
    returnC,

    takeC,
    takesC,
    emitC,
    emitsC
  ) where

import Control.Monad.Exception (MonadException(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Cont (ContT(..),
                                 shiftT,
                                 resetT,
                                 runContT)
import qualified Control.Monad.Trans.Cont as Cont
import Data.Loc
import Data.Monoid

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Name
import KZC.Trace
import KZC.Uniq

newtype K l m a = K { unK :: ContT (Comp l) m a }
  deriving (Functor, Applicative, Monad,
            MonadUnique,
            MonadFlags,
            MonadTrace)

instance MonadTrans (K l) where
    lift = K . lift

--- XXX This does not correctly lift throw and catch since the catch scopes over
--- the /entire/ continuation. However, we need both shift and reset and our
--- MonadTc instance, so...
instance MonadException m => MonadException (K l m) where
    throw = lift . throw

    e `catch` h = K $ ContT $ \k -> runContT (unK e) k `catch` \ex -> runContT (unK (h ex)) k

instance MonadErr m => MonadErr (K l m) where
    askErrCtx       = lift askErrCtx
    localErrCtx f m = K $ Cont.liftLocal askErrCtx localErrCtx f (unK m)

    displayWarning = lift . displayWarning

instance MonadTc m => MonadTc (K l m) where
    askTc       = lift askTc
    localTc f m = K $ Cont.liftLocal askTc localTc f (unK m)

runK :: MonadException m => K l m a -> m (Comp l)
runK m = runContT (unK m >> return mempty) return

reset :: Monad m => K l m (Comp l) -> K l m (Comp l)
reset m = K $ resetT (unK m)

shift :: forall l m a . Monad m => ((a -> K l m (Comp l)) -> K l m (Comp l)) -> K l m a
shift k = K $ shiftT k'
  where
    k' f = unK $ k (lift . f)

letref :: (IsLabel l, MonadUnique m)
       => Var -> Type -> (Exp -> K l m ()) -> K l m ()
letref v tau f = do
    v'       <- gensym (namedString v)
    let decl =  LetRefLD (mkBoundVar v') tau Nothing (v `srcspan` tau)
    l        <- gensym "letrefk"
    shift $ \k -> do
        c1 <- reset $ f (varE v') >> return mempty
        c2 <- k ()
        return $ mkComp (LetC l decl (srclocOf decl) : unComp c1) <> c2

bindC :: (IsLabel l, MonadTc m)
      => Type
      -> (Exp -> K l m (Comp l))
      -> K l m (Comp l)
bindC tau k = do
    l <- gensym "bindk"
    v <- gensym "v"
    c <- k (varE v)
    return $ mkComp $ BindC l (TameV (mkBoundVar v)) tau s : unComp c
  where
    s :: SrcLoc
    s = srclocOf tau

varC :: (IsLabel l, MonadTc m) => Var -> K l m Exp
varC v = do
    l   <- gensym "varC"
    tau <- inferComp (mkComp [VarC l v s])
    shift $ \k -> do
      c <- bindC tau k
      return $ mkComp $ VarC l v s : unComp c
  where
    s :: SrcLoc
    s = srclocOf v

forC :: (Integral a, IsLabel l, MonadTc m)
      => a
      -> a
      -> (Exp -> K l m ())
      -> K l m ()
forC i j f = do
    v <- gensym "i"
    l <- gensym "fork"
    shift $ \k -> do
      c1 <- reset $ f (varE v) >> return mempty
      c2 <- k ()
      return $ mkComp $ ForC l AutoUnroll v intT (intE i) (intE j) c1 (srclocOf c1) : unComp c2

timesC :: (Integral a, IsLabel l, MonadTc m)
       => a
       -> K l m ()
       -> K l m ()
timesC n body = forC 0 n (const body)

liftC :: (IsLabel l, MonadTc m) => Exp -> K l m Exp
liftC e = do
    l   <- gensym "liftk"
    tau <- inferExp e
    shift $ \k -> do
      c <- bindC tau k
      return $ mkComp $ LiftC l e s : unComp c
  where
    s :: SrcLoc
    s = srclocOf e

returnC :: (IsLabel l, MonadTc m) => Exp -> K l m Exp
returnC e = do
    l   <- gensym "returnk"
    tau <- inferExp e
    shift $ \k -> do
      c <- bindC tau k
      return $ mkComp $ ReturnC l e s : unComp c
  where
    s :: SrcLoc
    s = srclocOf e

takeC :: (IsLabel l, MonadTc m) => Type -> K l m Exp
takeC tau = do
    l <- gensym "takek"
    shift $ \k -> do
      c <- bindC tau k
      return $ mkComp $ TakeC l tau s : unComp c
  where
    s :: SrcLoc
    s = srclocOf tau

takesC :: (IsLabel l, MonadTc m) => Int -> Type -> K l m Exp
takesC n tau = do
    l <- gensym "takesk"
    shift $ \k -> do
      c <- bindC tau k
      return $ mkComp $ TakesC l n tau s : unComp c
  where
    s :: SrcLoc
    s = srclocOf tau

emitC :: (IsLabel l, MonadUnique m) => Exp -> K l m ()
emitC e = do
    l <- gensym "emitk"
    shift $ \k -> do
      c <- k ()
      return $ mkComp $ EmitC l e (srclocOf e) : unComp c

emitsC :: (IsLabel l, MonadUnique m) => Exp -> K l m ()
emitsC e = do
    l <- gensym "emitsk"
    shift $ \k -> do
      c <- k ()
      return $ mkComp $ EmitsC l e (srclocOf e) : unComp c
