{-
Module      :  KZC.Monad.KT
Copyright   :  (c) 2016 Drexel University
License     :  BSD-style
Maintainer  :  mainland@cs.drexel.edu

A continuation monad transformer supporting delimited continuations as well as
exception handling.
-}

module KZC.Monad.KT (
    KT(..),
    runKT,

    shift,
    reset
  ) where

import Control.Monad (ap)
import Control.Monad.Exception (Exception(..),
                                MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans (MonadTrans(..))
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Lint
import KZC.Error
import KZC.Uniq
import KZC.Trace

-- | Success continuation
type SK m r a = EK m r -> a -> m r

-- | Exception continuation
type EK m r = SomeException -> m r

-- | The continuation monad transformer. Can be used to add continuation
-- handling to a member of 'MonadErr'. The transformed monad correctly supports
-- exceptions via 'MonadException' as well as 'MonadErr', 'MonadFlags',
-- 'MonadTrace', and 'MonadTc'.
newtype KT r m a = KT { unKT :: EK m r -> SK m r a -> m r }

runKT :: MonadErr m => KT a m a -> m a
runKT m = unKT m throw $ \_ek x -> return x

reset :: MonadErr m => KT a m a -> KT b m a
reset m = KT $ \ek sk -> unKT m throw (\_ek x -> return x) >>= sk ek

shift :: MonadErr m => ((a -> KT b m b) -> KT b m b) -> KT b m a
shift f = KT $ \ek sk ->
    let c x = KT $ \ek' sk' -> sk ek x >>= sk' ek'
    in
      runKT (f c)

instance MonadTrans (KT r) where
    lift m = KT $ \ek sk -> m >>= \x -> sk ek x

instance MonadErr m => Functor (KT r m) where
    fmap f x = x >>= return . f

instance MonadErr m => Applicative (KT r m) where
    pure  = return
    (<*>) = ap

instance MonadErr m => Monad (KT r m) where
    return x = KT $ \ek sk -> sk ek x

    m >>= f  = KT $ \ek sk ->
               unKT m     ek  $ \ek'  x ->
               unKT (f x) ek' $ \ek'' y ->
               sk ek'' y

    m1 >> m2 = KT $ \ek sk ->
               unKT m1 ek  $ \ek'  _ ->
               unKT m2 ek' $ \ek'' y ->
               sk ek'' y

    fail msg = throw (FailException (string msg))

instance (MonadErr m, MonadIO m) => MonadIO (KT r m) where
    liftIO = lift . liftIO

instance MonadErr m => MonadException (KT r m) where
    throw = throwContextException throw'
      where
        throw' ::  Exception ex => ex -> KT r m a
        throw' ex = KT $ \ek _sk -> ek (toException ex)

    m `catch` h = KT $ \ek sk ->
                  let ek' ex = case fromException ex of
                                 Just ex' -> unKT (h ex') ek sk
                                 Nothing  ->
                                   case fromException ex of
                                     Just (ContextException _ ex') ->
                                       case fromException ex' of
                                         Just ex'' -> unKT (h ex'') ek sk
                                         Nothing  -> ek ex
                                     Nothing -> ek ex
                  in
                    unKT m ek' sk

instance MonadErr m => MonadErr (KT r m) where
    askErrCtx   = lift askErrCtx
    localErrCtx = liftLocal askErrCtx localErrCtx

    displayWarning = lift . displayWarning

instance (MonadErr m, MonadUnique m) => MonadUnique (KT r m) where
    newUnique = lift newUnique

instance (MonadErr m, MonadFlags m) => MonadFlags (KT r m) where
    askFlags   = lift askFlags
    localFlags = liftLocal askFlags localFlags

instance (MonadErr m, MonadTrace m) => MonadTrace (KT r m) where
    askTraceDepth   = lift askTraceDepth
    localTraceDepth = liftLocal askTraceDepth localTraceDepth

instance MonadTc m => MonadTc (KT r m) where
    askTc   = lift askTc
    localTc = liftLocal askTc localTc

-- | @'liftLocal' ask local@ lifts a local function from @m@ to a local function
-- for @'KT' r m@.
liftLocal :: Monad m
          => m r'
          -> ((r' -> r') -> m r -> m r)
          -> (r' -> r')
          -> KT r m a
          -> KT r m a
liftLocal ask local f m = KT $ \ek sk -> do
    r <- ask
    let ek' ex    = local (const r) (ek ex)
        sk' ek' x = local (const r) (sk ek' x)
    local f (unKT m ek' sk')
