{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  KZC.Monad.SEFKT
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Monad.SEFKT (
    SEFKT(..),
    runSEFKT,
    runSEFKT1,
    runSEFKTM
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..),
                      ap)
import Control.Monad.Exception (Exception(..),
                                MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Logic (MonadLogic(..),
                            reflect)
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))
import Text.PrettyPrint.Mainland

import KZC.Error
import KZC.Expr.Lint.Monad
import KZC.Flags
import KZC.Trace
import KZC.Uniq

type SK ans a = a -> EK ans -> FK ans -> ans

type EK ans = SomeException -> FK ans -> ans

type FK ans = ans

newtype SEFKT m a = SEFKT { unSEFKT :: forall ans . EK (m ans) -> FK (m ans) -> SK (m ans) a -> m ans }

runSEFKT :: forall m a . MonadErr m => SEFKT m a -> m a
runSEFKT m =
    unSEFKT m errk failk $ \x _ek _fk -> return x
  where
    errk :: EK (m a)
    errk ex _fk = throw ex

    failk :: FK (m a)
    failk = fail "no answer"

runSEFKT1 :: forall m a . MonadErr m => SEFKT m a -> m (Maybe a)
runSEFKT1 m =
    unSEFKT m errk failk $ \x _ek _fk -> return (Just x)
  where
    errk :: EK (m (Maybe a))
    errk ex _fk = throw ex

    failk :: FK (m (Maybe a))
    failk = return Nothing

runSEFKTM :: forall m a . MonadErr m => Maybe Int -> SEFKT m a -> m [a]
runSEFKTM Nothing m = unSEFKT m errk failk succk
  where
    errk :: EK (m [a])
    errk ex _fk = throw ex

    failk :: FK (m [a])
    failk = return []

    succk :: SK (m [a]) a
    succk x _errk fk = fmap (x:) fk

runSEFKTM (Just n) _ | n <= 0 = return []

runSEFKTM (Just 1) m = unSEFKT m errk failk succk
  where
    errk :: EK (m [a])
    errk ex _fk = throw ex

    failk :: FK (m [a])
    failk = return []

    succk :: SK (m [a]) a
    succk x _ek _fk = return [x]

runSEFKTM (Just n) m = unSEFKT (msplit m) errk failk succk
  where
    errk :: EK (m [a])
    errk ex _fk = throw ex

    failk :: FK (m [a])
    failk = return []

    succk :: SK (m [a]) (Maybe (a, SEFKT m a))
    succk Nothing        _ek _fk = return []
    succk (Just (x, m')) _ek _fk = fmap (x:) (runSEFKTM (Just (n-1)) m')

instance MonadTrans SEFKT where
    lift m = SEFKT $ \ek fk sk -> m >>= \x -> sk x ek fk

instance MonadErr m => Functor (SEFKT m) where
    fmap f x = x >>= return . f

instance MonadErr m => Applicative (SEFKT m) where
    pure  = return
    (<*>) = ap

instance MonadErr m => Alternative (SEFKT m) where
    empty = SEFKT $ \_ek fk _sk -> fk

    m1 <|> m2 = SEFKT $ \ek fk sk -> unSEFKT m1 ek (unSEFKT m2 ek fk sk) sk

instance MonadErr m => Monad (SEFKT m) where
    {-# INLINE return #-}
    return x = SEFKT $ \ek fk sk -> sk x ek fk

    {-# INLINE (>>=) #-}
    m >>= f  = SEFKT $ \ek fk sk ->
               unSEFKT m     ek  fk  $ \x ek'  fk'  ->
               unSEFKT (f x) ek' fk' $ \y ek'' fk'' ->
               sk y ek'' fk''

    {-# INLINE (>>) #-}
    m1 >> m2 = SEFKT $ \ek fk sk ->
               unSEFKT m1 ek  fk  $ \_ ek'  fk'  ->
               unSEFKT m2 ek' fk' $ \y ek'' fk'' ->
               sk y ek'' fk''

    fail msg = throw (FailException (string msg))

instance MonadErr m => MonadPlus (SEFKT m) where
    mzero = Control.Applicative.empty
    mplus = (Control.Applicative.<|>)

instance MonadErr m => MonadLogic (SEFKT m) where
    msplit m = lift $ unSEFKT m ek fk sk
      where
        ek ex _fk   = throw ex
        fk          = return Nothing
        sk x _ek fk = return $ Just (x, lift fk >>= reflect)

instance (MonadErr m, MonadIO m) => MonadIO (SEFKT m) where
    liftIO = lift . liftIO

instance MonadErr m => MonadException (SEFKT m) where
    throw = throwContextException throw'
      where
        throw' ::  Exception ex => ex -> SEFKT m a
        throw' ex = SEFKT $ \ek fk _sk -> ek (toException ex) fk

    m `catch` h = SEFKT $ \ek fk sk ->
                  let ek' ex fk' =
                          case fromException ex of
                            Just ex' -> unSEFKT (h ex') ek fk' sk
                            Nothing  ->
                                case fromException ex of
                                  Just (ContextException _ ex') ->
                                      case fromException ex' of
                                        Just ex'' -> unSEFKT (h ex'') ek fk' sk
                                        Nothing  -> ek ex fk'
                                  Nothing -> ek ex fk'
                  in
                    unSEFKT m ek' fk sk

instance MonadErr m => MonadErr (SEFKT m) where
    askErrCtx       = lift askErrCtx
    localErrCtx f m = SEFKT $ \ek fk sk -> do
                      ctx <- askErrCtx
                      let ek' ex fk'    = localErrCtx (const ctx) (ek ex fk')
                          fk'           = localErrCtx (const ctx) fk
                          sk' x ek' fk' = localErrCtx (const ctx) (sk x ek' fk')
                      localErrCtx f (unSEFKT m ek' fk' sk')

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance (MonadErr m, MonadReader r m) => MonadReader r (SEFKT m) where
    ask       = SEFKT $ \ek fk sk -> ask >>= \r -> sk r ek fk
    local f m = SEFKT $ \ek fk sk -> do
                r <- ask
                let ek' ex fk'    = local (const r) (ek ex fk')
                    fk'           = local (const r) fk
                    sk' x ek' fk' = local (const r) (sk x ek' fk')
                local f (unSEFKT m ek' fk' sk')

instance (MonadErr m, MonadState s m) => MonadState s (SEFKT m) where
    get    = SEFKT $ \ek fk sk -> get >>= \s -> sk s ek fk
    put s' = SEFKT $ \ek fk sk -> do
             s <- get
             put s'
             let ek' ex fk' = put s >> ek ex fk'
                 fk'        = put s >> fk
             sk () ek' fk'

instance (MonadErr m, MonadUnique m) => MonadUnique (SEFKT m) where
    newUnique = lift newUnique

instance (MonadErr m, MonadFlags m) => MonadFlags (SEFKT m) where
    askFlags       = lift askFlags
    localFlags f m = SEFKT $ \ek fk sk -> do
                     fs <- askFlags
                     let ek' ex fk'    = localFlags (const fs) (ek ex fk')
                         fk'           = localFlags (const fs) fk
                         sk' x ek' fk' = localFlags (const fs) (sk x ek' fk')
                     localFlags f (unSEFKT m ek' fk' sk')

instance (MonadErr m, MonadTrace m) => MonadTrace (SEFKT m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = SEFKT $ \ek fk sk -> do
                          d <- askTraceDepth
                          let ek' ex fk'    = localTraceDepth (const d) (ek ex fk')
                              fk'           = localTraceDepth (const d) fk
                              sk' x ek' fk' = localTraceDepth (const d) (sk x ek' fk')
                          localTraceDepth f (unSEFKT m ek' fk' sk')

instance MonadTc m => MonadTc (SEFKT m) where
    askTc       = lift askTc
    localTc f m = SEFKT $ \ek fk sk -> do
                  r <- askTc
                  let ek' ex fk'    = localTc (const r) (ek ex fk')
                      fk'           = localTc (const r) fk
                      sk' x ek' fk' = localTc (const r) (sk x ek' fk')
                  localTc f (unSEFKT m ek' fk' sk')
