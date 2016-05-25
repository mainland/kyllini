{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Trace
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Trace (
    MonadTrace(..),

    traceNest,

    traceRn,
    traceLift,
    traceTc,
    traceCg,
    traceLint,
    traceExprToCore,
    traceFusion,
    traceSimpl,
    traceEval,
    traceLUT,
    traceAutoLUT,
    traceRefFlow,
    traceNeedDefault,
    traceRate
  ) where

import Control.Monad (when)
#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Exception (ExceptionT(..), runExceptionT)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT(..))
import qualified Control.Monad.Trans.Cont as Cont
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid)
#endif /* !MIN_VERSION_base(4,8,0) */
import System.IO (hPutStrLn,
                  stderr)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland

import KZC.Flags

class MonadFlags m => MonadTrace m where
    askTraceDepth   :: m Int
    localTraceDepth :: (Int -> Int) -> m a -> m a

instance MonadTrace m => MonadTrace (MaybeT m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = MaybeT $ localTraceDepth f (runMaybeT m)

instance MonadTrace m => MonadTrace (ContT r m) where
    askTraceDepth   = lift askTraceDepth
    localTraceDepth = Cont.liftLocal askTraceDepth localTraceDepth

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadTrace m) => MonadTrace (ErrorT e m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ErrorT $ localTraceDepth f (runErrorT m)
#endif /* !MIN_VERSION_base(4,8,0) */

instance (MonadTrace m) => MonadTrace (ExceptT e m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ExceptT $ localTraceDepth f (runExceptT m)

instance (MonadTrace m) => MonadTrace (ExceptionT m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ExceptionT $ localTraceDepth f (runExceptionT m)

instance MonadTrace m => MonadTrace (ReaderT r m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ReaderT $ \r -> localTraceDepth f (runReaderT m r)

instance MonadTrace m => MonadTrace (StateT s m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = StateT $ \s -> localTraceDepth f (runStateT m s)

instance MonadTrace m => MonadTrace (S.StateT s m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = S.StateT $ \s -> localTraceDepth f (S.runStateT m s)

instance (Monoid w, MonadTrace m) => MonadTrace (WriterT w m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = WriterT $ localTraceDepth f (runWriterT m)

instance (Monoid w, MonadTrace m) => MonadTrace (S.WriterT w m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = S.WriterT $ localTraceDepth f (S.runWriterT m)

traceNest :: MonadTrace m => m a -> m a
traceNest = localTraceDepth (+1)

trace :: MonadTrace m => String -> Doc -> m ()
trace prefix doc = do
    d <- askTraceDepth
    let d'    = length prefix + 1 + 2*d
    let doc'  = spaces (2*d) <> nest d' doc
    return $!
        unsafePerformIO $
        hPutStrLn stderr (pretty 80 (text prefix <+> doc'))

traceIfSet :: MonadTrace m => TraceFlag -> String -> Doc -> m ()
traceIfSet flag prefix doc = do
    doTrace <- asksFlags (testTraceFlag flag)
    when doTrace $
        trace prefix doc

traceRn :: MonadTrace m => Doc -> m ()
traceRn = traceIfSet TraceRn "traceRn:"

traceLift :: MonadTrace m => Doc -> m ()
traceLift = traceIfSet TraceLift "traceLift:"

traceTc :: MonadTrace m => Doc -> m ()
traceTc = traceIfSet TraceTc "traceTc:"

traceCg :: MonadTrace m => Doc -> m ()
traceCg = traceIfSet TraceCg "traceCg:"

traceLint :: MonadTrace m => Doc -> m ()
traceLint = traceIfSet TraceLint "traceLint:"

traceExprToCore :: MonadTrace m => Doc -> m ()
traceExprToCore = traceIfSet TraceExprToCore "traceExprToCore:"

traceFusion :: MonadTrace m => Doc -> m ()
traceFusion = traceIfSet TraceFusion "traceFusion:"

traceSimpl :: MonadTrace m => Doc -> m ()
traceSimpl = traceIfSet TraceSimplify "traceSimplify:"

traceEval :: MonadTrace m => Doc -> m ()
traceEval = traceIfSet TraceEval "traceEval:"

traceLUT :: MonadTrace m => Doc -> m ()
traceLUT = traceIfSet TraceLUT "traceLUT:"

traceAutoLUT :: MonadTrace m => Doc -> m ()
traceAutoLUT = traceIfSet TraceAutoLUT "traceAutoLUT:"

traceRefFlow :: MonadTrace m => Doc -> m ()
traceRefFlow = traceIfSet TraceRefFlow "traceRefFlow:"

traceNeedDefault :: MonadTrace m => Doc -> m ()
traceNeedDefault = traceIfSet TraceNeedDefault "traceNeedDefault:"

traceRate :: MonadTrace m => Doc -> m ()
traceRate = traceIfSet TraceRate "traceRate:"

