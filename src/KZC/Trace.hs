{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Trace
-- Copyright   :  (c) 2014-2015 Drexel University
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
    traceAuto,
    traceAutoLint,
    traceFlatten,
    traceFusion
  ) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import System.IO (hPutStrLn,
                  stderr)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland

import KZC.Flags

class MonadFlags m => MonadTrace m where
    askTraceDepth   :: m Int
    localTraceDepth :: (Int -> Int) -> m a -> m a

instance (Error e, MonadTrace m) => MonadTrace (ErrorT e m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ErrorT $ localTraceDepth f (runErrorT m)

instance MonadTrace m => MonadTrace (ReaderT r m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = ReaderT $ \r -> localTraceDepth f (runReaderT m r)

instance MonadTrace m => MonadTrace (StateT s m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = StateT $ \s -> localTraceDepth f (runStateT m s)

instance (Monoid w, MonadTrace m) => MonadTrace (WriterT w m) where
    askTraceDepth       = lift askTraceDepth
    localTraceDepth f m = WriterT $ localTraceDepth f (runWriterT m)

traceNest :: MonadTrace m => m a -> m a
traceNest m = localTraceDepth (+1) m

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

traceAuto :: MonadTrace m => Doc -> m ()
traceAuto = traceIfSet TraceAuto "traceAuto:"

traceAutoLint :: MonadTrace m => Doc -> m ()
traceAutoLint = traceIfSet TraceAutoLint "traceAutoLint:"

traceFlatten :: MonadTrace m => Doc -> m ()
traceFlatten = traceIfSet TraceFlatten "traceFlatten:"

traceFusion :: MonadTrace m => Doc -> m ()
traceFusion = traceIfSet TraceFusion "traceFusion:"
