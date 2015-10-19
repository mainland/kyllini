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
    traceLint
  ) where

import Control.Monad.Reader
import System.IO (hPutStrLn,
                  stderr)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.Mainland

import KZC.Flags

class MonadFlags m => MonadTrace m where
    asksTraceDepth :: m Int
    localTraceDepth :: Int -> m a -> m a

traceNest :: MonadTrace m => m a -> m a
traceNest m = do
    d <- asksTraceDepth
    localTraceDepth (d+1) m

trace :: MonadTrace m => String -> Doc -> m ()
trace prefix doc = do
    d <- asksTraceDepth
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