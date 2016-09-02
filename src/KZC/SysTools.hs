{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      : KZC.SysTools
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

#include "KzcSysTools.h"

module KZC.SysTools (
    runCpp
  ) where

import Control.Concurrent (forkIO,
                           newEmptyMVar,
                           putMVar,
                           takeMVar)
import qualified Control.Exception as E
import Control.Monad (unless)
import Control.Monad.IO.Class
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as TIO
import System.Exit (ExitCode(..))
import System.FilePath (takeDirectory)
import System.Process (StdStream(..),
                       proc,
                       createProcess,
                       waitForProcess,
                       std_in,
                       std_out,
                       std_err)
import System.IO (hClose,
                  hFlush)
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Monad

globalDefines :: [(String, String)]
globalDefines = [("__KZC__", "1")]

runCpp :: FilePath -> T.Text -> KZC T.Text
runCpp filepath txt = do
    includePaths  <-  asksFlags includePaths
    defines       <-  asksFlags defines
    let args'     =   args ++ ["-undef", "-", "-o", "-"] ++
                      ["-I"++path | path <- takeDirectory filepath : includePaths] ++
                      ["-D"++d++"="++def | (d, def) <- defines ++ globalDefines]
    (ex, out, err) <- liftIO $ readProcessWithExitCode prog args' (prefix <> txt)
    unless (ex == ExitSuccess) $
       faildoc $ text "Cannot invoke cpp:" <+>
                (text . show) ex <+> (string . T.unpack) err
    return out
  where
    prefix :: T.Text
    prefix = T.pack ("# 1 \"" ++ filepath ++ "\"\n")

    prog :: String
    args :: [String]
    prog:args = words CPP

readProcessWithExitCode :: FilePath                      -- Command to run
                        -> [String]                      -- Arguments
                        -> T.Text                        -- Standard input
                        -> IO (ExitCode, T.Text, T.Text) -- exitcode, stdout, stderr
readProcessWithExitCode cmd args input = do
    (Just inh, Just outh, Just errh, pid) <-
        createProcess (proc cmd args){ std_in  = CreatePipe,
                                       std_out = CreatePipe,
                                       std_err = CreatePipe }

    outMVar <- newEmptyMVar

    -- Fork a thread to consume stdout
    out  <- TIO.hGetContents outh
    _ <- forkIO $ E.evaluate (T.length out) >> putMVar outMVar ()

    -- Fork a thread to consume stderr
    err  <- TIO.hGetContents errh
    _ <- forkIO $ E.evaluate (T.length err) >> putMVar outMVar ()

    -- Write and flush input
    unless (T.null input) $ do
        TIO.hPutStr inh input
        hFlush inh
    -- Done with stdin
    hClose inh

    -- Wait on the output
    takeMVar outMVar
    takeMVar outMVar

    -- Done with stdout and stdin
    hClose outh
    hClose errh

    -- Wait on the process
    ex <- waitForProcess pid

    return (ex, out, err)
