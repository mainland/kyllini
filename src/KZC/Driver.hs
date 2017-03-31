-- |
-- Module      : KZC.Driver
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module KZC.Driver (
    defaultMainWith,
    defaultMain,

    parseKzcOpts,
    kzcUsage
  ) where

import Control.Monad.Exception
import System.Environment
import System.Exit (exitFailure)
import System.IO (hPrint,
                  hPutStrLn,
                  stderr)

import KZC.Config
import KZC.Compiler
import KZC.Driver.Opts
import KZC.Monad

defaultMain :: IO ()
defaultMain = do
    args          <- getArgs
    (conf, files) <- parseKzcOpts args
    if mode conf == Help
      then kzcUsage >>= hPutStrLn stderr
      else defaultMainWith conf files

defaultMainWith :: Config -> [FilePath] -> IO ()
defaultMainWith conf files =
    evalKZC conf (compileFiles files) `catch` printFailure
  where
    printFailure :: SomeException -> IO ()
    printFailure e = hPrint stderr e >> exitFailure
