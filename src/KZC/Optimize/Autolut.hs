{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Autolut
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Autolut (
    AutoM,
    runAutoM,

    autolutProgram
  ) where

import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Analysis.Lut (lutInfo,
                         shouldLUT)
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Trace
import KZC.Uniq

newtype AutoM m a = AutoM { unAutoM :: m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans AutoM where
    lift = AutoM

runAutoM :: MonadTc m => AutoM m a -> m a
runAutoM = unAutoM

autolutProgram :: (IsLabel l, MonadTc m)
               => Program l
               -> AutoM m (Program l)
autolutProgram = programT

instance MonadTc m => Transform (AutoM m) where
    expT e = do
        traceAutoLUT $ nest 2 $ text "Attempting to LUT:" </> ppr e
        maybe_info <- fmap Right (lutInfo e)
                        `catch` \(ex :: SomeException) -> return (Left ex)
        case maybe_info of
          Left  err  -> do traceAutoLUT $ text "Error:" <+> (text . show) err
                           transExp e
          Right info -> do traceAutoLUT $ ppr info
                           should <- shouldLUT info e
                           if should
                             then do traceAutoLUT $ nest 2 $ text "Creating LUT for:" </> ppr e
                                     return $ LutE e
                             else transExp e
