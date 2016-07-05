{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Autolut
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Autolut (
    autolutProgram
  ) where

import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Analysis.Lut (LUTInfo(..),
                         lutInfo,
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
               -> m (Program l)
autolutProgram = runAutoM . programT

instance MonadTc m => TransformExp (AutoM m) where
    expT (LutE _ e) =
        expT e
        
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
                                     return $ LutE (lutBytes info) e
                             else transExp e

instance MonadTc m => TransformComp l (AutoM m) where
