{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Autolut
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Autolut (
    autolutProgram,
    autolutComp
  ) where

import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Text.PrettyPrint.Mainland hiding (width)
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Lut (LUTInfo(..),
                         lutInfo,
                         shouldLUT)
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

newtype AutoM m a = AutoM { unAutoM :: m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadPlatform,
              MonadTrace,
              MonadTc)

instance MonadTrans AutoM where
    lift = AutoM

runAutoM :: AutoM m a -> m a
runAutoM = unAutoM

autolutProgram :: MonadTc m
               => Program l
               -> m (Program l)
autolutProgram = runAutoM . programT

autolutComp :: MonadTc m
            => Comp l
            -> m (Comp l)
autolutComp = runAutoM . compT

instance MonadTc m => TransformExp (AutoM m) where
    expT e@ConstE{} =
        return e

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
