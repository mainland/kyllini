{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.LowerViews
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.LowerViews (
    lowerViews,
    lowerExpViews
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Map (Map)
import qualified Data.Map as Map

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

data LEnv = LEnv { views :: Map Var View }
  deriving (Eq, Ord, Show)

defaultLEnv :: LEnv
defaultLEnv = LEnv mempty

newtype L l m a = L { unL :: ReaderT LEnv m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadReader LEnv,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace,
              MonadTc)

instance MonadTrans (L l) where
    lift = L . lift

runL :: MonadTc m => L l m a -> m a
runL m = runReaderT (unL m) defaultLEnv

lowerViews :: forall l m . (IsLabel l, MonadTc m) => Program l -> m (Program l)
lowerViews = runL . lower
  where
    lower :: Program l -> L l m (Program l)
    lower = programT

lowerExpViews :: MonadTc m => Exp -> m Exp
lowerExpViews = runL . expT

lookupView :: MonadTc m => Var -> L l m (Maybe View)
lookupView v = asks (Map.lookup v . views)

extendViews :: MonadTc m
            => [(Var, View)]
            -> L l m a
            -> L l m a
extendViews = extendEnv views (\env x -> env { views = x })

instance MonadTc m => TransformExp (L l m) where
    expT e@(VarE v _) = do
        maybe_view <- lookupView v
        case maybe_view of
          Nothing   -> return e
          Just view -> expT (toExp view)

    -- Strictly speaking we don't have to handle this case separately from the
    -- VarE case, but it results in cleaner code.
    expT (IdxE e1@(VarE v s1) e2 len s) = do
        maybe_view <- lookupView v
        case maybe_view of
          Nothing                -> IdxE <$> pure e1 <*> expT e2 <*> pure len <*> pure s
          Just (IdxVW v' e3 _ _) -> expT $ IdxE (VarE v' s1) (e2 + e3) len s

    expT (LetE (LetViewLD v tau view _) e _) = do
        view' <- viewT view
        extendVars [(bVar v, tau)] $
          extendViews [(bVar v, view')] $
          expT e

    expT e = transExp e

instance (IsLabel l, MonadTc m) => TransformComp l (L l m) where
    declsT (LetD (LetViewLD v tau view _) _:decls) k = do
        view' <- viewT view
        extendVars [(bVar v, tau)] $
          extendViews [(bVar v, view')] $
          declsT decls k

    declsT decl k = transDecls decl k

    stepsT (LetC _ (LetViewLD v tau view _) _:steps) = do
        view' <- viewT view
        extendVars [(bVar v, tau)] $
          extendViews [(bVar v, view')] $
          stepsT steps

    stepsT steps = transSteps steps
