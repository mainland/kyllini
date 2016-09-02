{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.HashConsConsts
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.HashConsConsts (
    hashConsConsts
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Foldable (toList)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence ((|>)
                     ,Seq)
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Label
import KZC.Trace
import KZC.Uniq

data HCState l = HCState
    { topDecls :: !(Seq (Decl l))
    , consts   :: !(Map Const Var)
    }

defaultHCState :: HCState l
defaultHCState = HCState
    { topDecls = mempty
    , consts   = mempty
    }

newtype HC l m a = HC { unHC :: StateT (HCState l) m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState (HCState l),
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans (HC l) where
    lift m = HC $ lift m

runHC :: MonadTc m => HC l m a -> m a
runHC m = evalStateT (unHC m) defaultHCState

getTopDecls :: MonadTc m => HC l m [Decl l]
getTopDecls = do
    decls <- gets topDecls
    modify $ \s -> s { topDecls = mempty }
    return $ toList decls

appendTopDecl :: MonadTc m => Decl l -> HC l m ()
appendTopDecl decl = modify $ \s -> s { topDecls = topDecls s |> decl }

lookupConst :: MonadTc m => Const -> HC l m (Maybe Var)
lookupConst c = gets (Map.lookup c . consts)

insertConst :: MonadTc m => Const -> HC l m Var
insertConst c = do
    v   <- gensym "constarr"
    tau <- inferConst noLoc c
    appendTopDecl $ LetD (letD v tau (constE c)) noLoc
    modify $ \s -> s { consts = Map.insert c v (consts s) }
    return v

hashConsConsts :: forall l m . (IsLabel l, MonadTc m)
               => Program l
               -> m (Program l)
hashConsConsts = runHC . hashConsProgram
  where
    hashConsProgram :: Program l -> HC l m (Program l)
    hashConsProgram = programT

instance (IsLabel l, MonadTc m) => TransformExp (HC l m) where
    expT (LetE decl e s) = do
        (decl', e') <- localDeclT decl $
                       transExp e
        return $ LetE decl' e' s

    expT (ConstE c _) | isArrC c = do
        v <- maybe (insertConst c) return =<< lookupConst c
        return $ varE v

    expT e@GenE{} =
        return e

    expT e =
        transExp e

instance (IsLabel l, MonadTc m) => TransformComp l (HC l m) where
    declsT [] m = do
        x     <- m
        decls <- getTopDecls
        return (decls, x)

    declsT (d:ds) m = do
        (d', (ds1, ds2, x)) <-
            declT d $ do
            ds1      <- getTopDecls
            (ds2, x) <- declsT ds m
            return (ds1, ds2, x)
        return (ds1 ++ d':ds2, x)
