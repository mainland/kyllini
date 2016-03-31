{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Transform.LambdaLift.Monad
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Transform.LambdaLift.Monad (
    Lift,
    runLift,

    lookupFvs,
    lookupFunFvs,
    extendFunFvs,

    withDecl,

    appendTopDecl,
    getTopDecls
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)
import Data.Map (Map)
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (mempty)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Sequence (Seq, (|>))
import Data.Set (Set)
import qualified Data.Set as Set

import KZC.Core.Lint (Tc, liftTc, isInTopScope)
import KZC.Core.Syntax
import KZC.Monad
import KZC.Util.Env

type Lift a = ReaderT LiftEnv (StateT LiftState Tc) a

data LiftEnv = LiftEnv
    { funFvs :: Map Var (Var, [Var]) }

defaultLiftEnv :: LiftEnv
defaultLiftEnv = LiftEnv
    { funFvs = mempty }

data LiftState = LiftState
    { topdecls :: !(Seq Decl) }

defaultLiftState :: LiftState
defaultLiftState = LiftState
    { topdecls = mempty }

-- | Evaluate a 'Lift' action and return a list of 'C.Definition's.
runLift :: Lift a -> KZC a
runLift m = liftTc $ evalStateT (runReaderT m defaultLiftEnv) defaultLiftState

lookupFvs :: Var -> Lift (Set Var)
lookupFvs v = do
  maybe_fvs <- asks (Map.lookup v . funFvs)
  case maybe_fvs of
    Nothing      -> return mempty
    Just (_, vs) -> return (Set.fromList vs)

lookupFunFvs :: Var -> Lift (Var, [Var])
lookupFunFvs f = do
  maybe_fvs <- asks (Map.lookup f . funFvs)
  case maybe_fvs of
    Nothing       -> return (f, mempty)
    Just (f', vs) -> return (f', vs)

extendFunFvs :: [(Var, (Var, [Var]))] -> Lift a -> Lift a
extendFunFvs ves m =
    extendEnv funFvs (\env x -> env { funFvs = x }) ves m

withDecl :: Decl -> (Maybe Decl -> Lift a) -> Lift a
withDecl decl k = do
  atTop <- isInTopScope
  if atTop
    then do appendTopDecl decl
            k Nothing
    else k (Just decl)

appendTopDecl :: Decl -> Lift ()
appendTopDecl decl =
    modify $ \s -> s { topdecls = topdecls s |> decl }

getTopDecls :: Lift [Decl]
getTopDecls = gets (toList . topdecls)
