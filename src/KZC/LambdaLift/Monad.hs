{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.LambdaLift.Monad
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.LambdaLift.Monad (
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
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (mempty)
import Data.Sequence (Seq, (|>))
import Data.Set (Set)
import qualified Data.Set as Set

import KZC.Core.Syntax
import KZC.Lint.Monad
import KZC.Monad

type Lift a = Tc LiftEnv LiftState a

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
runLift m = liftTc defaultLiftEnv defaultLiftState m

extend :: forall k v a . Ord k
       => (LiftEnv -> Map k v)
       -> (LiftEnv -> Map k v -> LiftEnv)
       -> [(k, v)]
       -> Lift a
       -> Lift a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

{-
lookupBy :: Ord k
         => (LiftEnv -> Map k v)
         -> Lift v
         -> k
         -> Lift v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v
-}

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
    extend funFvs (\env x -> env { funFvs = x }) ves m

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
