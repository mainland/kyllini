{-# LANGUAGE ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      : Data.Digraph
-- Copyright   : (c) 2007-2009 The President and Fellows of Harvard College
--               (c) 2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

module Data.Digraph (scc) where

import Data.List (foldl')
import Data.Set (Set)
import qualified Data.Set as Set

depthFirstSearch  ::  forall a . Ord a
                  =>  (a -> [a])
                  ->  (Set a, [a])
                  ->  [a]
                  ->  (Set a, [a])
depthFirstSearch = foldl' . search
  where
    search  ::  (a -> [a])
            ->  (Set a, [a])
            ->  a
            ->  (Set a, [a])
    search relation (visited, sequence) vertex
        | vertex `Set.member` visited  = (visited, sequence)
        | otherwise                    = (visited', vertex : sequence')
      where
        (visited', sequence') =
            depthFirstSearch  relation
                              (Set.insert vertex visited, sequence)
                              (relation vertex)

spanningSearch  ::  forall a . Ord a
                =>  (a -> [a])
                ->  (Set a, [Set a])
                ->  [a]
                ->  (Set a, [Set a])
spanningSearch relation = foldl' (search relation)
  where
    search  ::  (a -> [a])
            ->  (Set a, [Set a])
            ->  a
            ->  (Set a, [Set a])
    search relation (visited, setSequence) vertex
        | vertex `Set.member` visited  =  (visited,   setSequence)
        | otherwise                    =  (visited',  setSequence')
      where
        (visited', sequence) =
            depthFirstSearch  relation
                              (Set.insert vertex visited, [])
                              (relation vertex)

        setSequence' = Set.fromList (vertex : sequence) : setSequence

scc  ::  Ord a
     =>  (a -> [a])
     ->  (a -> [a])
     ->  [a]
     ->  [Set a]
scc ins outs = spanning . depthFirst
  where
    depthFirst  = snd . depthFirstSearch  outs  (Set.empty, [])
    spanning    = snd . spanningSearch    ins   (Set.empty, [])
