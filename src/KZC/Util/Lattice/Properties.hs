-- |
-- Module      :  KZC.Util.Lattice.Properties
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Util.Lattice.Properties where

import Prelude hiding ((<=))

import KZC.Util.Lattice

import Test.QuickCheck

prop_poset_reflexivity :: Poset a => a -> Bool
prop_poset_reflexivity x = x <= x

prop_poset_antisymmetry :: Poset a => a -> a -> Property
prop_poset_antisymmetry x y = x <= y && y <= x ==> x == y

prop_poset_transitivity :: Poset a => a -> a -> a -> Property
prop_poset_transitivity x y z = x <= y && y <= z ==> x <= z

prop_lub :: Lattice a => a -> a -> a -> Property
prop_lub x y z = x <= z && y <= z ==> lub x y <= z

prop_glb :: Lattice a => a -> a -> a -> Property
prop_glb x y z = x <= y && x <= z ==> x <= glb y z

prop_top :: BoundedLattice a => a -> Bool
prop_top x = x <= top

prop_bot :: BoundedLattice a => a -> Bool
prop_bot x = bot <= x
