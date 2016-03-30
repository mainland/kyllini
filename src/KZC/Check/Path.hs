{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      :  KZC.Check.Path
Copyright   :  (c) 2016 Drexel University
License     :  BSD-style
Maintainer  :  mainland@cs.drexel.edu

Provides generic support for checking for aliasing between references.
-}

module KZC.Check.Path (
    RefPath(..),
    Path(..),

    checkNoPathAliasing
  ) where

import Control.Monad (when)
import Data.List (tails)
import Text.PrettyPrint.Mainland

data RefPath v f = RefP v [Path f]
  deriving (Eq, Ord, Show)

data Path f = IdxP Int Int
            | ProjP f
  deriving (Eq, Ord, Show)

instance (Pretty v, Pretty f) => Pretty (RefPath v f) where
    ppr (RefP v p) = ppr v <> pprPath p
      where
        pprPath :: [Path f] -> Doc
        pprPath []           = Text.PrettyPrint.Mainland.empty
        pprPath (IdxP i 1:p) = brackets (ppr i) <> pprPath p
        pprPath (IdxP i l:p) = brackets (commasep [ppr i, ppr l]) <> pprPath p
        pprPath (ProjP f:p)  = char '.' <> ppr f <> pprPath p

checkNoPathAliasing :: forall v f m . (Eq v, Eq f, Pretty v, Pretty f, Monad m)
                    => [RefPath v f]
                    -> m ()
checkNoPathAliasing rpaths =
    when (not (null overlapping)) $
        faildoc $ nest 4 $
        text "Aliasing between arguments:" </>
        stack (map pprOverlapping overlapping)
  where
    overlapping :: [(RefPath v f, RefPath v f)]
    overlapping = [(rp1, rp2) | (rp1, rp2) <- pairs rpaths, overlap rp1 rp2]

    overlap :: RefPath v f -> RefPath v f -> Bool
    overlap rp1@(RefP v1 p1) rp2@(RefP v2 p2) =
        v1 == v2 && not (disjoint p1 p2)
      where
        disjoint :: [Path f] -> [Path f] -> Bool
        disjoint [] [] =
            False

        disjoint [_] [] =
            False

        disjoint [] [_] =
            False

        disjoint (IdxP i l : p1) (IdxP j m : p2) =
            not (i < j+m && j < i+l) || disjoint p1 p2

        disjoint (ProjP f1 : p1) (ProjP f2 : p2) =
            f1 /= f2 || disjoint p1 p2

        disjoint _ _ =
            errordoc $ nest 2 $
            text "checkNoPathAliasing: illegal paths:" </> ppr rp1 </> ppr rp2

    pairs :: [a] -> [(a,a)]
    pairs l = [(x,y) | (x:xs) <- tails l, y <- xs]

    pprOverlapping :: (RefPath v f, RefPath v f) -> Doc
    pprOverlapping (rp1, rp2) =
        ppr rp2 <+> text "aliases earlier argument" <+> ppr rp1
