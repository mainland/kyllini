-- |
-- Module      : Language.Ziria.Parser.Util
-- Copyright   : (c) 2014-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Parser.Util (
    intC,

    constIntExp,

    RevList(..),
    rnil,
    rsingleton,
    rcons,
    rapp,
    rlist,
    rev
  ) where

import Data.Loc
import Text.PrettyPrint.Mainland

import Language.Ziria.Parser.Monad
import Language.Ziria.Syntax

intC :: Int -> SrcLoc -> Exp
intC i l = ConstE (IntC IDefault i) l

constIntExp :: Exp -> P Int
constIntExp e = go e
  where
    go :: Exp -> P Int
    go (ConstE (IntC IDefault i) _) =
        return i

    go (ConstE (IntC I{} i) _) =
        return i

    go (ConstE (IntC UDefault i) _) =
        return i

    go (ConstE (IntC U{} i) _) =
        return i

    go e@(BinopE op e1 e2 _) = do
        x <- go e1
        y <- go e2
        binop op x y
      where
        binop :: Binop -> Int -> Int -> P Int
        binop Add x y = return $ x + y
        binop Sub x y = return $ x - y
        binop Mul x y = return $ x * y
        binop Div x y = return $ x `div` y
        binop _   _ _ = parserError (locOf e) $
                        text "Non-constant integer expression:" <+> ppr e

    go e =
        parserError (locOf e) $
        text "Non-constant integer expression:" <+> ppr e

data RevList a  =  RNil
                |  RCons a (RevList a)
                |  RApp [a] (RevList a)

rnil :: RevList a
rnil = RNil

rsingleton :: a -> RevList a
rsingleton x = RCons x RNil

infixr 5 `rcons`

rcons :: a -> RevList a -> RevList a
rcons x xs  = RCons x xs

rapp :: [a] -> RevList a -> RevList a
rapp xs ys  = RApp xs ys

rlist :: [a] -> RevList a
rlist xs = rlist' xs rnil
  where
    rlist' []     acc = acc
    rlist' (x:xs) acc = rlist' xs (rcons x acc)

rev :: RevList a -> [a]
rev xs = go [] xs
  where
    go  l  RNil          = l
    go  l  (RCons x xs)  = go (x : l) xs
    go  l  (RApp xs ys)  = go (xs ++ l) ys

instance Located a => Located (RevList a) where
    locOf RNil         = mempty
    locOf (RCons x xs) = locOf x `mappend` locOf xs
    locOf (RApp xs ys) = locOf xs `mappend` locOf ys
