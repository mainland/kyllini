{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Rate
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.Rate (
    rateProgram,
    rateComp,

    parRate,

    compInOutM,
    compInM,
    compOutM,
    compInP,
    compOutP,
    fromP
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (MonadPlus(..),
                      when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Data.Maybe (fromJust)
import Text.PrettyPrint.Mainland

import KZC.Config
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

{- Note [Rates]

The rate analysis we perform is similar to the cardinality analysis performed by
the original Ziria compiler, but there are significant differences between the
two. In particular, rate analysis is now compositional, not limited to, e.g.,
"simple computers," and we can analyze more computations.

A rate is a pair of multiplicities (to be described below), one for the
computation's input, and one for its output. We write computer rates as $[m,
n]$, where $m$ and $n$ are multiplicities, and we write transformer rates as
$[m, n]^*$.

Multiplicities may be:

  1. A fixed constant, which could be zero, written $n$.
  2. Zero or more blocks of size $n > 1$, written $n^*$.
  2. One or more blocks of size $n > 1$, written $n^+$.

For a computer, a multiplicity describes the read/write behavior of the computer
over its entire execution. For a transformer, a multiplicity describes the
read/write behavior of the transformer for a single round of execution.

A rate of $n$ means that we know the computation will read/write exactly $n$
elements. A rate of $n^*$ means that *if* the computation reads/writes, it will
read/write some multiple of $n$ elements. Note that $1^*$ means that *if* the
computation reads/writes, it will read/write some multiple of $1$ elements,
i.e., it is equivalent to saying we don't know anything about the computation's
read/write behavior. A rate of $n^+$ means that the computation will read/write
some multiple of $n$ elements, i.e., it is a guarantee that some positive
multiple of $n$ elements will be read/written.

Having both $n^*$ and $n^+$ is important, as it lets us infer a useful rate for
examples like the following:

    xs <- take 16;
    emit e1
    while ( some condition ) {
        ys <- take 16
        emit e2
    }

The first part of the computation has rate $[16, 1]$, and the second part of the
computation has a rate $[16^*, 1^*]$, so the overall rate is $[16^+, 1^+]$.

The rules for inferring rates for computers in sequence are fairly
straightforward, although we sometimes need to take the $\gcd$ when combining,
e.g., multiplicities $i$ and $j^+$ to get the multiplicity $\gcd(i, j)^+$.

The rules for inferring rates for a computer in sequence with a transformer are
slightly less obvious because we have to ensure that the computed rate is valid
for *all* transformer rounds.
-}

newtype RateState = RateState { rate :: Rate M }

defaultRState :: RateState
defaultRState = RateState (staticRate 0 0)

newtype RM m a = RM { unRM :: StateT RateState m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState RateState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace,
              MonadTc)

instance MonadTrans RM where
    lift m = RM $ lift m

runRM :: MonadTc m => RM m a -> m a
runRM m = evalStateT (unRM m) defaultRState

plusRate :: MonadTc m => Rate M -> RM m ()
plusRate r = modify $ \s -> s { rate = rate s `rplus` r }

getRate :: MonadTc m => RM m (Rate M)
getRate = gets rate

putRate :: MonadTc m => Rate M -> RM m ()
putRate r = modify $ \s -> s { rate = r }

rateProgram :: (IsLabel l, MonadTc m) => Program l -> m (Program l)
rateProgram = runRM . programT

rateComp :: (IsLabel l, MonadTc m) => Comp l -> m (Comp l)
rateComp = runRM . compT

instance MonadTc m => TransformExp (RM m) where

instance (IsLabel l, MonadTc m) => TransformComp l (RM m) where
    compT comp = do
        r_old <- getRate
        putRate $ staticRate 0 0
        c <- transComp comp
        r <- getRate
        putRate r_old
        return c { compRate = Just r }

    stepT step@VarC{} = do
        unknownRate step
        return step

    stepT step@CallC{} = do
        unknownRate step
        return step

    stepT (IfC l e c1 c2 s) = do
        c1' <- compT c1
        c2' <- compT c2
        plusRate $ compR c1' `rjoin` compR c1'
        return $ IfC l e c1' c2' s

    stepT step@LetC{} =
        return step

    stepT (WhileC l e c s) = do
        c'            <- compT c
        let CompR i j =  compR c'
        plusRate $ CompR (mstar i) (mstar j)
        return $ WhileC l e c' s

    stepT (ForC l ann v tau e1 e2 c s) = do
        c' <- extendVars [(v, tau)] $
              compT c
        plusRate $ expM e2 $ compR c'
        return $ ForC l ann v tau e1 e2 c' s

    stepT step@LiftC{} =
        return step

    stepT step@ReturnC{} =
        return step

    stepT step@BindC{} =
        return step

    stepT step@TakeC{} = do
        plusRate $ staticRate 1 0
        return step

    stepT step@(TakesC _ n _ _) = do
        plusRate $ staticRate n 0
        return step

    stepT step@EmitC{} = do
        plusRate $ staticRate 0 1
        return step

    stepT step@(EmitsC _ e _) = do
        (iota, _) <- inferExp e >>= checkArrT
        plusRate $ CompR (N 0) (iotaM iota)
        return step

    stepT (RepeatC l ann c s) = do
        c' <- compT c
        -- This is a bit of a hack... we know that @repeat c@ will have a rate
        -- that is a multiplicity of the static rate of @c@.
        let CompR i j= compR c'
        plusRate $ TransR i j
        return $ RepeatC l ann c' s

    stepT step@(ParC ann b c1 c2 sloc) =
        withLocContext step (text "In par") $ do
        (s, a, c) <- askSTIndTypes
        c1'       <- localSTIndTypes (Just (s, a, b)) $ compT c1
        c2'       <- localSTIndTypes (Just (b, b, c)) $ compT c2
        -- traceRate $ ppr c1' <+> text ">>>" <+> ppr c2'
        traceRate $ ppr (compR c1') <+> text ">>>" <+> ppr (compR c2')
        r <- parRate (compR c1') (compR c2')
        traceRate $ text "rate:" <+> ppr r
        plusRate r
        return $ ParC ann b c1' c2' sloc

-- | Calculate the rate of a par given the rates of its left and right sides.
parRate :: MonadTc m => Rate M -> Rate M -> m (Rate M)
-- c >>> t
parRate (CompR _ m2) (TransR m3 _) | notPos m2 || notPos m3 =
    return unknownCompRate

parRate (CompR i m2) (TransR m3 l)
  | k == 0         = do warndocWhen WarnRateMismatch $
                          text "Transformer output rate is zero"
                        return unknownCompRate
  | j < k          = do warndocWhen WarnRateMismatch $
                          text "Computer output rate" <+> ppr j <+>
                          text "is less than" <+>
                          text "transformer input rate" <+> ppr k
                        return unknownCompRate
  | j `rem` k /= 0 = do warndocWhen WarnRateMismatch $
                          text "Transformer input rate" <+> ppr k <+>
                          text "does not divide" <+>
                          text "computer output rate" <+> ppr j
                        return unknownCompRate
  | otherwise      = return $ CompR i (n `mtimes` l)
  where
    j, k, n:: Int
    j = (fromJust . fromP) m2
    k = (fromJust . fromP) m3
    n = j `quot` k

-- t >>> c
parRate (TransR _ m2) (CompR m3 _) | notPos m2 || notPos m3 =
    return unknownCompRate

parRate (TransR i m2) (CompR m3 l)
  | j == 0         = do warndocWhen WarnRateMismatch $
                          text "Transformer output rate is zero"
                        return unknownCompRate
  | k < j          = do warndocWhen WarnRateMismatch $
                          text "Computer input rate" <+> ppr k <+>
                          text "is less than" <+>
                          text "transformer output rate" <+> ppr j
                        return unknownCompRate
  | k `rem` j /= 0 = do warndocWhen WarnRateMismatch $
                          text "Transformer output rate" <+> ppr j <+>
                          text "does not divide" <+>
                          text "computer input rate" <+> ppr k
                        return unknownCompRate
  | otherwise      = return $ CompR (n `mtimes` i) l
  where
    j, k, n :: Int
    j = (fromJust . fromP) m2
    k = (fromJust . fromP) m3
    n = k `quot` j

-- t1 >>> t2
parRate (TransR _ m2) (TransR m3 _) | notPos m2 || notPos m3 =
    return unknownTransRate

parRate (TransR i m2) (TransR m3 l)
  | j == 0 || k == 0 = do
    warndocWhen WarnRateMismatch $
      text "Transformer output rate is zero"
    return unknownTransRate

  | otherwise = do
    when (j < k && k `rem` j /= 0) $
      warndocWhen WarnRateMismatch $
        text "Transformer output rate" <+> ppr j <+>
        text "does not divide" <+>
        text "Transformer input rate" <+> ppr k
    when (j > k && j `rem` k /= 0) $
      warndocWhen WarnRateMismatch $
        text "Transformer input rate" <+> ppr k <+>
        text "does not divide" <+>
        text "Transformer output rate" <+> ppr j
    return $ TransR ((n `quot` j) `mtimes` i) ((n `quot` k) `mtimes` l)
  where
    j, k, n :: Int
    j = (fromJust . fromP) m2
    k = (fromJust . fromP) m3
    n = lcm j k

-- c1 >>> c2
parRate CompR{} CompR{} =
    errordoc $ text "Saw two computers in parallel."

-- | Return the in/out multiplicities of a computation.
compInOutM :: forall l m . Monad m => Comp l -> m (M, M)
compInOutM = go . compRate
  where
    go :: Maybe (Rate M) -> m (M, M)
    go Nothing               = fail "compInOutM: computation has no multiplicity"
    go (Just (CompR m1 m2))  = return (m1, m2)
    go (Just (TransR m1 m2)) = return (m1, m2)

-- | Return the input multiplicity of a computation.
compInM :: Monad m => Comp l -> m M
compInM comp = fst <$> compInOutM comp

-- | Return the output multiplicity of a computation.
compOutM :: Monad m => Comp l -> m M
compOutM comp = snd <$> compInOutM comp

-- | Return the input multiplicity of a computation if it is of the form n or
-- n+.
compInP :: MonadPlus m => Comp l -> m Int
compInP comp = compInM comp >>= fromP

-- | Return the output multiplicity of a computation if it is of the form n or
-- n+.
compOutP :: MonadPlus m => Comp l -> m Int
compOutP comp = compOutM comp >>= fromP

-- | Given a positive multiplicity, i.e., a multiplicity of the form n or n+,
-- return n. Otherwise, fail.
fromP :: MonadPlus m => M -> m Int
fromP (N i) = return i
fromP (P i) = return i
fromP Z{}   = mzero

-- | Get a computation's rate when we know it must exist.
compR :: Comp l -> Rate M
compR Comp{ compRate = Just r } = r
compR _                         = error "compR: no rate"

-- | Convert an 'Exp' to an iteration factor
expM :: Exp -> Rate M -> Rate M
expM (ConstE (FixC _ i) _) = rtimes i
expM _                     = rstar

-- | Convert an 'Iota' to a multiplicity.
iotaM :: Iota -> M
iotaM (ConstI n _) = N n
iotaM _            = Z 1

unknownRate :: (IsLabel l, MonadTc m) => Step l -> RM m ()
unknownRate step = do
    tau <- inferStep step
    case tau of
      ST _ C{} _ _ _ _ -> plusRate unknownCompRate
      _                -> plusRate unknownTransRate

unknownCompRate :: Rate M
unknownCompRate = CompR (Z 1) (Z 1)

unknownTransRate :: Rate M
unknownTransRate = TransR (Z 1) (Z 1)

staticRate :: Int -> Int -> Rate M
staticRate i o = CompR (N i) (N o)

-- | Return 'True' if a multiplicity is not stricly positive, i.e., if it may be
-- zero.
notPos :: M -> Bool
notPos Z{} = True
notPos _   = False

-- | Given a multiplicity m, return the multiplicity of a computation with
-- multiplicity m that is repeated 0 or more times.
mstar :: M -> M
mstar (N 0) = N 0
mstar (N i) = Z i
mstar (P i) = Z i
mstar (Z i) = Z i

-- | Return the rate of a computation with the given rate that is repeated 0 or
-- more times.
rstar :: Rate M -> Rate M
rstar (CompR i j) = CompR  (mstar i) (mstar j)
rstar TransR{}    = error "rstar: transformer"

-- | Given a multiplicity m, return the multiplicity of a computation with
-- multiplicity m that is repeated n times.
mtimes :: Int -> M -> M
mtimes 0 _     = N 0
mtimes n (N i) = N (i*n)
mtimes n (P i) = P (i*n)
mtimes _ (Z i) = Z i

-- | Return the rate of a computation with the given rate that is repeated n
-- times.
rtimes :: Int -> Rate M -> Rate M
n `rtimes` CompR i j = CompR  (n `mtimes` i) (n `mtimes` j)
_ `rtimes` TransR{}  = error "rtimes: transformer"

-- | Add rates for computations in sequence.
rplus :: Rate M -> Rate M -> Rate M
CompR i j `rplus` CompR k l  = CompR  (i `cplus` k) (j `cplus` l)
CompR i j `rplus` TransR k l = TransR (i `tplus` k) (j `tplus` l)
TransR{}  `rplus` CompR{}    = error "rplus: transformer before computer"
TransR{}  `rplus` TransR{}   = error "rplus: two transformers in sequence"

-- | Join rates for computations in different control flow branches.
rjoin :: Rate M -> Rate M -> Rate M
CompR i j  `rjoin` CompR k l  = CompR  (i `mjoin` k) (j `mjoin` l)
TransR i j `rjoin` TransR k l = TransR (i `mjoin` k) (j `mjoin` l)
CompR{}    `rjoin` TransR{}   = error "rjoin: computer and transformer"
TransR{}   `rjoin` CompR{}    = error "rjoin: transformer and computer"

-- | Add multiplicities for two computers in sequence
cplus :: M -> M -> M
N 0 `cplus` m   = m
m   `cplus` N 0 = m
N i `cplus` N j = N (i+j)
N i `cplus` P j = P (gcd i j)
N i `cplus` Z j = P (gcd i j)
P i `cplus` N j = P (gcd i j)
P i `cplus` P j = P (gcd i j)
P i `cplus` Z j = P (gcd i j)
Z i `cplus` N j = P (gcd i j)
Z i `cplus` P j = P (gcd i j)
Z i `cplus` Z j = Z (gcd i j)

-- | Add multiplicities for computer followed by transformer in sequence.
tplus :: M -> M -> M
N 0 `tplus` m   = m
_   `tplus` N 0 = Z 1
N i `tplus` N j = P (gcd i j)
N i `tplus` P j = P (gcd i j)
N i `tplus` Z j = Z (gcd i j)
P i `tplus` N j = P (gcd i j)
P i `tplus` P j = P (gcd i j)
P i `tplus` Z j = Z (gcd i j)
Z i `tplus` N j = N (gcd i j)
Z i `tplus` P j = P (gcd i j)
Z i `tplus` Z j = Z (gcd i j)

-- | Join multiplicites for different control flow branches.
mjoin :: M -> M -> M
N i `mjoin` N j
  | i == j      = N i
N 0 `mjoin` _   = Z 1
_   `mjoin` N 0 = Z 1
N i `mjoin` N j = P (gcd i j)
N i `mjoin` P j = P (gcd i j)
N i `mjoin` Z j = Z (gcd i j)
P i `mjoin` N j = P (gcd i j)
P i `mjoin` P j = P (gcd i j)
P i `mjoin` Z j = Z (gcd i j)
Z i `mjoin` N j = Z (gcd i j)
Z i `mjoin` P j = Z (gcd i j)
Z i `mjoin` Z j = Z (gcd i j)
