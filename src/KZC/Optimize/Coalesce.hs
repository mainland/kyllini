{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Coalesce
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.Coalesce (
    coalesceProgram
  ) where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus(..),
                      guard)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.Logic (MonadLogic(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Data.Function (on)
import Data.List (sort, sortBy)
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Rate
import KZC.Config
import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Fuel
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Pretty
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq

data CoEnv = CoEnv { leftCtx  :: !(Rate M)
                   , rightCtx :: !(Rate M)
                   }

defaultCoEnv :: CoEnv
defaultCoEnv = CoEnv simpleTrans simpleTrans
  where
    simpleTrans :: Rate M
    simpleTrans = TransR (N 1) (N 1)

newtype Co m a = Co { unCo :: ReaderT CoEnv (SEFKT m) a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadIO,
            MonadReader CoEnv,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadFuel,
            MonadPlatform,
            MonadTrace,
            MonadTc,
            MonadLogic)

runCo :: forall m a . MonadErr m
      => Co m a
      -> m a
runCo m = runSEFKT (runReaderT (unCo m) defaultCoEnv)

withLeftCtx :: MonadTc m => Maybe (Rate M) -> Co m a -> Co m a
withLeftCtx Nothing m =
    local (\env -> env { leftCtx = CompR (Z 1) (Z 1) }) m

withLeftCtx (Just r2) m = do
    r1 <- asks leftCtx
    r  <- parRate r1 r2
    local (\env -> env { leftCtx = r }) m

withRightCtx :: MonadTc m => Maybe (Rate M) -> Co m a -> Co m a
withRightCtx Nothing _ =
    errordoc $ text "withRightCtx: unknown computation rate"

withRightCtx (Just r1) m = do
    r2 <- asks rightCtx
    r  <- parRate r1 r2
    local (\env -> env { rightCtx = r }) m

askLeftCtx :: MonadTc m => Co m (Maybe M)
askLeftCtx = do
    r <- asks leftCtx
    case r of
      r@CompR{} -> return $ Just $ outMult r
      _         -> return Nothing

askRightCtx :: MonadTc m => Co m (Maybe M)
askRightCtx = do
    r <- asks rightCtx
    case r of
      r@CompR{} -> return $ Just $ inMult r
      _         -> return Nothing

coalesceProgram :: forall l m . (IsLabel l, MonadIO m, MonadTc m)
                => Program l -> m (Program l)
coalesceProgram = runCo . programT

{- Note [Pipeline Coalescing]

Pipeline coalescing attempts to do two things:

  1. Coalesce computation input/output into single blocks so that `take`s and
  `emit`s spread throughout a computation turn into a single `takes` and a
  single `emits`. This opens up opportunities for, e.g., LUTting, which can only
  LUT expressions.

  2. Process data in larger chunks. This effectively involves running the body
  of the computation multiple times, a transformation that is only valid for
  transformers, not computers.

Coalescing relies on inserting variants of two transformers, coLeft(tau,n) and
coRight(tau,n), into the pipeline to the left and right (resp.) of the
computation being transformed; we then rely on fusion to optimize the
transformed pipeline.

The transformer coLeft(tau,n) is:

    repeat { xs <- takes n; emit xs[0]; ...; emit xs[n-1]; }

coLeft(tau,n) is inserted to the left of a computation. It takes
arrays of input and parcels them out element-by-element.

The transformer coRight(tau,n) is:

    letref xs : arr[n] tau in
    repeat { x <- take; xs[0] := x; ...; x <- take; xs[n-1] := x; emits xs }

coRight(tau,n) is inserted to the right of a computation. It takes its input one
element at a time and outputs whole arrays.

The goal behind pipeline coalescing is to line up producers and consumers so
that they emit and take (resp.) (array-size) blocks of the same size.

We write $i \to j$ for a computer/transformer that takes input in chunks of size
$i$ and produce outputs in chunks of size $j$. Note that the value $i$
corresponds to a rate of *either* $i$ or $i^+$. When coalescing, we focus on the
granularity at which reads/writes occur, not on the total number of
reads/writes. Our eventual goal is to coalesce input/output into blocks. We will
write $i^n$ for input/output that is grouped into $n$ **blocks**, each of size
$i$

Note that $i^n$ corresponds to a multiplicity of either $i^n$ or ${i^n}^+$. In
particular, it is always safe to assign $i^n$ a multiplicity of ${i^n}^+$.

## C-rules

It is always valid to coalesce input/output according to the following rules,
which we call coalescing rules, or C-rules, where we write $X$ to stand for any
multiplicity:

\[
\begin{alignat*}{5}
i*j &&\to &X    &\leadsto  i^j &\to &X   &&\quad \textrm{C-Left} \\
X   &&\to &k*l  &\leadsto  X   &\to &k^l &&\quad \textrm{C-Right}
\end{alignat*}
\]

Here, $i^j$ to the left of an arrow corresponds to inserting coLeft(tau,i) to
the left of a computation, and $k^l$ corresponds to insertingcoRight(tau,k) to
the right of a computation. The C rules do not change the multiplicity of a
computation; they only reorganize the way input/output is performed by inserting
buffers.

## B-rules

For transformers, we might also like to batch input and/or output into groups
that are *larger* than the transformer's multiplicity, thereby taking or
emitting multiple transformer rounds worth of data at a time. We can batch on
the right or the left, or we can perform both transformations. This leads to the
B rules, where we write $X$ and $Y$ to stand for any multiplicity:

\[
\begin{alignat*}{7}
  i &&\to &X &&\leadsto  {(i * n_1)}^{n_2} &\to &X*n_1*n_2
      &
      &&\quad \textrm{B-Left} \\
  X &&\to &j &&\leadsto  X*n_1*n_2 &\to &{(j*n_1)}^{n_2}
      &
      &&\quad \textrm{B-Right} \\
  i &&\to &j &&\leadsto  {(i*n_1)}^{n_2} &\to &{(j*n'_1)}^{n'_2}
      &\quad \small{\textrm{$n_1 n_2 = n_1' n_2'$, and $\gcd(n_2,n_2') = 1$}}
      &&\quad \textrm{B-Both}
\end{alignat*}
\]

Unlike the C rules, the B-rules are not always valid. In particular, we cannot
batch a transformer that is run in series with a computer in a manner that
causes the transformer to consume/produce blocks that might be larger that what
its upstream/downstream (resp.) computer requires for termination.

Why is this a problem? A tranformer that consumes blocks that are larger than
needed to absorb the output of an upstream producer causes the pipeline to
under-produce since the computer may terminate before outputting a block. A
transformer that produces blocks that are larger than needed to satisfy a
downstream consumer causes the pipeline to over-consume since the transformer
may read more data than is strictly necessary to allow the downstream consumer
to successfully terminate. Both situations illegally change the semantics of the
program.

How do we avoid over-consumption or under-production? We have to ensure that the
block size is less than the multiplicity of the constraining computation.
Consider a transformer whose downstream computer has input multiplicity $m$ or
$m^+$. In this case, then we can only apply the B-Right rule when $j*n_1 \mid
m$. Similarly, if a transformer's upstream computer has output multiplicity $m$,
then we can only apply the B-Left rule when $i*n_2 \mid m$. Application of the
B-Both rule is subject to analogous restrictions. Finally, when the surrounding
computer has multiplicity $m^*$, we may not buffer read/writes into blocks at
all.

Note that the B rules *do* change the rate of a computation by a factor of
$n_1*n_2$.

The B rules allow us to obtain (potentially) different block sizes by running a
computation multiple times. This may allow us to match the block size of an
upstream/downstream computation, potentially leading to elimination of buffers.
What we really care about is the block size. Consider the B Both rule; we could
always allow $n_2$ and $n_2'$ to be multiplied by a common factor $k$, but this
would in effect just mean that we force the computation to run for a factor of
$k$ more rounds. Running a computation for extra rounds is only useful if it
allows us to block input/output differently, thus the restriction that
$\gcd(n_2,n_2') = 1$ in the B-Both rule.

## In Practice

The implementation makes some simplifying choices:

 1. We only choose blockings of the form $i^1$.

 2. B-rules require that we know both the input and output multiplicity of the
 computation. If the multiplicity is known, then we can probably fuse with the
 blocking coercion. Otherwise we are likely to just end up with a bunch of
 copies.

 3. When coalescing a producer and a consumer, we make the producer emit a
 single array and the consumer consume a single array (emit/take), rather than
 using emits/takes. This makes them easy to fuse together.
-}

-- | Input/output blocking, of the form $i^j$, i.e., $j$ blocks, each of size
-- $i$.
data B = B !Int !Int
  deriving (Eq, Ord, Show)

instance Pretty B where
    ppr (B i j) = ppr i <> char '^' <> ppr j

-- | Blocking candidate for a computation. Has the form $i^j \to k^l$.
data BC = BC { inBlock  :: Maybe B -- Input blocking
             , outBlock :: Maybe B -- Output blocking
             , rateMult :: !Int    -- Rate multiplier
             , inBits   :: !Int    -- Bit size of each input element
             , outBits  :: !Int    -- Bit size of each output element
             }
  deriving (Eq, Ord, Show)

instance Pretty BC where
  ppr bc =
      pprV (inBlock bc) <+> text "->" <+> pprV (outBlock bc)
    where
      pprV Nothing  = char '_'
      pprV (Just v) = ppr v

instance MonadTc m => TransformExp (Co m) where

instance (IsLabel l, MonadTc m) => TransformComp l (Co m) where
    mainT (Main comp tau) =
        inSTScope tau $
        inLocalScope $
        withLocContext comp (text "In definition of main") $ do
        traceCoalesce $ text "Top rate:" <+> ppr (compRate comp)
        (_s, a, b) <- askSTIndices
        comp'      <- compT comp
        flags      <- askConfig
        if testDynFlag CoalesceTop flags
          then do
            bcs <- coalesceTopComp comp'
            whenVerb $ traceCoalesce $ nest 2 $
              text "Top-level candidates:" </> stack (map ppr (sort bcs))
            comp'' <- case sortAscendingBy topMetric bcs of
                       bc:_ -> applyTopBlocking bc a b comp'
                       _    -> return comp'
            return $ Main comp'' tau
          else return $ Main comp' tau
        where
          applyTopBlocking :: BC
                           -> Type
                           -> Type
                           -> Comp l
                           -> Co m (Comp l)
          applyTopBlocking bc a b comp = do
              traceCoalesce $
               text "      Chose vectorization:" <+> ppr bc </>
               text "For top-level computation:" <+> ppr (compRate comp)
              comp' <- runK $ applyBlocking Top bc a b comp
              whenVerb $ traceCoalesce $ nest 2 $
                text "Coalesced top-level:" </> ppr comp'
              rateComp comp'

    compT c = transComp c >>= rateComp

    stepT step0@(ParC ann b c1 c2 sloc) = withSummaryContext step0 $ do
        (s, a, c) <- askSTIndices
        -- Why can we use c1 and c2 instead of c1' and c1' when calling
        -- withRightCtx and withLeftCtx? The only time the context will limit
        -- our choices is when it is a computer, in which case both the original
        -- and coalesced computations will have the same rate.
        traceCoalesce $ nest 2 $
          text "Producer:" <+> ppr (compRate c1) <+> text "::" <+> pprST a b </>
          ppr c1
        (c1', bcs1) <- localSTIndices (Just (s, a, b)) $
                       withRightCtx (compRate c2) $ do
                       c1'  <- compT c1
                       bcs1 <- coalesceComp c1'
                       return (c1', bcs1)
        traceCoalesce $ nest 2 $
          text "Consumer:" <+> ppr (compRate c2) <+> text "::" <+> pprST b c </>
          ppr c2
        (c2', bcs2) <- localSTIndices (Just (b, b, c)) $
                       withLeftCtx (compRate c1) $ do
                       c2'  <- compT c2
                       bcs2 <- coalesceComp c2'
                       return (c2', bcs2)
        whenVerb $ traceCoalesce $ nest 2 $
          text "Producer candidates:" </> stack (map ppr (sort bcs1))
        whenVerb $ traceCoalesce $ nest 2 $
          text "Consumer candidates:" </> stack (map ppr (sort bcs2))
        step' <- case sortAscendingBy patMetric [(bc1, bc2) | bc1 <- bcs1, bc2 <- bcs2] of
                   (bc1, bc2):_ -> applyParBlocking a b c bc1 c1' bc2 c2'
                   _            -> return $ ParC ann b c1' c2' sloc
        traceCoalesce $ nest 2 $
          text "Final coalesced par:" </> ppr step'
        return step'
      where
        applyParBlocking :: Type          -- ^ Input type
                         -> Type          -- ^ Intermediate type
                         -> Type          -- ^ Output type
                         -> BC            -- ^ Blocking for left side of par
                         -> Comp l        -- ^ Left side of par
                         -> BC            -- ^ Blocking for right side of par
                         -> Comp l        -- ^ Right side of par
                         -> Co m (Step l) -- ^ Coalesced par
        applyParBlocking a b c bc1 c1 bc2 c2 = do
            traceCoalesce $ nest 2 $
              text "Chose vectorization:" <+> ppr bc1 <+> text ">>>" <+> ppr bc2 </>
              text "            For par:" <+> ppr (compRate c1) <+> text ">>>" <+> ppr (compRate c2)
            parc <- runK $ coalescePar ann a b c c1 c2 bc1 bc2
            traceCoalesce $ nest 2 $
              text "Coalesced par:" </> ppr parc
            head . unComp <$> rateComp parc

        pprST :: Type -> Type -> Doc
        pprST a b = text "ST" <+> pprPrec appPrec1 a <+> pprPrec appPrec1 b

    stepT step = transStep step

sortAscendingBy :: Ord b => (a -> b) -> [a] -> [a]
sortAscendingBy f = sortBy (flip compare `on` f)

data BlockMetric = BlockMetric !Int -- ^ 1 if byte-sized, 0 otherwise
                               !Int -- ^ Negated block count
                               !Int -- ^ Negated block size
  deriving (Eq, Ord, Show)

instance Pretty BlockMetric where
    ppr (BlockMetric x y z) = ppr (x, y, z)

instance Metric BlockMetric where
    BlockMetric s t u .+. BlockMetric x y z = BlockMetric (s+x) (t+y) (u+z)

blockingUtil :: BC -> BlockMetric
blockingUtil BC { inBlock = ablock, outBlock = bblock, inBits = inBits, outBits = outBits } =
    metric inBits ablock .+. metric outBits bblock
  where
    metric :: Int -> Maybe B -> BlockMetric
    metric _ Nothing =
        BlockMetric 0 0 0

    metric sz (Just (B i j)) =
        BlockMetric (if i*sz `rem` 8 == 0 then 1 else 0)
                    (-fromIntegral (i*(j-1)))
                    (-fromIntegral i)

class Ord a => Metric a where
    infixl 6  .+.

    (.+.) :: a -> a -> a

data ParMetric = ParMetric !BlockMetric -- ^ Block utilities
                           !Int         -- ^ 1 if block sizes match, 0 otherwise
                           !Int         -- ^ Negated size of necessary rate matcher
  deriving (Eq, Ord, Show)

instance Pretty ParMetric where
    ppr (ParMetric x y z) = ppr (x, y, z)

patMetric :: (BC, BC) -> ParMetric
patMetric (bc1, bc2) =
    go (outBlock bc1) (inBlock bc2)
  where
    go :: Maybe B -> Maybe B -> ParMetric
    go (Just (B i _j)) (Just (B k _l)) =
        ParMetric (blockingUtil bc1 .+. blockingUtil bc2)
                  (if i == k then 1 else 0)
                  (if i == k then 0 else -fromIntegral (lcm i k))

    go _ _ =
        ParMetric (blockingUtil bc1 .+. blockingUtil bc2) 0 0

topMetric :: BC -> Int
topMetric BC { inBlock  = Just (B i _)
             , outBlock = Just (B j _)
             , inBits   = inBits
             , outBits  = outBits
             } =
    i*(if i*inBits `rem` 8 == 0 then 8 else 1) +
    j*(if j*outBits `rem` 8 == 0 then 8 else 1)

topMetric _ = 0

-- | Coalesce the two sides of a par construct.
coalescePar :: forall l m . (IsLabel l, MonadTc m)
            => PipelineAnn -- ^ Pipeline annotation
            -> Type        -- ^ Input type
            -> Type        -- ^ Intemediate type
            -> Type        -- ^ Output type
            -> Comp l      -- ^ Left side of par
            -> Comp l      -- ^ Right side of par
            -> BC          -- ^ Left blocking
            -> BC          -- ^ Right blocking
            -> K l m Exp   -- ^ Coalesced par
coalescePar ann a b c comp1 comp2 bc1@BC{outBlock=Just (B i _)} bc2@BC{inBlock=Just (B j _)}
  | i == j    = matchedRates
  | otherwise = mismatchedRates
  where
    matchedRates :: K l m Exp
    matchedRates =
        parC' ann
              (coArrT i b)
              (applyBlocking Producer bc1 a b comp1)
              (applyBlocking Consumer bc2 b c comp2)

    mismatchedRates :: K l m Exp
    mismatchedRates =
        parC' ann (coArrT j b)
              (parC (coArrT i b)
                    (applyBlocking Producer bc1 a b comp1)
                    matcher)
              (applyBlocking Consumer bc2 b c comp2)
      where
        n :: Int
        n = lcm i j

        matcher :: K l m Exp
        matcher
          -- Decrease rate for consumer
          | i == n =
            repeatC $ do
            xs <- takeC (coArrT n b)
            forC 0 (n `quot` j) $ \k ->
               if j == 1
                 then emitC (idxE xs (k*fromIntegral j))
                 else emitC (coSliceE xs (k*fromIntegral j) (fromIntegral j))

          -- Increase rate for consumer
          | j == n =
            repeatC $
            letrefC "xs_upconsumer" (coArrT n b) $ \xs -> do
              forC 0 (n `quot` i) $ \k -> do
                ys <- takeC (coArrT i b)
                liftC $ assignE (coSliceE xs (k*fromIntegral i) (fromIntegral i)) ys
              ys <- liftC $ derefE xs
              emitC ys

          -- Increase both rates up to n
          | otherwise =
            repeatC $
            letrefC "xs_upboth" (coArrT n b) $ \xs -> do
              forC 0 (n `quot` i) $ \k -> do
                ys <- takeC (coArrT i b)
                liftC $ assignE (coSliceE xs (k*fromIntegral i) (fromIntegral i)) ys
              forC 0 (n `quot` j) $ \k -> do
                ys <- liftC $ derefE xs
                emitC (coSliceE ys (k*fromIntegral j) (fromIntegral j))

coalescePar ann a b c comp1 comp2 bc1 bc2 =
    parC' ann b (applyBlocking Top bc1 a b comp1)
                (applyBlocking Top bc2 b c comp2)

-- The type of the block of n elements we pass between computers. When n =
-- 1, we use elements rather than arrays of size 1.
coArrT :: Int -> Type -> Type
coArrT 1 tau = tau
coArrT n tau = arrKnownT n tau

-- Extract an array slice. If the slice is only 1 element in length, just return
-- the element itself.
coSliceE :: Exp -> Exp -> Int -> Exp
coSliceE e1 e2 1   = idxE e1 e2
coSliceE e1 e2 len = sliceE e1 e2 len

-- | Whether the current computation is top-level, a producer, or a consumer.
data Mode = Top      -- ^ Computation is top-level
          | Producer -- ^ Computation is a producer
          | Consumer -- ^ Computation is a consume
  deriving (Eq, Ord, Show)

-- | Apply a blocking to a computation.
applyBlocking :: forall l m . (IsLabel l, MonadTc m)
              => Mode      -- ^ Computation mode
              -> BC        -- ^ Blocking
              -> Type      -- ^ Input type
              -> Type      -- ^ Output type
              -> Comp l    -- ^ The computation to which we apply the blocking
              -> K l m Exp -- ^ Resulting computation
applyBlocking mode bc a b comp =
    go bc
  where
    go :: BC -> K l m Exp
    go BC{inBlock = Just (B i _j), outBlock = Just (B k _l)} =
        -- Associate to the right
        -- coleft mode i a (coright mode k b (compC comp))
        -- Associate to the left
        coRight k b (coLeft i a (compC comp))

    go BC{inBlock = Just (B i _j), outBlock = Nothing} =
        coLeft i a (compC comp)

    go BC{inBlock = Nothing, outBlock = Just (B k _l)} =
        coRight k b (compC comp)

    go _ =
        compC comp

    -- | Create a coercion that buffers on the left. If we are the consumer half of
    -- a par, take the entire buffer as an array using @take@ rather than taking it
    -- an element at a time using @takes@.
    coLeft :: Int       -- ^ Number of elements to take per round
           -> Type      -- ^ Type of elements
           -> K l m Exp -- ^ Right side of par
           -> K l m Exp
    coLeft n tau comp =
        parC tau (co mode n tau) comp
      where
        -- | The coercion computation
        co :: Mode -> Int -> Type -> K l m Exp
        co _ 1 tau =
            identityC 1 $
            repeatC $ do
              x <- takeC tau
              emitC x

        -- We are the consumer half of a par, so take an entire array of values at
        -- once.
        co Consumer n tau =
            repeatC $ do
              xs <- takeC (coArrT n tau)
              emitsC xs

        co _ n tau =
            identityC n $
            repeatC $ do
              xs <- takesC n tau
              emitsC xs

    -- | Create a coercion that buffers on the right. If we are the producer half of
    -- a par, emit the entire buffer using @emit@ rather than emitting it an element
    -- at a time using @emits@.
    coRight :: Int       -- ^ Number of elements to emit per round
            -> Type      -- ^ Type of elements
            -> K l m Exp -- ^ Left side of par
            -> K l m Exp
    coRight n tau comp =
        parC tau comp (co mode n tau)
      where
        -- | The coercion computation
        co :: Mode -> Int -> Type -> K l m Exp
        co _ 1 tau =
            identityC 1 $
            repeatC $ do
              x <- takeC tau
              emitC x

        -- We are the producer half of a par, so emit an entire array of values at
        -- once.
        co Producer n tau =
            repeatC $ do
              xs <- takesC n tau
              emitC xs

        co _ n tau =
            identityC n $
            repeatC $ do
              xs <- takesC n tau
              emitsC xs

-- | Generate candidate blockings for a top-level computation.
coalesceTopComp :: forall l m . MonadTc m
                => Comp l
                -> Co m [BC]
coalesceTopComp comp = do
    (_, a, b) <- askSTIndices
    inBits    <- typeSize a
    outBits   <- typeSize b
    maxBuf    <- asksConfig maxCoalesceBuffer
    maxRate   <- asksConfig maxTopCoalesceRate
    -- Evaluate Nat's in the vectorization annotation
    ann <- traverse (traverse evalNat) (vectAnn comp)
    traceCoalesce $ text "Vectorization annotation:" <+>
      ppr ann <+> parens (ppr (vectAnn comp))
    -- Compute C and B rules
    let cs = crules comp inBits outBits maxBuf
    let bs = brules comp inBits outBits maxRate
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "C-rules:" </> stack (map ppr (sort cs))
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "B-rules:" </> stack (map ppr (sort bs))
    dflags <- askConfig
    let allCs :: [BC]
        allCs = filter (byteSizePred dflags) $
                filter (vectAnnPred dflags ann) $
                map (dontCoalesceBits a b) $
                cs ++ bs
    return $ noVect inBits outBits : allCs
  where
    -- | Implement the C rules.
    crules :: Comp l -- ^ The computation
           -> Int    -- ^ Size (in bits) of input type
           -> Int    -- ^ Size (in bits) of output type
           -> Int    -- ^ Maximum buffer size in bits
           -> [BC]
    crules comp inBits outBits maxBuf = do
        (inMult, outMult) <- compInOutM comp
        inBlock           <- crule inMult  (8*maxBuf `quot` inBits)
        outBlock          <- crule outMult (8*maxBuf `quot` outBits)
        return BC { inBlock  = inBlock
                  , outBlock = outBlock
                  , rateMult = 1
                  , inBits   = inBits
                  , outBits  = outBits
                  }
      where
        crule :: M         -- ^ Multiplicity
              -> Int       -- ^ Maximum number of elements
              -> [Maybe B] -- ^ Blocking
        -- We only coalesce one side of a computation if it has a known
        -- multiplicity of i or i+, where i > 0.
        crule m maxElems =
            case toCount m of
              Just i | i > 0 -> [Just (B i 1) | i <= maxElems]
              _              -> [Nothing]

    -- | Implement the B rules
    brules :: Comp l    -- ^ The computation
           -> Int       -- ^ Size (in bits) of input type
           -> Int       -- ^ Size (in bits) of output type
           -> Maybe Int -- ^ Maximum number of elements we may buffer
           -> [BC]
    brules comp inBits outBits maxElems = do
        -- We only rate-expand transformers
        guard (isTransformer comp)
        -- We only rate-expand when we have known input and output rates.
        (inMult, outMult) <- compInOutM comp
        inRate <- toCount inMult
        guard (inRate > 0)
        outRate <- toCount outMult
        guard (outRate > 0)
        -- Compute limits on rate multipliers. We can only multiply a rate up to
        -- the point where we input/output 'maxElems' elements.
        let xMax =  min (multiplierBound maxElems inBits inRate)
                        (multiplierBound maxElems outBits outRate)
        x        <- [1..xMax]
        -- Compute blockings
        inBlock  <- brule inRate  x
        outBlock <- brule outRate x
        -- A batch of the form i^j -> k^l is only allowed if j and l DO NOT have
        -- common factors, i.e., they must be coprime.
        guard (bfCoprime inBlock outBlock)
        return BC { inBlock  = Just inBlock
                  , outBlock = Just outBlock
                  , rateMult = x
                  , inBits   = inBits
                  , outBits  = outBits
                  }
      where
        -- | Upper bound on rate multiplier. We adhere to the 'maxElems' bound
        -- except when we need to multiply the rate to reach a byte boundary.
        multiplierBound :: Maybe Int -> Int -> Int -> Int
        multiplierBound maxElems bits n =
            max minRateXForBytes maxRateX
          where
            -- Min rate multiplier needed to reach a bit boundary.
            minRateXForBytes :: Int
            minRateXForBytes = lcm 8 (n*bits) `quot` (8*bits*n)

            -- Max rate multiplier. We use 'maxElems' to calculate this.
            maxRateX :: Int
            maxRateX = fromMaybe 1 $ do
                k <- maxElems
                return $ k `quot` n

        -- | Return 'True' if blocking factors are coprime, 'False' otherwise.
        bfCoprime :: B -> B -> Bool
        bfCoprime (B _ n) (B _ m) = gcd n m == 1

        brule :: Int -- ^ Our rate
              -> Int -- ^ Rate multiplier factor
              -> [B]
        -- We want to bail on batching one side of a computation if it doesn't
        -- have a known multiplicity of i or i+, where i > 0.
        brule n x
          | n > 0     = [B (x*n) 1]
          | otherwise = []

-- | Generate candidate blockings for a computation.
coalesceComp :: forall l m . MonadTc m
             => Comp l
             -> Co m [BC]
coalesceComp comp = do
    (_, a, b) <- askSTIndices
    inBits    <- typeSize a
    outBits   <- typeSize b
    leftCtx   <- askLeftCtx
    rightCtx  <- askRightCtx
    maxBuf    <- asksConfig maxCoalesceBuffer
    maxRate   <- asksConfig maxCoalesceRate
    traceCoalesce $ text "Left context:" <+> ppr leftCtx
    traceCoalesce $ text "Right context:" <+> ppr rightCtx
    -- Evaluate Nat's in the vectorization annotation
    ann <- traverse (traverse evalNat) (vectAnn comp)
    traceCoalesce $ text "Vectorization annotation:" <+>
      ppr ann <+> parens (ppr (vectAnn comp))
    -- Compute C and B rules
    let cs = crules comp inBits outBits maxBuf
    let bs = brules comp inBits outBits leftCtx rightCtx maxRate
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "C-rules:" </> stack (map ppr (sort cs))
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "B-rules:" </> stack (map ppr (sort bs))
    dflags <- askConfig
    let allCs :: [BC]
        allCs = filter (byteSizePred dflags) $
                filter (vectAnnPred dflags ann) $
                map (dontCoalesceBits a b) $
                cs ++ bs
    return $ noVect inBits outBits : allCs
  where
    -- | Implement the C rules.
    crules :: Comp l -- ^ The computation
           -> Int    -- ^ Size (in bits) of input type
           -> Int    -- ^ Size (in bits) of output type
           -> Int    -- ^ Maximum buffer size in bits
           -> [BC]
    crules comp inBits outBits maxBuf = do
        (inMult, outMult) <- compInOutM comp
        inBlock           <- crule inMult  (8*maxBuf `quot` inBits)
        outBlock          <- crule outMult (8*maxBuf `quot` outBits)
        return BC { inBlock  = inBlock
                  , outBlock = outBlock
                  , rateMult = 1
                  , inBits   = inBits
                  , outBits  = outBits
                  }
      where
        crule :: M         -- ^ Multiplicity
              -> Int       -- ^ Maximum number of elements
              -> [Maybe B] -- ^ Blocking
        -- We only coalesce one side of a computation if it has a known
        -- multiplicity of i or i+, where i > 0.
        crule m maxElems =
            case toCount m of
              Just i | i > 0 -> [Just (B i 1) | i <= maxElems]
              _              -> [Nothing]

    -- | Implement the B rules
    brules :: Comp l    -- ^ The computation
           -> Int       -- ^ Size (in bits) of input type
           -> Int       -- ^ Size (in bits) of output type
           -> Maybe M   -- ^ Left computer's rate
           -> Maybe M   -- ^ Right computer's rate
           -> Maybe Int -- ^ Maximum number of elements we may buffer
           -> [BC]
    brules comp inBits outBits leftCtx rightCtx maxElems = do
        -- We only rate-expand transformers
        guard (isTransformer comp)
        -- We only rate-expand when we have known input and output rates.
        (inMult, outMult) <- compInOutM comp
        inRate <- toCount inMult
        guard (inRate > 0)
        outRate <- toCount outMult
        guard (outRate > 0)
        -- Compute limits on rate multipliers. We can only multiply a rate up to
        -- the point where we input/output 'maxElems' elements.
        let xMax =  min (multiplierBound maxElems inRate)
                        (multiplierBound maxElems outRate)
        x        <- [1..xMax]
        -- Compute blockings
        inBlock  <- brule leftCtx  inRate  x
        outBlock <- brule rightCtx outRate x
        -- A batch of the form i^j -> k^l is only allowed if j and l DO NOT have
        -- common factors, i.e., they must be coprime.
        guard (bfCoprime inBlock outBlock)
        return BC { inBlock  = Just inBlock
                  , outBlock = Just outBlock
                  , rateMult = x
                  , inBits   = inBits
                  , outBits  = outBits
                  }
      where
        -- | Upper bound on rate multiplier.
        multiplierBound :: Maybe Int -> Int -> Int
        multiplierBound maxElems n = fromMaybe 1 $ do
            k <- maxElems
            return $ k `quot` n

        -- | Return 'True' if blocking factors are coprime, 'False' otherwise.
        bfCoprime :: B -> B -> Bool
        bfCoprime (B _ n) (B _ m) = gcd n m == 1

        brule :: Maybe M -- ^ If we are in the context of a computer, its rate
              -> Int     -- ^ Our rate
              -> Int     -- ^ Rate multiplier factor
              -> [B]
        -- We want to bail on batching one side of a computation if it doesn't
        -- have a known multiplicity of i or i+, where i > 0.
        brule ctx n x
          | n > 0     = [b | let b = B (x*n) 1, rateDividesCtx ctx b]
          | otherwise = []

        -- | Given a multiplicity constraint and the computation's multiplicity,
        -- return a predicate constraining us to legal blockings.
        rateDividesCtx :: Maybe M -> B -> Bool
        rateDividesCtx Nothing   _      = True
        rateDividesCtx (Just m) (B i j)
            | Just n <- toCount m = (i*j) `divides` n
            | otherwise           = False

-- | Modify a blocking to ensure that bit arrays are never coalesced.
dontCoalesceBits :: Type -> Type -> BC -> BC
dontCoalesceBits a b bc =
  bc { inBlock  = dontCoalesceIf (isBitArrT a) (inBlock bc)
     , outBlock = dontCoalesceIf (isBitArrT b) (outBlock bc)
     }
  where
    dontCoalesceIf :: Bool -> Maybe a -> Maybe a
    dontCoalesceIf True  _ = Nothing
    dontCoalesceIf False x = x

-- | No vectorization
noVect :: Int -> Int -> BC
noVect inBits outBits =
    BC { inBlock  = Nothing
       , outBlock = Nothing
       , rateMult = 1
       , inBits   = inBits
       , outBits  = outBits
       }

byteSizePred :: Config -> BC -> Bool
byteSizePred dflags bc | VectOnlyBytes `testDynFlag` dflags =
    byteSized (inBits bc)  (inBlock bc) &&
    byteSized (outBits bc) (outBlock bc)
  where
    byteSized :: Int -> Maybe B -> Bool
    byteSized _ Nothing        = True
    byteSized n (Just (B i _)) = (i*n) `rem` 8 == 0

byteSizePred _ _ = True

vectAnnPred :: Config -> Maybe (VectAnn Int) -> BC -> Bool
vectAnnPred dflags (Just ann) bc | VectFilterAnn `testDynFlag` dflags =
    (matchInBlock ann . inBlock) bc && (matchOutBlock ann . outBlock) bc
  where
    matchInBlock :: VectAnn Int -> Maybe B -> Bool
    matchInBlock _             Nothing        = True
    matchInBlock AutoVect      _              = True
    matchInBlock (Rigid _ m _) (Just (B i _)) = i == m
    matchInBlock (UpTo _ m _)  (Just (B i _)) = i <= m

    matchOutBlock :: VectAnn Int -> Maybe B -> Bool
    matchOutBlock _             Nothing        = True
    matchOutBlock AutoVect      _              = True
    matchOutBlock (Rigid _ _ m) (Just (B i _)) = i == m
    matchOutBlock (UpTo _ _ m)  (Just (B i _)) = i <= m

vectAnnPred _ _ _ =
    True

isTransformer :: Comp l -> Bool
isTransformer c =
  case compRate c of
    Just TransR{} -> True
    _             -> False

vectAnn :: Comp l -> Maybe (VectAnn Nat)
vectAnn c = go (unComp c)
  where
    go :: [Step l] -> Maybe (VectAnn Nat)
    go [] =
        Nothing

    go steps =
        case last steps of
          RepeatC _ ann _ _ -> Just ann
          _                 -> Nothing

divides :: Integral a => a -> a -> Bool
divides x y = y `rem` x == 0
