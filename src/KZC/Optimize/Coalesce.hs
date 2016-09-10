{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.Coalesce
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.Coalesce where

#if MIN_VERSION_base(4,8,0)
import Control.Applicative (Alternative)
#else /* !MIN_VERSION_base(4,8,0) */
import Control.Applicative (Alternative, Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (MonadPlus(..),
                      guard,
                      when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.Logic (MonadLogic(..),
                            ifte)
import Control.Monad.IO.Class (MonadIO(..),
                               liftIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            modify)
import Control.Monad.Trans (lift)
import Data.Function (on)
import Data.List (sort, sortBy)
import Data.Maybe (isNothing)
import Text.PrettyPrint.Mainland

import KZC.Analysis.Rate
import KZC.Config
import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Util.Error
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

data CoStats = CoStats
    { upCoalesced :: !Int }

instance Monoid CoStats where
    mempty = CoStats 0

    x `mappend` y = CoStats
        { upCoalesced = upCoalesced x + upCoalesced y }

instance Pretty CoStats where
    ppr stats =
        text "Up-coalesced:" <+> ppr (upCoalesced stats)

newtype Co m a = Co { unCo :: ReaderT CoEnv (SEFKT (StateT CoStats m)) a }
  deriving (Functor, Applicative, Monad,
            Alternative, MonadPlus,
            MonadIO,
            MonadReader CoEnv,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadTrace,
            MonadTc,
            MonadLogic)

runCo :: forall m a . MonadErr m
      => Co m a
      -> m a
runCo m = evalStateT (runSEFKT (runReaderT (unCo m) defaultCoEnv)) mempty

observeAll :: forall m a . MonadErr m => Co m a -> Co m [a]
observeAll m = Co $ ReaderT $ \env ->
    lift $ runSEFKTM Nothing (runReaderT (unCo m) env)

getStats :: MonadTc m => Co m CoStats
getStats = Co $ lift $ lift get

modifyStats :: MonadTc m => (CoStats -> CoStats) -> Co m ()
modifyStats = Co . lift . lift . modify

withLeftCtx :: MonadTc m => Maybe (Rate M) -> Co m a -> Co m a
withLeftCtx Nothing m =
    local (\env -> env { leftCtx = CompR (Z 1) (Z 1) }) m

withLeftCtx (Just r2) m = do
    r1 <- asks leftCtx
    r  <- parRate r1 r2
    local (\env -> env { leftCtx = r }) m

withRightCtx :: MonadTc m => Maybe (Rate M) -> Co m a -> Co m a
withRightCtx Nothing m =
    local (\env -> env { rightCtx = CompR (Z 1) (Z 1) }) m

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
coalesceProgram = runCo . coalesceProg
  where
    coalesceProg :: Program l -> Co m (Program l)
    coalesceProg prog = do
        prog'     <- programT prog
        dumpStats <- asksConfig (testDynFlag ShowFusionStats)
        when dumpStats $ do
            stats  <- getStats
            liftIO $ putDocLn $ nest 2 $
                text "Fusion statistics:" </> ppr stats
        return prog'

{- Note [Pipeline Coalescing]

Pipeline coalescing attempts to do two things:

  1. Coalesce computation input/output into single blocks so that `take`s and
  `emit`s spread throughout a computation turn into a single `takes` and a
  single `emits`. This opens up opportunities for, e.g., LUTting, which can only
  LUT expressions.

  2. Process data in larger chunks. This effectively involves running the body
  of the computation multiple times, a transformation that is only valid for
  transformers, not computers.

Coalescing relies on inserting variants of two transformers,
${{co}_\textrm{L}}_{\tau}^n$ and ${{co}_\textrm{R}}_{\tau}^n$, into the pipeline
to the left and right (resp.) of the computation being transformed; we then rely
on fusion to optimize the transformed pipeline.

The transformer ${{co}_\textrm{L}}_{\tau}^n$ is:

    repeat { xs <- takes n; emit xs[0]; ...; emit xs[n-1]; }

${{co}_\textrm{L}}_{\tau}^n$ is inserted to the left of a computation. It takes
arrays of input and parcels them out element-by-element.

The transformer ${{co}_\textrm{R}}_{\tau}^n$ is:

    letref xs : arr[n] tau in
    repeat { x <- take; xs[0] := x; ...; x <- take; xs[n-1] := x; emits xs }

${{co}_\textrm{R}}_{\tau}^n$ is inserted to the right of a computation. It takes
its input one element at a time and outputs whole arrays.

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

Here, $i^j$ to the left of an arrow corresponds to inserting
${{co}_\textrm{L}}_{\tau}^i$ to the left of a computation, and $k^l$ corresponds
to inserting ${{co}_\textrm{R}}_{\tau}^k$ to the right of a computation. The C
rules do not change the multiplicity of a computation; they only reorganize the
way input/output is performed by inserting buffers.

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
-}

-- | Maximum size of input/output blocks, in bits
mAX_BLOCK_SIZE :: Int
mAX_BLOCK_SIZE = 512

-- | Maximum size of input/output batches, in elements.
mAX_BATCH_SIZE :: Int
mAX_BATCH_SIZE = 288

class Ord a => Metric a where
    infixl 6  .+.

    (.+.) :: a -> a -> a

data BlockMetric = BlockMetric !Int -- ^ 1 if byte-sized, 0 otherwise
                               !Int -- ^ Negated block count
                               !Int -- ^ Negated block size
  deriving (Eq, Ord, Show)

instance Pretty BlockMetric where
    ppr (BlockMetric x y z) = ppr (x, y, z)

instance Metric BlockMetric where
    BlockMetric s t u .+. BlockMetric x y z = BlockMetric (s+x) (t+y) (u+z)

data ParMetric = ParMetric !BlockMetric -- ^ Block utilities
                           !Int         -- ^ 1 if block sizes match, 0 otherwise
                           !Int         -- ^ Negated size of necessary rate matcher
  deriving (Eq, Ord, Show)

instance Pretty ParMetric where
    ppr (ParMetric x y z) = ppr (x, y, z)

instance Metric ParMetric where
    ParMetric s t u .+. ParMetric x y z = ParMetric (s.+.x) (t+y) (u+z)

-- | Input/output blocking, of the form $i^j$.
data B = B !Int !Int
  deriving (Eq, Ord, Show)

instance Pretty B where
    ppr (B i j) = ppr i <> char '^' <> ppr j

-- | Blocking candidate for a computation. Has the form $i^j \to k^l$.
data BC = BC { inBlock   :: Maybe B
             , outBlock  :: Maybe B
             , batchFact :: !Int
             , bcUtil    :: !BlockMetric
             }
  deriving (Eq, Ord, Show)

instance Pretty BC where
  ppr bc =
      pprV (inBlock bc) <+> text "->" <+> pprV (outBlock bc) <+>
      parens (ppr (bcUtil bc))
    where
      pprV Nothing  = char '_'
      pprV (Just v) = ppr v

instance MonadTc m => TransformExp (Co m) where

instance (IsLabel l, MonadTc m) => TransformComp l (Co m) where
    programT (Program decls comp tau) = do
        (decls', comp') <-
          declsT decls $
          inSTScope tau $
          inLocalScope $
          withLocContext comp (text "In definition of main") $ do
          traceCoalesce $ text "Top rate:" <+> ppr (compRate comp)
          (_s, a, b) <- askSTIndTypes
          comp'      <- compT comp
          flags      <- askConfig
          if testDynFlag CoalesceTop flags
            then do
              bcs <- coalesceComp comp'
              whenVerb $ traceCoalesce $ nest 2 $
                text "Top-level candidates:" </> stack (map ppr (sort bcs))
              asz <- typeSize a
              bsz <- typeSize b
              applyBestBlocking (sortAscendingBy (topMetric asz bsz) bcs)
                                a b comp'
            else return comp'
        return $ Program decls' comp' tau
      where
        applyBestBlocking :: [BC]
                          -> Type
                          -> Type
                          -> Comp l
                          -> Co m (Comp l)
        applyBestBlocking [] _ _ comp =
            return comp

        applyBestBlocking (bc:_) a b comp = do
            traceCoalesce $
             text "      Chose vectorization:" <+> ppr bc </>
             text "For top-level computation:" <+> ppr (compRate comp)
            comp' <- runK $ coalesce Top bc a b comp
            whenVerb $ traceCoalesce $ nest 2 $
              text "Coalesced top-level:" </> ppr comp'
            rateComp comp'

    compT c = transComp c >>= rateComp

    stepT c0@(ParC ann b c1 c2 sloc) = withSummaryContext c0 $ do
        (s, a, c)   <- askSTIndTypes
        -- Why can we use c1 and c2 instead of c1' and c1' when calling
        -- withRightCtx and withLeftCtx? The only time the context will limit
        -- our choices is when it is a computer, in which case both the original
        -- and coalesced computations will have the same rate.
        traceCoalesce $ nest 2 $
          text "Producer:" <+> ppr (compRate c1) <+> text "::" <+> pprST a b </>
          ppr c1
        (c1', bcs1) <- localSTIndTypes (Just (s, a, b)) $
                       withRightCtx (compRate c2) $ do
                       c1'  <- compT c1
                       bcs1 <- coalesceComp c1'
                       return (c1', bcs1)
        traceCoalesce $ nest 2 $
          text "Consumer:" <+> ppr (compRate c2) <+> text "::" <+> pprST b c </>
          ppr c2
        (c2', bcs2) <- localSTIndTypes (Just (b, b, c)) $
                       withLeftCtx (compRate c1) $ do
                       c2'  <- compT c2
                       bcs2 <- coalesceComp c2'
                       return (c2', bcs2)
        whenVerb $ traceCoalesce $ nest 2 $
          text "Producer candidates:" </> stack (map ppr (sort bcs1))
        whenVerb $ traceCoalesce $ nest 2 $
          text "Consumer candidates:" </> stack (map ppr (sort bcs2))
        let bcs = sortAscendingBy (uncurry parMetric)
                                  [(bc1, bc2) | bc1 <- bcs1, bc2 <- bcs2]
        c' <- applyBestBlocking bcs a b c c1' c2'
        traceCoalesce $ nest 2 $
          text "Final coalesced par:" </> ppr c'
        return c'
      where
        applyBestBlocking :: [(BC,BC)]
                          -> Type
                          -> Type
                          -> Type
                          -> Comp l
                          -> Comp l
                          -> Co m (Step l)
        applyBestBlocking [] _ b _ c1 c2 =
            return $ ParC ann b c1 c2 sloc

        applyBestBlocking (bc@(bc1,bc2):_) a b c c1 c2 = do
            traceCoalesce $ nest 2 $
              text "Chose vectorization:" <+> ppr bc </>
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

blockMetric :: Int -> Maybe B -> BlockMetric
blockMetric _ Nothing =
    BlockMetric 0 0 0

blockMetric sz (Just (B i j)) =
    BlockMetric (if i*sz `rem` 8 == 0 then 1 else 0)
                (-fromIntegral (i*(j-1)))
                (-fromIntegral i)

parMetric :: BC -> BC -> ParMetric
parMetric bc1 bc2 =
    go (outBlock bc1) (inBlock bc2)
  where
    go :: Maybe B -> Maybe B -> ParMetric
    go (Just (B i _j)) (Just (B k _l)) =
        ParMetric (bcUtil bc1 .+. bcUtil bc2)
                  (if i == k then 1 else 0)
                  (if i == k then 0 else -fromIntegral (lcm i k))

    go _ _ =
        ParMetric (bcUtil bc1 .+. bcUtil bc2) 0 0

topMetric :: Int -> Int -> BC -> Int
topMetric asz bsz BC { inBlock = Just (B i _), outBlock = Just (B j _) } =
    i*(if i*asz `rem` 8 == 0 then 8 else 1) +
    j*(if j*bsz `rem` 8 == 0 then 8 else 1)

topMetric _ _ _ = 0

data Mode = Top
          | Producer
          | Consumer
  deriving (Eq, Ord, Show)

coalescePar :: forall l m . (IsLabel l, MonadTc m)
            => PipelineAnn
            -> Type
            -> Type
            -> Type
            -> Comp l
            -> Comp l
            -> BC
            -> BC
            -> K l m Exp
coalescePar ann a b c comp1 comp2 bc1@BC{outBlock=Just (B i _)} bc2@BC{inBlock=Just (B j _)}
  | i == j    = matchedRates
  | otherwise = mismatchedRates
  where
    matchedRates :: K l m Exp
    matchedRates =
        parC' ann
              (coArrT i b)
              (coalesce Producer bc1 a b comp1)
              (coalesce Consumer bc2 b c comp2)

    mismatchedRates :: K l m Exp
    mismatchedRates =
        parC' ann (coArrT j b)
              (parC (coArrT i b)
                    (coalesce Producer bc1 a b comp1)
                    matcher)
              (coalesce Consumer bc2 b c comp2)
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
    parC' ann b (coalesce Top bc1 a b comp1)
                (coalesce Top bc2 b c comp2)

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

coalesce :: forall l m . (IsLabel l, MonadTc m)
         => Mode
         -> BC
         -> Type
         -> Type
         -> Comp l
         -> K l m Exp
coalesce mode bc a b comp =
    go bc
  where
    go :: BC -> K l m Exp
    go BC{inBlock = Just (B i _j), outBlock = Just (B k _l)} =
        -- Associate to the right
        -- coleft mode i a (coright mode k b (compC comp))
        -- Associate to the left
        coright mode k b (coleft mode i a (compC comp))

    go BC{inBlock = Just (B i _j), outBlock = Nothing} =
        coleft mode i a (compC comp)

    go BC{inBlock = Nothing, outBlock = Just (B k _l)} =
        coright mode k b (compC comp)

    go _ =
        compC comp

coleft :: forall l m . (IsLabel l, MonadTc m)
       => Mode
       -> Int       -- ^ Number of elements to take per round
       -> Type      -- ^ Type of elements
       -> K l m Exp -- ^ Right side of par
       -> K l m Exp
coleft mode n tau c_right =
    parC tau (c_left mode n tau) c_right
  where
    c_left :: Mode -> Int -> Type -> K l m Exp
    c_left _ 1 tau =
        identityC 1 $
        repeatC $ do
          x <- takeC tau
          emitC x

    c_left Consumer n tau =
        repeatC $ do
          xs <- takeC (coArrT n tau)
          emitsC xs

    c_left _ n tau =
        identityC n $
        repeatC $ do
          xs <- takesC n tau
          emitsC xs

coright :: forall l m . (IsLabel l, MonadTc m)
        => Mode
        -> Int       -- ^ Number of elements to emit per round
        -> Type      -- ^ Type of elements
        -> K l m Exp -- ^ Left side of par
        -> K l m Exp
coright mode n tau c_left =
    parC tau c_left (c_right mode n tau)
  where
    c_right :: Mode -> Int -> Type -> K l m Exp
    c_right _ 1 tau =
        identityC 1 $
        repeatC $ do
          x <- takeC tau
          emitC x

    c_right Producer n tau =
        repeatC $ do
          xs <- takesC n tau
          emitC xs

    c_right _ n tau =
        identityC n $
        repeatC $ do
          xs <- takesC n tau
          emitsC xs

coalesceComp :: forall l m . (IsLabel l, MonadTc m)
             => Comp l
             -> Co m [BC]
coalesceComp comp = do
    (_, a, b) <- askSTIndTypes
    ctx_left  <- askLeftCtx
    ctx_right <- askRightCtx
    traceCoalesce $ text "Left context:" <+> ppr ctx_left
    traceCoalesce $ text "Right context:" <+> ppr ctx_right
    traceCoalesce $ text "Vectorization annotation:" <+> ppr (vectAnn comp)
    asz   <- typeSize a
    bsz   <- typeSize b
    cs1   <- observeAll $ do
             guard (not (isBitArrT a) && not (isBitArrT b))
             crules asz asz (mAX_BLOCK_SIZE `quot` asz) (mAX_BLOCK_SIZE `quot` bsz)
    cs2   <- observeAll $ do
             guard (not (isBitArrT a) && not (isBitArrT b))
             brules asz bsz ctx_left ctx_right
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "C-rules:" </> stack (map ppr (sort cs1))
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "B-rules:" </> stack (map ppr (sort cs2))
    dflags <- askConfig
    let cs :: [BC]
        cs = filter (byteSizePred dflags asz bsz) $
             filter (vectAnnPred dflags (vectAnn comp)) $
             cs1 ++ cs2
    return cs
  where
    byteSizePred :: Config -> Int -> Int -> BC -> Bool
    byteSizePred dflags asz bsz bc | VectOnlyBytes `testDynFlag` dflags =
        (byteSized asz . inBlock) bc && (byteSized bsz . outBlock) bc
      where
        byteSized :: Int -> Maybe B -> Bool
        byteSized _  Nothing        = True
        byteSized sz (Just (B i _)) = (i*sz) `rem` 8 == 0

    byteSizePred _ _ _ _ =
        True

    vectAnnPred :: Config -> Maybe VectAnn -> BC -> Bool
    vectAnnPred dflags ann | VectFilterAnn `testDynFlag` dflags =
        matchVectAnn ann
      where
        matchVectAnn :: Maybe VectAnn -> BC -> Bool
        matchVectAnn Nothing _ =
            True

        matchVectAnn (Just ann) bc =
            (matchInBlock ann . inBlock) bc && (matchOutBlock ann . outBlock) bc

        matchInBlock :: VectAnn -> Maybe B -> Bool
        matchInBlock _             Nothing        = True
        matchInBlock AutoVect      _              = True
        matchInBlock (Rigid _ m _) (Just (B i _)) = i == m
        matchInBlock (UpTo _ m _)  (Just (B i _)) = i <= m

        matchOutBlock :: VectAnn -> Maybe B -> Bool
        matchOutBlock _             Nothing        = True
        matchOutBlock AutoVect      _              = True
        matchOutBlock (Rigid _ _ m) (Just (B i _)) = i == m
        matchOutBlock (UpTo _ _ m)  (Just (B i _)) = i <= m

    vectAnnPred _ _ =
        const True

    -- | Implement the C rules.
    crules :: Int
           -> Int
           -> Int
           -> Int
           -> Co m BC
    crules asz bsz max_left max_right = do
        (m_left, m_right) <- compInOutM comp
        b_in              <- crule m_left  max_left
        b_out             <- crule m_right max_right
        return BC { inBlock   = b_in
                  , outBlock  = b_out
                  , batchFact = 1
                  , bcUtil    = blockMetric asz b_in .+. blockMetric bsz b_out
                  }
      where
        crule :: M   -- ^ Multiplicity
              -> Int -- ^ Maximum block size, measured in elements (not bytes)
              -> Co m (Maybe B)
        -- We only want to bail on coalescing one side of a computation if it
        -- doesn't have a known multiplicity of i or i+.
        crule m maxBlock =
            ifte (fromP m)
                 (\i -> if i == 0
                        then return Nothing
                        else Just <$> fact i i blockingPred)
                 (return Nothing)
          where
            blockingPred :: B -> Bool
            blockingPred (B i _) = i <= maxBlock

    -- | Implement the B rules
    brules :: Int
           -> Int
           -> Maybe M
           -> Maybe M
           -> Co m BC
    brules asz bsz ctx_left ctx_right = do
        guard (isTransformer comp)
        (m_left, m_right) <- compInOutM comp
        let n_max         =  min (nBound m_left) (nBound m_right)
        n                 <- choices [1..n_max]
        b_in              <- brule ctx_left  m_left  n
        b_out             <- brule ctx_right m_right n
        -- A batch of the form i^j -> k^l is only allowed if j and l DO NOT have
        -- common factors, i.e., they must be coprime.
        guard (bfCoprime b_in b_out)
        -- Disallow no-op batching strategy.
        guard (not (isNothing b_in && isNothing b_out))
        return BC { inBlock   = b_in
                  , outBlock  = b_out
                  , batchFact = n
                  , bcUtil    = blockMetric asz b_in .+. blockMetric bsz b_out
                  }
      where
        -- | Return 'True' if blocking factors are coprime, 'False' otherwise.
        bfCoprime :: Maybe B -> Maybe B -> Bool
        bfCoprime (Just (B _ n)) (Just (B _ m)) = gcd n m == 1
        bfCoprime _              _              = True

        brule :: Maybe M
              -> M
              -> Int
              -> Co m (Maybe B)
        -- We want to bail on batching one side of a computation if it doesn't
        -- have a known multiplicity of i or i+ *or*
        brule ctx m n =
            ifte (fromP m)
                 (\i -> do p <- mkBlockingPred ctx m
                           if i == 0
                             then return Nothing
                             else Just <$> fact i (i*n) p)
                 (return Nothing)

        -- | Upper bound on n.
        nBound :: M -> Int
        nBound (N i) | i == 0    = mAX_BATCH_SIZE
                     | otherwise = mAX_BATCH_SIZE `quot` i
        nBound (P i)             = mAX_BATCH_SIZE `quot` i
        nBound Z{}               = mAX_BATCH_SIZE

        -- | Given a multiplicity constraint and the computation's multiplicity,
        -- return a predicate constraining us to legal blockings.
        mkBlockingPred :: Maybe M -> M -> Co m (B -> Bool)
        mkBlockingPred Nothing _m  =
            return $ const True

        -- If we have a context, we must be a transformer.
        mkBlockingPred (Just m_ctx) _m = do
            n_ctx <- fromP m_ctx
            return $ \(B i j) -> (i*j) `divides` n_ctx

isTransformer :: Comp l -> Bool
isTransformer c =
  case compRate c of
    Just TransR{} -> True
    _             -> False

vectAnn :: Comp l -> Maybe VectAnn
vectAnn c = go (unComp c)
  where
    go :: [Step l] -> Maybe VectAnn
    go [] =
        Nothing

    go steps =
        case last steps of
          RepeatC _ ann _ _ -> Just ann
          _                 -> Nothing

choices :: MonadPlus m => [a] -> m a
choices = foldr (mplus . return) mzero

divides :: Integral a => a -> a -> Bool
divides x y = y `rem` x == 0

-- | Factor a multiplicity into all possible blockings satisfying a given
-- constraint on the blocking.
fact :: (MonadPlus m, MonadTc m)
     => Int         -- ^ Minimum multiplicity
     -> Int         -- ^ Maximum multiplicity
     -> (B -> Bool) -- ^ Predicate on blocking
     -> m B
fact n m p =
    choices [B i j | i <- [n..m],
                     m `rem` i == 0,
                     i `rem` n == 0,
                     let j = m `quot` i,
                     p (B i j)]
