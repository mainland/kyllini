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
import KZC.Core.Embed
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad.SEFKT
import KZC.Summary
import KZC.Trace
import KZC.Uniq

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
            MonadFlags,
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
        dumpStats <- asksFlags (testDynFlag ShowFusionStats)
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

-- | Input/output blocking, of the form $i^j$.
data B = B !Int !Int
  deriving (Eq, Ord, Show)

instance Pretty B where
    ppr (B i j) = ppr i <> char '^' <> ppr j

-- | Blocking candidate for a computation. Has the form $i^j \to k^l$.
data BC = BC { inBlock   :: Maybe B
             , outBlock  :: Maybe B
             , batchFact :: !Int
             , bcUtil    :: !Double
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
        whenVerb $ traceCoalesce $ nest 2 $
          text "Producer candidates:" </> stack (map ppr (sort bcs1))
        traceCoalesce $ nest 2 $
          text "Consumer:" <+> ppr (compRate c2) <+> text "::" <+> pprST b c </>
          ppr c2
        (c2', bcs2) <- localSTIndTypes (Just (b, b, c)) $
                       withLeftCtx (compRate c1) $ do
                       c2'  <- compT c2
                       bcs2 <- coalesceComp c2'
                       return (c2', bcs2)
        whenVerb $ traceCoalesce $ nest 2 $
          text "Consumer candidates:" </> stack (map ppr (sort bcs2))
        let bcs = sortBy (flip compare `on` thrd)
                  [(bc1, bc2, u) | bc1 <- bcs1,
                                   bc2 <- bcs2,
                                   compat bc1 bc2,
                                   let u = bcUtil bc1 +
                                           parUtil bc1 bc2 +
                                           bcUtil bc2]
        whenVerb $ traceCoalesce $ nest 2 $
          text "Compatible candidates:" </> stack (map ppr bcs)
        case bcs of
          [] -> return $ ParC ann b c1' c2' sloc
          bc@(bc1,bc2,_):_ -> do
            traceCoalesce $ nest 2 $
             text "Chose vectorization:" <+> ppr bc </>
             text "            For par:" <+> ppr (compRate c1) <+> text ">>>" <+> ppr (compRate c2)
            parc <- runK $ parC b (coalesce bc1 a b c1') (coalesce bc2 b c c2')
            traceCoalesce $ nest 2 $
              text "Coalesced par:" </> ppr parc
            head . unComp <$> rateComp parc
      where
        compat :: BC -> BC -> Bool
        compat bc1 bc2 =
            go (outBlock bc1) (inBlock bc2)
          where
            go :: Maybe B -> Maybe B -> Bool
            go Nothing         Nothing       = True
            go (Just (B i _)) (Just (B j _)) = j == i
            go _              _              = False

        pprST :: Type -> Type -> Doc
        pprST a b = text "ST" <+> pprPrec appPrec1 a <+> pprPrec appPrec1 b

        thrd :: (a, b, c) -> c
        thrd (_, _, x) = x

    stepT step = transStep step

coalesce :: forall l m . (IsLabel l, MonadTc m)
         => BC
         -> Type
         -> Type
         -> Comp l
         -> K l m Exp
coalesce bc a b comp =
    go bc
  where
    go :: BC -> K l m Exp
    go BC{inBlock = Just (B i _j), outBlock = Just (B k _l)} =
        parC a (coleft i a) (parC b (compC comp) (coright k b))

    go BC{inBlock = Just (B i _j), outBlock = Nothing} =
        parC a (coleft i a) (compC comp)

    go BC{inBlock = Nothing, outBlock = Just (B k _l)} =
        parC b (compC comp) (coright k b)

    go _ =
        compC comp

blockUtil :: Maybe B -> Double
blockUtil Nothing        = 0
blockUtil (Just (B i _)) = -(fromIntegral i)

parUtil :: BC -> BC -> Double
parUtil bc1 bc2 = go (outBlock bc1) (inBlock bc2)
  where
    go (Just (B i j)) (Just (B _k l)) = fromIntegral (2*i - abs(l-j)*i - (l+j) `quot` 2)
    go _              _               = 0

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
             crules (mAX_BLOCK_SIZE `quot` asz) (mAX_BLOCK_SIZE `quot` bsz)
    cs2   <- observeAll $ do
             guard (not (isBitArrT a) && not (isBitArrT b))
             brules ctx_left ctx_right
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "C-rules:" </> stack (map ppr (sort cs1))
    whenVerbLevel 2 $ traceCoalesce $ nest 2 $
      text "B-rules:" </> stack (map ppr (sort cs2))
    dflags <- askFlags
    let cs :: [BC]
        cs = filter (byteSizePred dflags asz bsz) $
             filter (vectAnnPred dflags (vectAnn comp)) $
             cs1 ++ cs2
    return cs
  where
    byteSizePred :: Flags -> Int -> Int -> BC -> Bool
    byteSizePred dflags asz bsz bc | VectOnlyBytes `testDynFlag` dflags =
        (byteSized asz . inBlock) bc && (byteSized bsz . outBlock) bc
      where
        byteSized :: Int -> Maybe B -> Bool
        byteSized _  Nothing        = True
        byteSized sz (Just (B i _)) = (i*sz) `rem` 8 == 0

    byteSizePred _ _ _ _ =
        True

    vectAnnPred :: Flags -> Maybe VectAnn -> BC -> Bool
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
           -> Co m BC
    crules max_left max_right = do
        (m_left, m_right) <- compInOutM comp
        b_in              <- crule m_left  max_left
        b_out             <- crule m_right max_right
        return BC { inBlock   = b_in
                  , outBlock  = b_out
                  , batchFact = 1
                  , bcUtil    = blockUtil b_in + blockUtil b_out
                  }
      where
        crule :: M   -- ^ Multiplicity
              -> Int -- ^ Maximum block size, measured in elements (not bytes)
              -> Co m (Maybe B)
        -- We only want to bail on coalescing one side of a computation if it
        -- doesn't have a known multiplicity of i or i+.
        crule m maxBlock =
            ifte (fromP m)
                 (\i -> Just <$> fact 2 i blockingPred)
                 (return Nothing)
          where
            blockingPred :: B -> Bool
            blockingPred (B i _) = i <= maxBlock

    -- | Implement the B rules
    brules :: Maybe M
           -> Maybe M
           -> Co m BC
    brules ctx_left ctx_right = do
        guard (isTransformer comp)
        (m_left, m_right) <- compInOutM comp
        let n_max         =  min (nBound m_left) (nBound m_right)
        n                 <- choices [2..n_max]
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
                  , bcUtil    = blockUtil b_in + blockUtil b_out
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
                           Just <$> fact 2 (i*n) p)
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

coleft :: (IsLabel l, MonadTc m)
       => Int
       -> Type
       -> K l m Exp
coleft 1 tau =
    identityC 1 $
    repeatC $ do
      x <- takeC  tau
      emitC x

coleft n tau =
    identityC n $
    repeatC $ do
      xs <- takesC n tau
      forC 0 n $ \i ->
        emitC (idxE xs i)

coright :: (IsLabel l, MonadTc m)
        => Int
        -> Type
        -> K l m Exp
coright 1 tau =
    identityC 1 $
    repeatC $ do
      x <- takeC  tau
      emitC x

coright n tau =
    identityC n $
    letrefC "xs" (arrKnownT n tau) $ \xs ->
    repeatC $ do
      forC 0 n $ \i -> do
        x <- takeC tau
        liftC $ assignE (idxE xs i) x
      xs' <- liftC $ derefE xs
      emitsC xs'
