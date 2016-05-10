{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.ReadWriteSet
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.ReadWriteSet (
    RWSet(..),
    PreciseInterval(..),
    Intv(..),

    readWriteSets
  ) where

import qualified Prelude as P
import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (void)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            execStateT,
                            gets,
                            modify)
import Control.Monad.Trans (MonadTrans(..))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Ratio (numerator)
import Text.PrettyPrint.Mainland hiding (empty)

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax hiding (PI)
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice

readWriteSets :: MonadTc m
              => Exp
              -> m (Map Var (Known RWSet), Map Var (Known RWSet))
readWriteSets e = do
    s <- execRW (rangeExp e)
    return (readSet s, writeSet s)

-- | An interval
data Intv -- | Empty interval
          = EmptyI
          -- | Invariant: @'RangeI' i1 i2@ iff @i1@ <= @i2@.
          | RangeI Integer Integer
  deriving (Eq, Ord, Show)

singI :: Integer -> Known Intv
singI i = Known $ RangeI i i

fromSingI :: Monad m => Known Intv -> m Integer
fromSingI (Known (RangeI i j)) | i == j =
    return i

fromSingI _ =
    fail " interval"

instance Pretty Intv where
    ppr EmptyI         = text "()"
    ppr (RangeI lo hi)
        | hi == lo     = ppr lo
        | otherwise    = brackets $ ppr lo <> comma <> ppr hi

instance Poset Intv where
    EmptyI   <= _          = True
    RangeI i j <= RangeI i' j' = i' <= i && j <= j'
    _        <= _          = False

instance Lattice Intv where
    EmptyI     `lub` i            = i
    i          `lub` EmptyI       = i
    RangeI i j `lub` RangeI i' j' = RangeI l h
      where
        l = min i i'
        h = max j j'

    EmptyI     `glb` _            = EmptyI
    _          `glb` EmptyI       = EmptyI
    RangeI i j `glb` RangeI i' j'
        | gap                     = EmptyI
        | otherwise               = RangeI l h
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 || i' - j > 1

-- | A bounded known interval
newtype BoundedInterval = BI (Known Intv)
  deriving (Eq, Ord, Show, Poset, Lattice, BoundedLattice)

instance Pretty BoundedInterval where
    ppr (BI x) = ppr x

-- | A precisely known interval
newtype PreciseInterval = PI (Known Intv)
  deriving (Eq, Ord, Show, Poset)

instance Pretty PreciseInterval where
    ppr (PI x) = ppr x

instance Lattice PreciseInterval where
    i `lub` j | i <= j = j
              | j <= i = i

    PI (Known (RangeI i j)) `lub` PI (Known (RangeI i' j'))
        | gap       = top
        | otherwise = PI (Known (RangeI l h))
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 || i' - j > 1

    _ `lub` _ = top

    i `glb` j | i <= j = i
              | j <= i = j

    PI (Known (RangeI i j)) `glb` PI (Known (RangeI i' j'))
        | gap       = bot
        | l == h    = PI (Known EmptyI)
        | otherwise = PI (Known (RangeI l h))
      where
        l   = max i i'
        h   = min j j'
        gap = i - j' > 1 || i' - j > 1

    _ `glb` _ = bot

instance BoundedLattice PreciseInterval where
    top = PI top
    bot = PI bot

-- | References
data Ref = VarR Var
         | IdxR Ref Val (Maybe Int)
         | ProjR Ref Field
  deriving (Eq, Ord, Show)

instance Pretty Ref where
    pprPrec _ (VarR v) =
        ppr v

    pprPrec _ (IdxR r i Nothing) =
        pprPrec appPrec1 r <> brackets (ppr i)

    pprPrec _ (IdxR r i (Just len)) =
        pprPrec appPrec1 r <> brackets (commasep [ppr i, ppr len])

    pprPrec _ (ProjR r f) =
        pprPrec appPrec1 r <> text "." <> ppr f

-- | Values
data Val = UnknownV           -- ^ Unknown (not-yet defined)
         | IntV (Known Intv)  -- ^ All integers in a range
         | BoolV (Known Bool) -- ^ Booleans
         | TopV               -- ^ Could be anything as far as we know...
  deriving (Eq, Ord, Show)

instance Pretty Val where
    ppr UnknownV       = text "unknown"
    ppr (IntV x)       = ppr x
    ppr (BoolV x)      = ppr x
    ppr TopV           = text "top"

instance Poset Val where
    UnknownV <= _        = True
    _        <= TopV     = True
    IntV bi  <= IntV bi' = bi <= bi'
    BoolV b  <= BoolV b' = b <= b'
    _        <= _        = False

instance Lattice Val where
    IntV bi `lub` IntV bi' = IntV (bi `lub` bi')
    BoolV b `lub` BoolV b' = BoolV (b `lub` b')
    _       `lub` _        = top

    IntV bi `glb` IntV bi' = IntV (bi `glb` bi')
    BoolV b `glb` BoolV b' = BoolV (b `glb` b')
    _       `glb` _        = bot

instance BranchLattice Val where
    IntV bi `bub` IntV bi' = IntV (bi `lub` bi')
    BoolV b `bub` BoolV b' = BoolV (b `lub` b')
    _       `bub` _        = top

instance BoundedLattice Val where
    top = TopV
    bot = UnknownV

-- | Read-write sets
data RWSet = ArrayS BoundedInterval PreciseInterval
  deriving (Eq, Ord, Show)

instance Pretty RWSet where
    ppr (ArrayS bi pi) = text "array" <+> ppr bi <+> ppr pi

instance Poset RWSet where
    ArrayS rs ws <= ArrayS rs' ws' = rs <= rs' && ws <= ws'

instance Lattice RWSet where
    ArrayS rs ws `lub` ArrayS rs' ws' = ArrayS (rs `lub` rs') (ws `lub` ws')

    ArrayS rs ws `glb` ArrayS rs' ws' = ArrayS (rs `glb` rs') (ws `glb` ws')

instance BranchLattice RWSet where
    ArrayS rs ws `bub` ArrayS rs' ws' = ArrayS (rs `lub` rs') (ws `glb` ws')

instance BranchLattice (Known RWSet) where
    Unknown `bub` x       = x
    x       `bub` Unknown = x
    Any     `bub` _       = Any
    _       `bub` Any     = Any
    Known x `bub` Known y = Known (x `bub` y)

-- | The range analysis state
data RState = RState
    { vals     :: Map Var Val
    , readSet  :: Map Var (Known RWSet)
    , writeSet :: Map Var (Known RWSet)
    }

defaultRState :: RState
defaultRState = RState
    { vals     = mempty
    , readSet  = mempty
    , writeSet = mempty
    }

instance Poset RState where
    r1 <= r2 = vals r1 <= vals r2 &&
               readSet r1 <= readSet r2 &&
               writeSet r1 <= writeSet r2

instance Lattice RState where
    r1 `lub` r2 = RState
        { vals     = vals r1     `lub` vals r2
        , readSet  = readSet r1  `lub` readSet r2
        , writeSet = writeSet r1 `lub` writeSet r2
        }

    r1 `glb` r2 = RState
        { vals     = vals r1     `glb` vals r2
        , readSet  = readSet r1  `glb` readSet r2
        , writeSet = writeSet r1 `glb` writeSet r2
        }

instance BranchLattice RState where
    r1 `bub` r2 = RState
        { vals     = vals r1     `bub` vals r2
        , readSet  = readSet r1  `bub` readSet r2
        , writeSet = writeSet r1 `bub` writeSet r2
        }

newtype RW m a = RW { unRW :: StateT RState m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState RState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

execRW :: MonadTc m => RW m a -> m RState
execRW m = execStateT (unRW m) defaultRState

instance MonadTrans RW where
    lift = RW . lift

collectState :: MonadTc m => RW m a -> RW m (a, RState)
collectState m = do
    pre  <- get
    x    <- m
    post <- get
    put pre
    return (x, post)

lookupVal :: MonadTc m => Var -> RW m Val
lookupVal v =
    fromMaybe bot <$> gets (Map.lookup v . vals)

extendVals :: forall a m . MonadTc m => [(Var, Val)] -> RW m a -> RW m a
extendVals vvals m = do
    old_vals     <- gets $ \s -> map (\v -> Map.lookup v (vals s)) vs
    old_readSet  <- gets $ \s -> map (\v -> Map.lookup v (readSet s)) vs
    old_writeSet <- gets $ \s -> map (\v -> Map.lookup v (writeSet s)) vs
    modify $ \s -> s { vals = foldl' insert (vals s) vvals }
    x <- m
    modify $ \s -> s { vals     = foldl' update (vals s)     (vs `zip` old_vals)
                     , readSet  = foldl' update (readSet s)  (vs `zip` old_readSet)
                     , writeSet = foldl' update (writeSet s) (vs `zip` old_writeSet)
                     }
    return x
  where
    vs :: [Var]
    vs = map fst vvals

    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

    update :: Ord k => Map k v -> (k, Maybe v) -> Map k v
    update m (k, v) = Map.update (const v) k m

extendWildVals :: MonadTc m => [(WildVar, Val)] -> RW m a -> RW m a
extendWildVals wvs = extendVals [(bVar bv, val) | (TameV bv, val) <- wvs]

putVal :: MonadTc m => Var -> Val -> RW m ()
putVal v val =
    modify $ \s -> s { vals = Map.insert v val (vals s) }

updateRWSet :: forall m .  MonadTc m
            => Ref
            -> (RState -> Map Var (Known RWSet))
            -> (RState -> Map Var (Known RWSet) -> RState)
            -> RW m ()
updateRWSet ref proj upd =
    go ref
  where
    go :: Ref -> RW m ()
    go (VarR v) =
        modify $ \s -> upd s $ Map.insert v top (proj s)

    go (IdxR (VarR v) idx len) =
        modify $ \s ->
            let rwset :: Known RWSet
                rwset =
                    fromMaybe bot (Map.lookup v (proj s))
                    `lub`
                    Known (ArrayS (BI intv) (PI intv))
            in
              upd s $ Map.insert v rwset (proj s)
      where
        intv :: Known Intv
        intv = sliceToInterval idx len

    go (IdxR r _ _) =
        go r

    go (ProjR r _) =
        go r

updateReadSet :: forall m . MonadTc m => Ref -> RW m ()
updateReadSet ref =
    updateRWSet ref readSet (\s x -> s { readSet = x })

updateWriteSet :: forall m . MonadTc m => Ref -> RW m ()
updateWriteSet ref =
    updateRWSet ref writeSet (\s x -> s { writeSet = x })

sliceToInterval :: Val -> Maybe Int -> Known Intv
sliceToInterval (IntV intv@(Known _)) Nothing =
    intv

sliceToInterval (IntV i) (Just len) | Just idx <- fromSingI i =
    Known $ RangeI idx (idx + fromIntegral len - 1)

sliceToInterval _ _ =
    top

rangeExp :: forall m . MonadTc m => Exp -> RW m Val
rangeExp e =
    withFvContext e $
    go e
  where
    go :: Exp -> RW m Val
    go (ConstE c _) =
        return $ rangeConst c
      where
        rangeConst :: Const -> Val
        rangeConst (BoolC b)               = BoolV (pure b)
        rangeConst (FixC I _s _w (BP 0) r) = IntV $ singI (numerator r)
        rangeConst _c                      = top

    go (VarE v _) = do
        updateReadSet (VarR v)
        lookupVal v

    go (UnopE op e _) =
        unop op <$> go e
      where
        unop :: Unop -> Val -> Val
        unop Lnot (BoolV b)                      = BoolV $ not <$> b
        unop Lnot _                              = BoolV top
        unop Bnot (IntV _)                       = IntV top
        unop Bnot _                              = top
        unop Neg (IntV i)
            | Just x <- fromSingI i              = IntV <$> singI $ negate x
        unop Neg _                               = top
        unop (Cast (FixT I _s _w (BP 0) _)) _    = IntV top
        unop Cast{} _                            = top
        unop (Bitcast (FixT I _s _w (BP 0) _)) _ = IntV top
        unop Bitcast{} _                         = top
        unop Len _                               = IntV top

    go (BinopE op e1 e2 _) =
        binop op <$> go e1 <*> go e2
      where
        binop :: Binop -> Val -> Val -> Val
        binop Lt (IntV i) (IntV j) = BoolV $ (<) <$> i <*> j
        binop Le (IntV i) (IntV j) = BoolV $ (P.<=) <$> i <*> j
        binop Eq (IntV i) (IntV j) = BoolV $ (==) <$> i <*> j
        binop Ge (IntV i) (IntV j) = BoolV $ (>=) <$> i <*> j
        binop Gt (IntV i) (IntV j) = BoolV $ (>) <$> i <*> j
        binop Ne (IntV i) (IntV j) = BoolV $ (/=) <$> i <*> j

        binop Lt _ _ = BoolV top
        binop Eq _ _ = BoolV top
        binop Le _ _ = BoolV top
        binop Ge _ _ = BoolV top
        binop Gt _ _ = BoolV top
        binop Ne _ _ = BoolV top

        binop Land (BoolV b) (BoolV b') = BoolV $ (&&) <$> b <*> b'
        binop Lor  (BoolV b) (BoolV b') = BoolV $ (||) <$> b <*> b'

        binop Land _ _ = BoolV top
        binop Lor  _ _ = BoolV top

        binop Band _ _ = top
        binop Bor  _ _ = top
        binop Bxor _ _ = top

        binop LshL _ _ = top
        binop LshR _ _ = top
        binop AshR _ _ = top

        binop Add (IntV (Known (RangeI xlo xhi))) (IntV (Known (RangeI ylo yhi))) =
            IntV $ Known $ RangeI (xlo + ylo) (xhi + yhi)

        binop Sub (IntV (Known (RangeI xlo xhi))) (IntV (Known (RangeI ylo yhi))) =
            IntV $ Known $ RangeI (xlo - yhi) (xhi + ylo)

        binop Mul (IntV (Known (RangeI xlo xhi))) (IntV (Known (RangeI ylo yhi))) =
            IntV $ Known $ RangeI (xlo * ylo) (xhi * yhi)

        binop Div (IntV (Known (RangeI xlo xhi))) (IntV (Known (RangeI ylo yhi))) =
            IntV $ Known $ RangeI (xlo `quot` yhi) (xhi `quot` ylo)

        binop Add _ _ = top
        binop Sub _ _ = top
        binop Mul _ _ = top
        binop Div _ _ = top
        binop Rem _ _ = top
        binop Pow _ _ = top
        binop Cat _ _ = top

    go (IfE e1 e2 e3 _) = do
        val1 <- rangeExp e1
        rangeIf val1 (rangeExp e2) (rangeExp e3)

    go (LetE (LetLD v tau e1 _) e2 _) = do
        val1 <- rangeExp e1
        extendVars [(bVar v, tau)] $
            extendVals [(bVar v, val1)] $
            rangeExp e2

    go (LetE (LetRefLD v tau Nothing _) e2 _) =
        extendVars [(bVar v, refT tau)] $
        extendVals [(bVar v, bot)] $
        rangeExp e2

    go (LetE (LetRefLD v tau (Just e1) _) e2 _) = do
        val1 <- rangeExp e1
        extendVars [(bVar v, refT tau)] $
            extendVals [(bVar v, val1)] $
            rangeExp e2

    go (CallE _v _iotas es _) = do
        mapM_ rangeArg es
        return top

    go (DerefE e _) = do
        ref <- rangeRef e
        updateReadSet ref
        case ref of
          VarR v -> lookupVal v
          _      -> return top

    go (AssignE e1 e2 _) = do
        ref <- rangeRef e1
        val <- rangeExp e2
        updateWriteSet ref
        case ref of
          VarR v -> putVal v val
          _      -> return ()
        return top

    go (WhileE e1 e2 _) = do
        val <- rangeExp e1
        rangeWhile val (rangeExp e2)

    go (ForE _ v tau e_start e_len e_body _) = do
        v_start <- rangeExp e_start
        v_len   <- rangeExp e_len
        extendVars [(v, tau)] $
            rangeFor v v_start v_len (rangeExp e_body)

    go (ArrayE es _) = do
        mapM_ rangeExp es
        return top

    go e@(IdxE VarE{} _ _ _) = do
        ref <- rangeRef e
        updateReadSet ref
        return top

    go (IdxE e1 e2 _ _) = do
        void $ rangeExp e1
        void $ rangeExp e2
        return top

    go (StructE _ flds _) = do
        mapM_ (go . snd) flds
        return top

    go (ProjE e _ _) = do
        void $ rangeExp e
        return top

    go (PrintE _ es _) = do
        mapM_ rangeExp es
        return top

    go ErrorE{} =
        return top

    go (ReturnE _ e _) =
        rangeExp e

    go (BindE wv tau e1 e2 _) = do
        val1 <- rangeExp e1
        extendWildVars [(wv, tau)] $
          extendWildVals [(wv, val1)] $
          rangeExp e2

    go (LutE e) =
        go e

rangeRef :: forall m . MonadTc m => Exp -> RW m Ref
rangeRef = go
  where
    go :: Exp -> RW m Ref
    go (VarE v _) =
        pure $ VarR v

    go (IdxE e1 e2 len _) =
        IdxR <$> rangeRef e1 <*> rangeExp e2 <*> pure len

    go (ProjE e f _) =
        ProjR <$> rangeRef e <*> pure f

    go e =
        faildoc $ nest 2$
        text "Non-reference expression evaluated in reference context:" </> ppr e

rangeArg :: forall m . MonadTc m => Exp -> RW m ()
rangeArg e = do
    tau <- inferExp e
    case tau of
      RefT {} -> rangeRefArg e
      _       -> void $ rangeExp e
  where
    rangeRefArg :: MonadTc m => Exp -> RW m ()
    rangeRefArg e = do
        ref <- rangeRef e
        updateWriteSet ref

rangeIf :: (BranchLattice a, MonadTc m)
        => Val
        -> RW m a
        -> RW m a
        -> RW m a
rangeIf (BoolV (Known True)) k2 _k3 =
    k2

rangeIf (BoolV (Known False)) _k2 k3 =
    k3

rangeIf _ k2 k3 = do
    (val2, post2) <- collectState k2
    (val3, post3) <- collectState k3
    put $ post2 `bub` post3
    return $ val2 `bub` val3

rangeWhile :: (BoundedLattice a, MonadTc m)
           => Val
           -> RW m a
           -> RW m a
rangeWhile (BoolV (Known False)) k =
    k

rangeWhile _ k = do
    void k
    return top

rangeFor :: MonadTc m => Var -> Val -> Val -> RW m a -> RW m a
rangeFor v (IntV i) (IntV j) k | Just start <- fromSingI i, Just len <- fromSingI j =
    extendVals [(v, IntV $ Known $ RangeI start (start+len-1))] k

rangeFor v _v_start _v_len k =
    extendVals [(v, top)] k
