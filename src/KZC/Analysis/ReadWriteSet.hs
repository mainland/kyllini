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

    readWriteSets
  ) where

import qualified Prelude as P
import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (unless,
                      void)
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
import Text.PrettyPrint.Mainland hiding (empty)

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax hiding (PI)
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq
import KZC.Util.Interval
import KZC.Util.Lattice

readWriteSets :: MonadTc m
              => Exp
              -> m (Map Var RWSet, Map Var RWSet)
readWriteSets e = do
    s <- execRW (rangeExp e)
    return (readSet s, writeSet s)

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
data Val = UnknownV              -- ^ Unknown (not-yet defined)
         | IntV (Bound Interval) -- ^ All integers in a range
         | BoolV (Known Bool)    -- ^ Booleans
         | TopV                  -- ^ Could be anything as far as we know...
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

instance BoundedLattice RWSet where
    top = ArrayS top top
    bot = ArrayS bot bot

-- | The range analysis state
data RState = RState
    { vals     :: Map Var Val
    , readSet  :: Map Var RWSet
    , writeSet :: Map Var RWSet
    }
  deriving (Eq)

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
            -> (RState -> Map Var RWSet)
            -> (Var -> RWSet -> RWSet -> RW m ())
            -> RW m ()
updateRWSet ref proj upd =
    go ref
  where
    go :: Ref -> RW m ()
    go (VarR v) = do
        old <- gets (fromMaybe bot . Map.lookup v . proj)
        upd v old new
      where
        new :: RWSet
        new = top

    go (IdxR (VarR v) idx len) = do
        old <- gets (fromMaybe bot . Map.lookup v . proj)
        upd v old new
      where
        new :: RWSet
        new = ArrayS (BI intv) (PI intv)

        intv :: Bound Interval
        intv = sliceToInterval idx len

    go (IdxR r _ _) =
        go r

    go (ProjR r _) =
        go r

updateReadSet :: forall m . MonadTc m => Ref -> RW m ()
updateReadSet ref =
    updateRWSet ref readSet upd
  where
    upd :: Var -> RWSet -> RWSet -> RW m ()
    upd v old new = do
      wset <- gets (fromMaybe bot . Map.lookup v . writeSet)
      unless (new <= wset) $
        modify $ \s -> s { readSet = Map.insert v (old `lub` new) (readSet s) }

updateWriteSet :: forall m . MonadTc m => Ref -> RW m ()
updateWriteSet ref =
    updateRWSet ref writeSet upd
  where
    upd :: Var -> RWSet -> RWSet -> RW m ()
    upd v old new =
      modify $ \s -> s { writeSet = Map.insert v (old `lub` new) (writeSet s) }

sliceToInterval :: Val -> Maybe Int -> Bound Interval
sliceToInterval (IntV intv@KnownB{}) Nothing =
    intv

sliceToInterval (IntV i) (Just len) | Just idx <- fromUnit i =
    interval idx (idx + fromIntegral len - 1 :: Integer)

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
        rangeConst (FixC I _s _w (BP 0) x) = IntV $ unit x
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
            | Just x <- fromUnit i               = IntV $ unit (negate x :: Integer)
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
        binop Lt (IntV i) (IntV j) = BoolV . toKnown $ (<) <$> i <*> j
        binop Le (IntV i) (IntV j) = BoolV . toKnown $ (P.<=) <$> i <*> j
        binop Eq (IntV i) (IntV j) = BoolV . toKnown $ (==) <$> i <*> j
        binop Ge (IntV i) (IntV j) = BoolV . toKnown $ (>=) <$> i <*> j
        binop Gt (IntV i) (IntV j) = BoolV . toKnown $ (>) <$> i <*> j
        binop Ne (IntV i) (IntV j) = BoolV . toKnown $ (/=) <$> i <*> j

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

        binop Add (IntV x) (IntV y) | Just (xlo, xhi) <- fromInterval x, Just (ylo, yhi) <- fromInterval y =
            IntV $ interval (xlo + ylo :: Integer) (xhi + yhi :: Integer)

        binop Sub (IntV x) (IntV y) | Just (xlo, xhi) <- fromInterval x, Just (ylo, yhi) <- fromInterval y =
            IntV $ interval (xlo - yhi :: Integer) (xhi + ylo :: Integer)

        binop Mul (IntV x) (IntV y) | Just (xlo, xhi) <- fromInterval x, Just (ylo, yhi) <- fromInterval y =
            IntV $ interval (xlo * ylo :: Integer) (xhi * yhi :: Integer)

        binop Div (IntV x) (IntV y) | Just (xlo, xhi) <- fromInterval x, Just (ylo, yhi) <- fromInterval y =
            IntV $ interval (xlo `quot` yhi :: Integer) (xhi `quot` ylo :: Integer)

        binop Add _ _ = top
        binop Sub _ _ = top
        binop Mul _ _ = top
        binop Div _ _ = top
        binop Rem _ _ = top
        binop Pow _ _ = top
        binop Cat _ _ = top

        toKnown :: Bound a -> Known a
        toKnown UnknownB   = Unknown
        toKnown (KnownB x) = Known x
        toKnown AnyB       = Any

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

    go (LutE _ e) =
        go e

    go GenE{} =
        return top

rangeRef :: forall m . MonadTc m => Exp -> RW m Ref
rangeRef = go
  where
    go :: Exp -> RW m Ref
    go (VarE v _) =
        lookupVar v >>= go
      where
        -- For extra precision, when we read an entire array, we specify that we
        -- read all its elements, not that we read top---the two are not equal!
        -- We have to then deal with the returned IdxR range in the next case
        -- below.
        go :: Type -> RW m Ref
        go (ArrT (ConstI n _) _ _) =
            pure $ IdxR (VarR v) (IntV $ unit (0::Integer)) (Just n)

        go (RefT tau _) =
            go tau

        go _ =
            pure $ VarR v

    go (IdxE e1 e2 len _) =
        rangeRef e1 >>= go
      where
        -- We must handle IdxR specially here as noted above.
        go :: Ref -> RW m Ref
        go (IdxR ref _ _) = IdxR ref <$> rangeExp e2 <*> pure len
        go ref            = IdxR ref <$> rangeExp e2 <*> pure len

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
rangeFor v (IntV i) (IntV j) k | Just start <- fromUnit i, Just len <- fromUnit j =
    extendVals [(v, IntV $ interval start (start+len-1 :: Integer))] k

rangeFor v _v_start _v_len k =
    extendVals [(v, top)] k
