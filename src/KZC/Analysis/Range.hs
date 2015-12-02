{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Range
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.Range (
    R,
    runR,

    varRanges
  ) where

import qualified Prelude as P
import Prelude hiding ((<=))

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad (void)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            gets,
                            modify)
import Control.Monad.Trans (MonadTrans(..))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Ratio (numerator)

import KZC.Analysis.Abs
import KZC.Auto.Lint
import KZC.Auto.Syntax hiding (PI)
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice

varRanges :: MonadTc m => Exp -> m (Val, Map Var Val)
varRanges e = do
    (val, s) <- runR (absEval e)
    return (val, vals s)

class Interval a where
    empty     :: a
    singleton :: Integral i => i -> a
    range     :: Integral i => i -> i -> a

data Intv = EmptyI
          -- | Invariant: @'IntI' i1 i2@ iff @i1@ <= @i2@.
          | IntI Integer Integer
  deriving (Eq, Ord, Show)

instance Poset Intv where
    EmptyI   <= _          = True
    IntI i j <= IntI i' j' = i' <= i && j <= j'
    _        <= _          = False

instance Lattice Intv where
    EmptyI   `lub` i          = i
    i        `lub` EmptyI     = i
    IntI i j `lub` IntI i' j' = IntI l h
      where
        l = min i i'
        h = max j j'

    EmptyI   `glb` _          = EmptyI
    _        `glb` EmptyI     = EmptyI
    IntI i j `glb` IntI i' j'
        | gap                 = EmptyI
        | otherwise           = IntI l h
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 || i' - j > 1

newtype BoundedInterval = BI (Known Intv)
  deriving (Eq, Ord, Show, Poset, Lattice, BoundedLattice)

instance Interval BoundedInterval where
    empty       = BI (Known EmptyI)
    singleton i = BI (Known (IntI (fromIntegral i) (fromIntegral i)))
    range i j   = BI (Known (IntI (fromIntegral i) (fromIntegral j)))

newtype PreciseInterval = PI (Known Intv)
  deriving (Eq, Ord, Show, Poset)

instance Lattice PreciseInterval where
    i `lub` j | i <= j = j
              | j <= i = i

    PI (Known (IntI i j)) `lub` PI (Known (IntI i' j'))
        | gap       = top
        | otherwise = PI (Known (IntI l h))
      where
        l   = min i i'
        h   = max j j'
        gap = i - j' > 1 || i' - j > 1

    _ `lub` _ = top

    i `glb` j | i <= j = i
              | j <= i = j

    PI (Known (IntI i j)) `glb` PI (Known (IntI i' j'))
        | gap       = bot
        | l == h    = PI (Known EmptyI)
        | otherwise = PI (Known (IntI l h))
      where
        l   = max i i'
        h   = min j j'
        gap = i - j' > 1 || i' - j > 1

    _ `glb` _ = bot

instance BoundedLattice PreciseInterval where
    top = PI top
    bot = PI bot

instance Interval PreciseInterval where
    empty       = PI (Known EmptyI)
    singleton i = PI (Known (IntI (fromIntegral i) (fromIntegral i)))
    range i j   = PI (Known (IntI (fromIntegral i) (fromIntegral j)))

data Val = UnknownV                               -- ^ Unknown (not-yet defined)
         | IntV (Known Integer)                   -- ^ Integers
         | BoolV (Known Bool)                     -- ^ Booleans
         | ArrayV BoundedInterval PreciseInterval -- ^ Array read/write sets
         | TopV                                   -- ^ Could be anything as far
                                                  -- as we know...
  deriving (Eq, Ord, Show)

instance Poset Val where
    UnknownV     <= _              = True
    _            <= TopV           = True
    IntV bi      <= IntV bi'       = bi <= bi'
    BoolV b      <= BoolV b'       = b <= b'
    ArrayV rs ws <= ArrayV rs' ws' = rs <= rs' && ws <= ws'
    _            <= _              = False

instance Lattice Val where
    IntV bi      `lub` IntV bi'       = IntV (bi `lub` bi')
    BoolV b      `lub` BoolV b'       = BoolV (b `lub` b')
    ArrayV rs ws `lub` ArrayV rs' ws' = ArrayV (rs `lub` rs') (ws `lub` ws')
    _            `lub` _              = top

    IntV bi      `glb` IntV bi'       = IntV (bi `glb` bi')
    BoolV b      `glb` BoolV b'       = BoolV (b `glb` b')
    ArrayV rs ws `glb` ArrayV rs' ws' = ArrayV (rs `glb` rs') (ws `glb` ws')
    _            `glb` _              = bot

instance BranchLattice Val where
    IntV bi      `bub` IntV bi'       = IntV (bi `lub` bi')
    BoolV b      `bub` BoolV b'       = BoolV (b `lub` b')
    ArrayV rs ws `bub` ArrayV rs' ws' = ArrayV (rs `lub` rs') (ws `glb` ws')
    _            `bub` _              = top

instance BoundedLattice Val where
    top = TopV
    bot = UnknownV

data RState = RState
    { ivals :: Map IVar Val
    , vals  :: Map Var  Val
    }

defaultRState :: RState
defaultRState = RState
    { ivals = mempty
    , vals  = mempty
    }

instance Poset RState where
    r1 <= r2 = ivals r1 <= ivals r2 && vals r1 <= vals r2

instance Lattice RState where
    r1 `lub` r2 = RState
        { ivals = ivals r1 `lub` ivals r2
        , vals  = vals r1  `lub` vals r2
        }

    r1 `glb` r2 = RState
        { ivals = ivals r1 `glb` ivals r2
        , vals  = vals r1  `glb` vals r2
        }

instance BranchLattice RState where
    r1 `bub` r2 = RState
        { ivals = ivals r1 `bub` ivals r2
        , vals  = vals r1  `bub` vals r2
        }

newtype R m a = R { unR :: StateT RState m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState RState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

runR :: MonadTc m => R m a -> m (a, RState)
runR m = runStateT (unR m) defaultRState

instance MonadTrans R where
    lift = R . lift

extend :: forall m k v a . (MonadTc m, Ord k)
       => (RState -> Map k v)
       -> (RState -> Map k v -> RState)
       -> [(k, v)]
       -> R m a
       -> R m a
extend _ _ [] m = m

extend proj upd kvs m = do
    maybe_vs <- mapM lookup (map fst kvs)
    modify $ \env -> upd env (foldl' insert (proj env) kvs)
    x <- m
    modify $ \env -> upd env (foldl' update (proj env) (map fst kvs `zip` maybe_vs))
    return x
  where
    lookup :: k -> R m (Maybe v)
    lookup k = gets (Map.lookup k . proj)

    insert :: Ord k => Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

    update :: Ord k => Map k v -> (k, Maybe v) -> Map k v
    update mp (k, v) = Map.update (const v) k mp

lookupIVal :: MonadTc m => IVar -> R m Val
lookupIVal iv =
    maybe (IntV Unknown) id <$> gets (Map.lookup iv . ivals)

{-
extendIVals :: MonadTc m => [(IVar, Val)] -> R m a -> R m a
extendIVals ivs m = extend ivals (\env x -> env { ivals = x }) ivs m
-}

lookupVal :: MonadTc m => Var -> R m Val
lookupVal v = do
    tau <- lookupVar v
    maybe (typeTop tau) id <$> gets (Map.lookup v . vals)

extendVals :: MonadTc m => [(Var, Val)] -> R m a -> R m a
extendVals vs m = extend vals (\env x -> env { vals = x }) vs m

updateVal :: MonadTc m => Var -> Val -> R m Val
updateVal v val = do
    val' <- lub <$> lookupVal v <*> pure val
    modify $ \s -> s { vals = Map.insert v val' (vals s) }
    return val'

sliceToInterval :: (Interval a, BoundedLattice a)
                => Val -> Maybe Int -> a
sliceToInterval (IntV (Known i)) Nothing    = singleton i
sliceToInterval (IntV (Known i)) (Just len) = range i (i+fromIntegral len-1)
sliceToInterval _                _          = top

typeTop :: Type -> Val
typeTop (BoolT {})              = BoolV top
typeTop (FixT I _s _w (BP 0) _) = IntV top
typeTop (ArrT {})               = ArrayV empty empty
typeTop _                       = top

instance ValDom Val where
    constDom (BoolC b)               = BoolV (pure b)
    constDom (FixC I _s _w (BP 0) r) = IntV $ Known (numerator r)
    constDom _c                      = top

    unopDom Lnot (BoolV b)                      = BoolV $ not <$> b
    unopDom Lnot _                              = BoolV top
    unopDom Bnot (IntV _)                       = IntV top
    unopDom Bnot _                              = top
    unopDom Neg (IntV i)                        = IntV $ negate <$> i
    unopDom Neg _                               = top
    unopDom (Cast (FixT I _s _w (BP 0) _)) _    = IntV top
    unopDom (Cast {}) _                         = top
    unopDom (Bitcast (FixT I _s _w (BP 0) _)) _ = IntV top
    unopDom (Bitcast {}) _                      = top
    unopDom Len _                               = IntV top

    binopDom Lt (IntV i) (IntV j) = BoolV $ (<) <$> i <*> j
    binopDom Le (IntV i) (IntV j) = BoolV $ (P.<=) <$> i <*> j
    binopDom Eq (IntV i) (IntV j) = BoolV $ (==) <$> i <*> j
    binopDom Ge (IntV i) (IntV j) = BoolV $ (>=) <$> i <*> j
    binopDom Gt (IntV i) (IntV j) = BoolV $ (>) <$> i <*> j
    binopDom Ne (IntV i) (IntV j) = BoolV $ (/=) <$> i <*> j

    binopDom Lt _ _ = BoolV top
    binopDom Eq _ _ = BoolV top
    binopDom Le _ _ = BoolV top
    binopDom Ge _ _ = BoolV top
    binopDom Gt _ _ = BoolV top
    binopDom Ne _ _ = BoolV top

    binopDom Land (BoolV b) (BoolV b') = BoolV $ (&&) <$> b <*> b'
    binopDom Lor  (BoolV b) (BoolV b') = BoolV $ (||) <$> b <*> b'

    binopDom Land _ _ = BoolV top
    binopDom Lor  _ _ = BoolV top

    binopDom Band _ _ = top
    binopDom Bor  _ _ = top
    binopDom Bxor _ _ = top

    binopDom LshL _ _ = top
    binopDom LshR _ _ = top
    binopDom AshR _ _ = top

    binopDom Add (IntV i) (IntV j) = IntV $ (+) <$> i <*> j
    binopDom Sub (IntV i) (IntV j) = IntV $ (-) <$> i <*> j
    binopDom Mul (IntV i) (IntV j) = IntV $ (*) <$> i <*> j
    binopDom Div (IntV i) (IntV j) = IntV $ quot <$> i <*> j
    binopDom Rem (IntV i) (IntV j) = IntV $ rem <$> i <*> j

    binopDom Add _ _ = top
    binopDom Sub _ _ = top
    binopDom Mul _ _ = top
    binopDom Div _ _ = top
    binopDom Rem _ _ = top
    binopDom Pow _ _ = top

    arrayDom _vs = ArrayV empty empty

    idxDom tau _arr _idx _len = typeTop tau

    structDom _s _flds = top

    projDom tau _s _fld = typeTop tau

instance MonadTc m => MonadAbs RState Val Val (R m) where
    iotaDom (ConstI i _) = return $ IntV (Known (fromIntegral i))
    iotaDom (VarI iv _)  = lookupIVal iv

    varDom v = lookupVal v

    letDom v val body = extendVals [(v, val)] body

    letrefDom v body = extendVals [(v, bot)] body

    callDom _ _ _ = fail "call not supported in range analysis"

    derefDom r =
        updateReadSet r
      where
        updateReadSet :: Ref Val -> R m Val
        updateReadSet (VarR v) =
            lookupVar v >>= checkRefT >>= go
          where
            go :: Type -> R m Val
            go (ArrT iota _ _) = do
                val <- iotaDom iota
                case val of
                  IntV (Known n) -> updateVal v (ArrayV (range 0 (n-1)) bot)
                  _              -> updateVal v (ArrayV top bot)

            go _ =
                return top

        updateReadSet (IdxR (VarR v) idx len) =
            updateVal v (ArrayV (sliceToInterval idx len) bot)

        updateReadSet r@(IdxR r' _ _) = do
            void $ updateReadSet r'
            typeTop <$> inferRef r

        updateReadSet r@(ProjR r' _) = do
            void $ updateReadSet r'
            typeTop <$> inferRef r

    assignDom r _ =
        updateWriteSet r
      where
        updateWriteSet :: Ref Val -> R m ()
        updateWriteSet (VarR v) =
            lookupVar v >>= checkRefT >>= go
          where
            go :: Type -> R m ()
            go (ArrT iota _ _) = do
                val <- iotaDom iota
                case val of
                  IntV (Known n) -> void $ updateVal v (ArrayV bot (range 0 (n-1)))
                  _              -> void $ updateVal v (ArrayV bot top)

            go _ =
                return ()

        updateWriteSet (IdxR (VarR v) idx len) =
            void $ updateVal v (ArrayV bot (sliceToInterval idx len))

        updateWriteSet r =
            updateWriteSetTop r
          where
            updateWriteSetTop :: Ref Val -> R m ()
            updateWriteSetTop (VarR v) = do
                lookupVar v >>= checkRefT >>= go
              where
                go :: Type -> R m ()
                go (ArrT {}) =
                    void $ updateVal v (ArrayV bot top)

                go tau =
                    void $ updateVal v (typeTop tau)

            updateWriteSetTop (IdxR r _ _) =
                updateWriteSetTop r

            updateWriteSetTop (ProjR r _) =
                updateWriteSetTop r

    printDom _ _ = fail "print not supported in range analysis"
    errorDom     = fail "print not supported in range analysis"

    returnDom v = return v

    bindDom WildV     _   body = body
    bindDom (TameV v) val body = extendVals [(bVar v, val)] body

    ifDom av_cond m1 m2 =
        joinBranchA (withCond av_cond m1) (withCond (unopDom Lnot av_cond) m2)

    getA = get
    putA = put

    withCond (BoolV (Known True))  m = m
    withCond (BoolV (Known False)) _ = skipA
    withCond _                     m = m
