{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.ReadWriteSet
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.ReadWriteSet (
    IntV(..),
    RWSet(..),
    weaklyUpdated,

    readWriteSets
  ) where

import qualified Prelude as P
import Prelude hiding ((<=))

import Control.Monad (void)
import Control.Monad.Exception (MonadException(..))
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
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
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland hiding (empty)
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Interval
import KZC.Analysis.Lattice
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Fuel
import KZC.Platform
import KZC.Util.Env
import KZC.Util.Error
import KZC.Util.Pretty
import KZC.Util.Trace
import KZC.Util.Uniq

readWriteSets :: MonadTc m
              => Exp
              -> m (Map Var RWSet)
readWriteSets e = do
    s <- execRW (evalExp e)
    return $ rwsets s

-- | An interval. We track both a bounded interval containing all the values the
-- integer /may/ have at some point during execution and a precise interval that
-- contains all the values the integer /does/ have at some point during
-- execution.
data IntV = IV BoundedInterval PreciseInterval
  deriving (Eq, Ord, Show)

instance Pretty IntV where
    pprPrec p (IV bi pi) =
        parensIf (p > appPrec) $
        text "int" <+> ppr bi <+> ppr pi

instance IsInterval IntV where
    empty = IV empty empty

    unit i = IV (unit i) (unit i)

    fromUnit (IV i j) = do
        x <- fromUnit i
        y <- fromUnit j
        if x == y then return x else fail "Inconsistent intervals"

    interval i j = IV (interval i j) (interval i j)

    fromInterval (IV i j) = do
        x <- fromInterval i
        y <- fromInterval j
        if x == y then return x else fail "Inconsistent intervals"

    extend (IV i j) x = IV (extend i x) (extend j x)

instance Poset IntV where
    IV bi pi <= IV bi' pi' = bi <= bi' && pi <= pi'

instance Lattice IntV where
    IV bi pi `lub` IV bi' pi' = IV (bi `lub` bi') (pi `lub` pi')

    IV bi pi `glb` IV bi' pi' = IV (bi `glb` bi') (pi `glb` pi')

instance BottomLattice IntV where
    bot = IV bot bot

instance TopLattice IntV where
    top = IV top top

instance BoundedLattice IntV where

instance BranchLattice IntV where
    IV bi pi `bub` IV bi' pi' = IV (bi `bub` bi') (pi `bub` pi')

-- | A type that represents a set of fields.
class IsFields a where
    field :: Field -> a
    fields :: [Field] -> a

instance IsFields Fields where
    field  = Fields . Set.singleton
    fields = Fields . Set.fromList

instance IsFields a => IsFields (Top a) where
    field  = NotTop . field
    fields = NotTop . fields

-- | A set of fields.
newtype Fields = Fields (Set Field)
  deriving (Eq, Ord, Show, Poset, Lattice, BottomLattice)

instance Pretty Fields where
    ppr (Fields fs) = (braces . commasep . map ppr . Set.toList) fs

-- | A bounded set of fields.
newtype BoundedFields = BF (Top Fields)
  deriving (Eq, Ord, Show, Pretty, Poset, Lattice,
            BottomLattice, TopLattice, BoundedLattice,
            IsFields)

instance BranchLattice BoundedFields where
    bub = lub

-- | A precise set of fields.
newtype PreciseFields = PF (Top Fields)
  deriving (Eq, Ord, Show, Pretty, Poset, Lattice,
            BottomLattice, TopLattice, BoundedLattice,
            IsFields)

instance BranchLattice PreciseFields where
    i `bub` j | i == j    = i
              | otherwise = top

-- | A read/write set.
data RWSet = UnknownRW
           | VarRW All All
           | ArrayRW BoundedInterval PreciseInterval
           | StructRW BoundedFields PreciseFields
           | TopRW
  deriving (Eq, Ord, Show)

-- | Returns 'True' if the given read/write set is weakly, rather than
-- precisely, updated.
weaklyUpdated :: RWSet -> Bool
weaklyUpdated UnknownRW            = True
weaklyUpdated VarRW{}              = False
weaklyUpdated (ArrayRW _ (PI i))   = i == top
weaklyUpdated (StructRW _ (PF fs)) = fs == top
weaklyUpdated TopRW                = True

instance Pretty RWSet where
    ppr UnknownRW      = botDoc
    ppr (VarRW r w)    = text "var" <+> pprPrec appPrec1 r <+>pprPrec appPrec1 w
    ppr (ArrayRW r w)  = text "array" <+> pprPrec appPrec1 r <+>pprPrec appPrec1 w
    ppr (StructRW r w) = text "struct" <+> pprPrec appPrec1 r <+>pprPrec appPrec1 w
    ppr TopRW          = topDoc

instance Poset RWSet where
    UnknownRW    <= _              = True
    _            <= TopRW          = True
    VarRW r w    <= VarRW r' w'    = r <= r' && w <= w'
    ArrayRW r w  <= ArrayRW r' w'  = r <= r' && w <= w'
    StructRW r w <= StructRW r' w' = r <= r' && w <= w'
    _            <= _              = False

instance Lattice RWSet where
    UnknownRW     `lub` x              = x
    x             `lub` UnknownRW      = x
    VarRW r w     `lub` VarRW r' w'    = VarRW (r `lub` r') (w `lub` w')
    ArrayRW r w   `lub` ArrayRW r' w'  = ArrayRW (r `lub` r') (w `lub` w')
    StructRW r  w `lub` StructRW r' w' = StructRW (r `lub` r') (w `lub` w')
    _             `lub` _              = top

    UnknownRW    `glb` x              = x
    x            `glb` UnknownRW      = x
    VarRW r w    `glb` VarRW r' w'    = VarRW (r `glb` r') (w `glb` w')
    ArrayRW r w  `glb` ArrayRW r' w'  = ArrayRW (r `glb` r') (w `glb` w')
    StructRW r w `glb` StructRW r' w' = StructRW (r `glb` r') (w `glb` w')
    _            `glb` _              = bot

-- When calculating branch upper bounds, unknown values get mapped to bottom.
-- However, we need extra precision to correctly compute the MUST values of
-- field sets and intervals.
instance BranchLattice RWSet where
    UnknownRW   `bub` UnknownRW    = UnknownRW
    x           `bub` UnknownRW    = UnknownRW `bub` x
    UnknownRW   `bub` x@VarRW{}    = VarRW bot bot `bub` x
    UnknownRW   `bub` x@ArrayRW{}  = ArrayRW bot bot `bub` x
    UnknownRW   `bub` x@StructRW{} = StructRW bot bot `bub` x
    UnknownRW   `bub` x            = x

    VarRW r w    `bub` VarRW r' w'    = VarRW (r `bub` r') (w `bub` w')
    ArrayRW r w  `bub` ArrayRW r' w'  = ArrayRW (r `bub` r') (w `bub` w')
    StructRW r w `bub` StructRW r' w' = StructRW (r `bub` r') (w `bub` w')
    _            `bub` _              = top

instance BottomLattice RWSet where
    bot = UnknownRW

instance TopLattice RWSet where
    top = TopRW

instance BoundedLattice RWSet where

-- | Abstract values that represent read/write set.
class ReadWriteSet a b | a -> b, b -> a where
    inPrecise :: a -> b -> Bool

instance ReadWriteSet BoundedInterval PreciseInterval where
    inPrecise (BI x) (PI y) = x <= y

instance ReadWriteSet BoundedFields PreciseFields where
    inPrecise (BF x) (PF y) = x <= y

-- | Values
data Val = UnknownV           -- ^ Unknown (not-yet defined)
         | IntV IntV          -- ^ Interval bound on the value
         | BoolV (Known Bool) -- ^ Booleans
         | TopV               -- ^ Could be anything as far as we know...
  deriving (Eq, Ord, Show)

instance Pretty Val where
    ppr UnknownV  = botDoc
    ppr (IntV x)  = ppr x
    ppr (BoolV x) = ppr x
    ppr TopV      = topDoc

instance Poset Val where
    UnknownV <= _        = True
    _        <= TopV     = True
    IntV bi  <= IntV bi' = bi <= bi'
    BoolV b  <= BoolV b' = b <= b'
    _        <= _        = False

instance Lattice Val where
    UnknownV `lub` x        = x
    x        `lub` UnknownV = x
    IntV bi  `lub` IntV bi' = IntV (bi `lub` bi')
    BoolV b  `lub` BoolV b' = BoolV (b `lub` b')
    _        `lub` _        = top

    TopV    `glb` x        = x
    x       `glb` TopV     = x
    IntV bi `glb` IntV bi' = IntV (bi `glb` bi')
    BoolV b `glb` BoolV b' = BoolV (b `glb` b')
    _       `glb` _        = bot

instance BranchLattice Val where
    UnknownV `bub` UnknownV = UnknownV
    x        `bub` UnknownV = UnknownV `bub` x
    UnknownV `bub` x@IntV{} = IntV bot `bub` x
    UnknownV `bub` x        = x

    IntV bi  `bub` IntV bi' = IntV (bi `bub` bi')
    BoolV b  `bub` BoolV b' = BoolV (b `lub` b')
    _        `bub` _        = top

instance BottomLattice Val where
    bot = UnknownV

instance TopLattice Val where
    top = TopV

instance BoundedLattice Val where

data REnv = REnv { views :: Map Var View }
  deriving (Eq)

defaultREnv :: REnv
defaultREnv = REnv { views = mempty }

-- | The read-write set analysis state
data RState = RState
    { vals   :: Map Var Val   -- Variable values
    , rwsets :: Map Var RWSet -- Variable read/write sets
    }
  deriving (Eq)

defaultRState :: RState
defaultRState = RState
    { vals   = mempty
    , rwsets = mempty
    }

instance Pretty RState where
    ppr s = ppr (vals s) </> ppr (rwsets s)

instance Poset RState where
    r1 <= r2 = vals r1 <= vals r2 && rwsets r1 <= rwsets r2

instance Lattice RState where
    r1 `lub` r2 = RState
        { vals   = vals r1 `lub` vals r2
        , rwsets = rwsets r1 `lub` rwsets r2
        }

    r1 `glb` r2 = RState
        { vals   = vals r1 `glb` vals r2
        , rwsets = rwsets r1 `glb` rwsets r2
        }

instance BranchLattice RState where
    r1 `bub` r2 = RState
        { vals   = vals r1 `bub` vals r2
        , rwsets = rwsets r1 `bub` rwsets r2
        }

newtype RW m a = RW { unRW :: ReaderT REnv (StateT RState m) a }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadFail
             , MonadIO
             , MonadReader REnv
             , MonadState RState
             , MonadException
             , MonadUnique
             , MonadErr
             , MonadConfig
             , MonadFuel
             , MonadPlatform
             , MonadTrace
             , MonadTc)

execRW :: MonadTc m => RW m a -> m RState
execRW m = execStateT (runReaderT (unRW m) defaultREnv) defaultRState

instance MonadTrans RW where
    lift = RW . lift . lift

lookupView :: MonadTc m => Var -> RW m (Maybe View)
lookupView v = asks (Map.lookup v . views)

extendViews :: MonadTc m
            => [(Var, View)]
            -> RW m a
            -> RW m a
extendViews = extendEnv views (\env x -> env { views = x })

collectState :: MonadTc m => RW m a -> RW m (a, RState)
collectState m = do
    pre  <- get
    x    <- m
    post <- get
    put pre
    return (x, post)

lookupVal :: MonadTc m => Var -> RW m Val
lookupVal v = fromMaybe bot <$> gets (Map.lookup v . vals)

extendVals :: forall a m . MonadTc m => [(Var, Val)] -> RW m a -> RW m a
extendVals vvals m = do
    old_vals   <- gets $ \s -> map (\v -> Map.lookup v (vals s)) vs
    old_rwsets <- gets $ \s -> map (\v -> Map.lookup v (rwsets s)) vs
    modify $ \s -> s { vals = foldl' insert (vals s) vvals }
    x <- m
    -- We restore the old values here. This may mean deleting values, which is
    -- why we must use update.
    modify $ \s -> s { vals   = foldl' update (vals s) (vs `zip` old_vals)
                     , rwsets = foldl' update (rwsets s) (vs `zip` old_rwsets)
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
putVal v val = modify $ \s -> s { vals = Map.insert v val (vals s) }

lookupRWSet :: MonadTc m => Var -> RW m RWSet
lookupRWSet v = do
    maybe_ref <- gets (Map.lookup v . rwsets)
    case maybe_ref of
      Just rws -> return rws
      Nothing  -> do rws <- newRWSet . unRefT <$> lookupVar v
                     putRWSet v rws
                     return rws
  where
    newRWSet :: Type -> RWSet
    newRWSet ArrT{}    = ArrayRW bot bot
    newRWSet StructT{} = StructRW bot bot
    newRWSet _         = VarRW bot bot

putRWSet :: MonadTc m => Var -> RWSet -> RW m ()
putRWSet v rws = modify $ \s -> s { rwsets = Map.insert v rws (rwsets s) }

fromLen :: Maybe Int -> Int
fromLen Nothing    = 1
fromLen (Just len) = len

{- Note [Read/write Sets]

We track read/write sets at the granularity of individual array elements and
individual struct fields. In both cases, we track both bounded and precise sets
(of array elements/fields) so that we can potentially determine the precise
parts of an array/struct that are read.

When tracking precise sets, we are careful not to push a write set stright to
top when we assign an entire array/struct, becase top in a precise tracking
context means that stuff is written, but we can't determien precisely what!
Instead, we explicitly add all elements of the array/struct to the write set.
-}

data Ref = Ref Var [RefPath]
  deriving (Eq, Ord)

data RefPath = IdxP Val (Maybe Int)
             | ProjP Field
  deriving (Eq, Ord)

evalRef :: forall m . MonadTc m => Exp -> RW m Ref
evalRef = go []
  where
    go :: [RefPath] -> Exp -> RW m Ref
    go path (VarE v _) = do
        maybe_view <- lookupView v
        case maybe_view of
          Nothing   -> return $ Ref v path
          Just view -> go path (toExp view)

    -- We combine ref paths involving indexing into a slice.
    go (IdxP val0 len : path) (IdxE e1 e2 Just{} _) = do
        val <- evalExp e2
        go (IdxP (addVals val0 val) len : path) e1

    go path (IdxE e1 e2 Nothing _) = do
        val <- evalExp e2
        go (IdxP val Nothing : path) e1

    go path (IdxE e1 e2 (Just (NatT len _)) _) = do
        val <- evalExp e2
        go (IdxP val (Just len) : path) e1

    go path (IdxE e1 _ _ _) = do
        go path e1

    go path (ProjE e f _) =
        go (ProjP f : path) e

    go _ e =
        faildoc $ text "Not a reference:" <+> ppr e

    addVals :: Val -> Val -> Val
    addVals (IntV x) (IntV y) | Just (x1, x2) <- fromInterval x,
                                Just (y1, y2) <- fromInterval y =
        IntV $ interval (x1 + y1 :: Integer) (x2 + y2 :: Integer)

    addVals _ _ =
        top

readRef :: forall m .  MonadTc m => Ref -> RW m ()
readRef (Ref v path) = do
    rws  <- lookupRWSet v
    rws' <- go rws path
    putRWSet v rws'
  where
    go :: RWSet -> [RefPath] -> RW m RWSet
    -- We're reading the entire array. Rather than sending the read set to top,
    -- we send it to the interval that includes all elements.
    go ref@(ArrayRW _rs ws) [] = do
        (nat, _) <- lookupVar v >>= checkArrOrRefArrT
        case nat of
          NatT n _ -> do let rs :: BoundedInterval
                             rs = extend (unit (0::Integer)) n
                         if rs `inPrecise` ws
                           then return ref
                           else return $ ArrayRW rs ws
          _        -> return $ ArrayRW top ws

    go ref@(ArrayRW rs ws) (IdxP (IntV (IV bi _pi)) len:_)
      | new `inPrecise` ws = return ref
      | otherwise          = return $ ArrayRW (rs `lub` new) ws
      where
        new :: BoundedInterval
        new = extend bi (fromLen len)

    go (ArrayRW _rs ws) _ =
        return $ ArrayRW top ws

    go ref@(StructRW _rs ws) [] = do
        (struct, taus) <- lookupVar v >>= checkStructOrRefStructT
        flds           <- tyAppStruct struct taus
        let rs :: BoundedFields
            rs = fields (map fst flds)
        if rs `inPrecise` ws
          then return ref
          else return $ StructRW rs ws

    go ref@(StructRW rs ws) (ProjP f:_)
      | new `inPrecise` ws = return ref
      | otherwise          = return $ StructRW (rs `lub` new) ws
      where
        new :: BoundedFields
        new = field f

    go (StructRW _rs ws) _ =
        return $ StructRW top ws

    go ref@(VarRW _rs ws) _
        | ws == top = return ref
        | otherwise = return $ VarRW top ws

    go UnknownRW _ =
        return TopRW

    go TopRW _ =
        return TopRW

writeRef :: forall m .  MonadTc m => Ref -> RW m ()
writeRef (Ref v path) = do
    rws  <- lookupRWSet v
    rws' <- go rws path
    putRWSet v rws'
  where
    go :: RWSet -> [RefPath] -> RW m RWSet
    -- We're writing the entire array. As above, rather than sending the write
    -- set to top, we send it to the interval that includes all elements.
    go (ArrayRW rs _ws) [] = do
        (nat, _) <- lookupVar v >>= checkArrOrRefArrT
        case nat of
          NatT n _ -> do let ws :: PreciseInterval
                             ws = extend (unit (0::Integer)) n
                         return $ ArrayRW rs ws
          _        -> return $ ArrayRW rs top

    go (ArrayRW rs ws) [IdxP (IntV (IV _bi pi)) len] =
        return $ ArrayRW rs (ws `lub` ws')
      where
        ws' :: PreciseInterval
        ws' = extend pi (fromLen len)

    go (ArrayRW rs _ws) _ =
        return $ ArrayRW rs top

    go (StructRW rs _) [] = do
        (struct, taus) <- lookupVar v >>= checkStructOrRefStructT
        flds           <- tyAppStruct struct taus
        let ws :: PreciseFields
            ws  = fields (map fst flds)
        return $ StructRW rs ws

    go (StructRW rs ws) [ProjP f] =
        return $ StructRW rs (ws `lub` field f)

    go (StructRW rs _ws) _ =
        return $ StructRW rs top

    go (VarRW rs _ws) _ =
        return $ VarRW rs top

    go UnknownRW _ =
        return TopRW

    go TopRW _ =
        return TopRW

evalExp :: forall m . MonadTc m => Exp -> RW m Val
evalExp e =
    withFvContext e $
    go e
  where
    go :: Exp -> RW m Val
    go (ConstE c _) =
        return $ evalConst c
      where
        evalConst :: Const -> Val
        evalConst (BoolC b)  = BoolV (pure b)
        evalConst (IntC _ i) = IntV $ unit i
        evalConst _c         = top

    go e@(VarE v _) = do
        evalRef e >>= readRef
        lookupVal v

    go (UnopE op e _) =
        unop op <$> go e
      where
        unop :: Unop -> Val -> Val
        unop Lnot (BoolV b)         = BoolV $ not <$> b
        unop Lnot _                 = BoolV top
        unop Bnot (IntV _)          = IntV top
        unop Bnot _                 = top
        unop Neg (IntV i)
            | Just x <- fromUnit i  = IntV $ unit (negate x :: Integer)
        unop Neg _                  = top
        unop Len _                  = IntV top
        unop _ _                    = top

    go (BinopE op e1 e2 _) =
        binop op <$> go e1 <*> go e2
      where
        binop :: Binop -> Val -> Val -> Val
        binop Eq (IntV i) (IntV j) = BoolV . Known $ i == j
        binop Ne (IntV i) (IntV j) = BoolV . Known $ i /= j

        binop Lt (IntV i) (IntV j) = BoolV . Known $ i < j
        binop Le (IntV i) (IntV j) = BoolV . Known $ i P.<= j
        binop Ge (IntV i) (IntV j) = BoolV . Known $ i >= j
        binop Gt (IntV i) (IntV j) = BoolV . Known $ i > j

        binop Eq _ _ = BoolV top
        binop Ne _ _ = BoolV top

        binop Lt _ _ = BoolV top
        binop Le _ _ = BoolV top
        binop Ge _ _ = BoolV top
        binop Gt _ _ = BoolV top

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

        binop Add (IntV x) (IntV y) | Just (x1, x2) <- fromInterval x,
                                      Just (y1, y2) <- fromInterval y =
            IntV $ interval (x1 + y1 :: Integer) (x2 + y2 :: Integer)

        binop Sub (IntV x) (IntV y) | Just (x1, x2) <- fromInterval x,
                                      Just (y1, y2) <- fromInterval y =
            IntV $ interval (x1 - y2 :: Integer) (x2 - y1 :: Integer)

        binop Mul (IntV x) (IntV y) | Just (x1, x2) <- fromInterval x,
                                      Just (y1, y2) <- fromInterval y =
            IntV $ interval (x1 * y1 :: Integer) (x2 * y2 :: Integer)

        binop Div (IntV x) (IntV y) | Just (x1, x2) <- fromInterval x,
                                      Just (y1, y2) <- fromInterval y =
            IntV $ interval (min (x1 `quot` y2 :: Integer)
                                 (y1 `quot` x2 :: Integer))
                            (max (x2 `quot` y1 :: Integer)
                                 (y2 `quot` x1 :: Integer))

        binop Add _ _ = top
        binop Sub _ _ = top
        binop Mul _ _ = top
        binop Div _ _ = top
        binop Rem _ _ = top
        binop Pow _ _ = top
        binop Cat _ _ = top

    go (IfE e1 e2 e3 _) = do
        val1 <- evalExp e1
        evalIf val1 (evalExp e2) (evalExp e3)

    go (LetE (LetLD v tau e1 _) e2 _) = do
        val1 <- evalExp e1
        extendVars [(bVar v, tau)] $
          extendVals [(bVar v, val1)] $
          evalExp e2

    go (LetE (LetRefLD v tau Nothing _) e2 _) =
        extendVars [(bVar v, refT tau)] $
        extendVals [(bVar v, bot)] $
        evalExp e2

    go (LetE (LetRefLD v tau (Just e1) _) e2 _) = do
        val1 <- evalExp e1
        extendVars [(bVar v, refT tau)] $
            extendVals [(bVar v, val1)] $
            evalExp e2

    go (LetE (LetTypeLD alpha kappa tau _) e _) =
        extendTyVars [(alpha, kappa)] $
        extendTyVarTypes [(alpha, tau)] $
        evalExp e

    go (LetE (LetViewLD v tau view _) e2 _) =
        extendVars [(bVar v, tau)] $
        extendViews [(bVar v, view)] $
        evalExp e2

    go (CallE f _taus es _) = do
        isExt <- isExtFun f
        mapM_ (evalArg isExt) es
        return top
      where
        -- We assume that ref arguments to an external function are written. For
        -- a non-external function, we treat ref arguments as being both read
        -- and written.
        evalArg :: Bool -> Exp -> RW m ()
        evalArg isExt e = do
            tau <- inferExp e
            case tau of
              RefT {} | isExt     -> evalRef e >>= writeRef
                      | otherwise -> do ref <- evalRef e
                                        readRef ref
                                        writeRef ref
              _                   -> void $ evalExp e

    go (DerefE e _) = do
        evalRef e >>= readRef
        case e of
          VarE v _ -> lookupVal v
          _        -> return top

    go (AssignE e1 e2 _) = do
        val <- evalExp e2
        evalRef e1 >>= writeRef
        case e1 of
          VarE v _ -> putVal v val
          _        -> return ()
        return top

    go (LowerE tau _) = do
        n <- evalNat tau
        return $ IntV $ unit n

    go (WhileE e1 e2 _) = do
        val <- evalExp e1
        evalWhile val $
          evalExp e2

    go (ForE _ v tau gint e_body _) = do
        v_start <- evalExp e_start
        v_len   <- evalExp e_len
        extendVars [(v, tau)] $
          evalFor v v_start v_len (evalExp e_body)
      where
        e_start, e_len :: Exp
        (e_start, e_len) = toStartLenGenInt gint

    go (ArrayE es _) = do
        mapM_ evalExp es
        return top

    go e@(IdxE VarE{} _ _ _) = do
        evalRef e >>= readRef
        return top

    go (IdxE e1 e2 _ _) = do
        void $ evalExp e1
        void $ evalExp e2
        return top

    go (StructE _ _ flds _) = do
        mapM_ (go . snd) flds
        return top

    go e@(ProjE VarE{} _ _) = do
        evalRef e >>= readRef
        return top

    go (ProjE e _ _) = do
        void $ evalExp e
        return top

    go (CastE tau e _) =
        cast tau <$> evalExp e
      where
        cast :: Type -> Val -> Val
        -- XXX not quite correct since we don't actually cast.
        cast IntT{} v@IntV{} = v
        cast IntT{} _        = IntV top
        cast _      _        = top

    go (BitcastE tau e _) =
        bitcast tau <$> evalExp e
      where
        bitcast :: Type -> Val -> Val
        bitcast IntT{} _ = IntV top
        bitcast _      _ = top

    go (PrintE _ es _) = do
        mapM_ evalExp es
        return top

    go ErrorE{} =
        return top

    go (ReturnE _ e _) =
        evalExp e

    go (BindE wv tau e1 e2 _) = do
        val1 <- evalExp e1
        extendWildVars [(wv, tau)] $
          extendWildVals [(wv, val1)] $
          evalExp e2

    go (LutE _ e) =
        go e

    go GenE{} =
        return top

evalIf :: (BranchLattice a, MonadTc m)
        => Val
        -> RW m a
        -> RW m a
        -> RW m a
evalIf (BoolV (Known True)) k2 _k3 =
    k2

evalIf (BoolV (Known False)) _k2 k3 =
    k3

evalIf _ k2 k3 = do
    (val2, post2) <- collectState k2
    (val3, post3) <- collectState k3
    put $ post2 `bub` post3
    return $ val2 `bub` val3

evalWhile :: (BoundedLattice a, MonadTc m)
           => Val
           -> RW m a
           -> RW m a
evalWhile (BoolV (Known False)) k =
    k

evalWhile _ k = do
    void k
    return top

evalFor :: MonadTc m => Var -> Val -> Val -> RW m a -> RW m a
evalFor v (IntV i) (IntV j) k | Just start <- fromUnit i, Just len <- fromUnit j =
    extendVals [(v, IntV $ interval (start::Integer) (start + len - 1))] k

evalFor v _v_start _v_len k =
    extendVals [(v, top)] k
