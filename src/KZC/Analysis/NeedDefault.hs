{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      :  KZC.Analysis.NeedDefault
Copyright   :  (c) 2016 Drexel University
License     :  BSD-style
Maintainer  :  mainland@cs.drexel.edu

Analyzes programs to determine which variables' default values are actually
used. In other words, determine if we need to implicitly initialize a variable
because it is used before the program explicitly initializes it.
-}

module KZC.Analysis.NeedDefault (
    defaultsUsedExp,

    needDefaultProgram
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (void,
                      when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

import KZC.Analysis.Lattice
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Pretty
import KZC.Trace
import KZC.Uniq
import KZC.Vars

data Range = Range Iota Iota
  deriving (Eq, Ord, Show)

-- | Construct a literal range of length 1.
unitR :: Integral a => a -> Range
unitR x = Range (constI x) (constI (1::Int))

fromUnitR :: Range -> Maybe Iota
fromUnitR (Range i (ConstI 1 _)) = Just i
fromUnitR _                      = Nothing

-- | Construct a symbolic range of length 1.
iotaR :: Iota -> Range
iotaR x = Range x (constI (1::Int))

-- | Construct a range with known, constant start and length.
rangeR :: Integral a => a -> a -> Range
rangeR i len = Range (constI i) (constI len)

-- | Union of two ranges only if it can be represented precisely.
unionR :: Range -> Range -> Maybe Range
unionR i j | i == j =
    Just i

unionR (Range i (ConstI len _)) (Range j (ConstI len' _)) | i == j =
    Just $ Range i (constI (min len len'))

unionR (Range (ConstI i _) (ConstI len _)) (Range (ConstI i' _) (ConstI len' _))
  | i  + len  == i' = Just $ rangeR i  (len+len')
  | i' + len' == i  = Just $ rangeR i' (len+len')

unionR _ _ =
    Nothing

-- | Intersection of two ranges only if it can be represented precisely.
intersectionR :: Range -> Range -> Maybe Range
intersectionR i j | i == j =
    Just i

intersectionR (Range i (ConstI len _)) (Range j (ConstI len' _)) | i == j =
    Just $ Range i (constI (max len len'))

intersectionR (Range (ConstI i _) (ConstI len _)) (Range (ConstI i' _) (ConstI len' _))
  | i  < i' && i + len  > i' = Just $ rangeR i' (i  + len  - i')
  | i' < i  && i'+ len' > i  = Just $ rangeR i  (i' + len' - i)

intersectionR _ _ =
    Nothing

instance Pretty Range where
    ppr (Range lo hi) = brackets $ commasep [ppr lo, ppr hi]

instance Poset Range where
    Range i (ConstI len _) <= Range j (ConstI len' _) | i == j =
        len <= len'

    Range (ConstI i _) (ConstI len _) <= Range (ConstI i' _) (ConstI len' _) =
        i' <= i && i + len <= i' + len'

    i <= j = i == j

-- | A precisely known range.
newtype PreciseRange = PR (Known Range)
  deriving (Eq, Ord, Show, Poset)

-- | Extend a precise range by a known length.
extendPR :: PreciseRange -> Maybe Int -> PreciseRange
extendPR (PR (Known (Range i (ConstI len _)))) (Just len') =
    PR $ Known $ Range i (constI (len+len'-1))

extendPR r _ =
     r

instance Pretty PreciseRange where
    ppr (PR rng) = ppr rng

-- This instance is why a 'PreciseRange' is different from a 'Known Range'---we
-- can do a better job calculating the lub and glb of a 'PreciseRange'.
instance Lattice PreciseRange where
    PR (Known i) `lub` PR (Known j) | Just k <- unionR i j =
        PR (Known k)

    i `lub` j | i <= j    = j
              | j <= i    = i
              | otherwise = top

    PR (Known i) `glb` PR (Known j) | Just k <- intersectionR i j =
        PR (Known k)

    i `glb` j | i <= j    = i
              | j <= i    = j
              | otherwise = bot

instance BottomLattice PreciseRange where
    bot = PR bot

instance TopLattice PreciseRange where
    top = PR top

instance BoundedLattice PreciseRange where

-- | An array value specifying which elements are certainly known.
data Array = Arr Iota PreciseRange
  deriving (Eq, Ord, Show)

instance Pretty Array where
    ppr (Arr n r) = text "arr" <> brackets (ppr n) <+> ppr r

instance Poset Array where
    Arr n i <= Arr n' j
      | n == n'   = i <= j
      | otherwise = error "Arrays have different sizes"

instance Lattice Array where
    Arr n i `lub` Arr n' j
      | n == n'   = Arr n (i `lub` j)
      | otherwise = error "Arrays have different sizes"

    Arr n i `glb` Arr n' j
      | n == n'   = Arr n (i `glb` j)
      | otherwise = error "Arrays have different sizes"

-- | An abstract value.
data Val -- | Unknown (not yet defined)
         = UnknownV
         -- | The variable takes on all values in the range, i.e., it may be a
         -- loop variable
         | IntV PreciseRange
         | ArrV Array
         | StructV (Map Field Val)
         -- | Could be anything as far as we know...
         | TopV
  deriving (Eq, Ord, Show)

intV :: Integral a => a -> Val
intV = IntV . PR . Known . unitR

iotaV :: Iota -> Val
iotaV = IntV . PR . Known . iotaR

rangeV :: Iota -> Iota -> Val
rangeV i len = IntV $ PR $ Known $ Range i len

fromUnitV :: Val -> Maybe Iota
fromUnitV (IntV (PR (Known r))) = fromUnitR r
fromUnitV _                     = Nothing

wholeArrV :: Iota -> Val
wholeArrV n = ArrV $ Arr n (PR $ Known $ Range (constI (0::Int)) n)

instance Pretty Val where
    ppr UnknownV       = text "unknown"
    ppr (IntV rng)     = ppr rng
    ppr (ArrV arr)     = ppr arr
    ppr (StructV flds) = pprStruct equals (Map.toList flds)
    ppr TopV           = text "top"

instance Poset Val where
    UnknownV  <= _        = True
    _         <= TopV     = True
    IntV x    <= IntV y    = x <= y
    ArrV x    <= ArrV y    = x <= y
    StructV x <= StructV y = x <= y
    _         <= _         = False

instance Lattice Val where
    UnknownV  `lub` x         = x
    x         `lub` UnknownV  = x
    IntV x    `lub` IntV y    = IntV (x `lub` y)
    ArrV x    `lub` ArrV y    = ArrV (x `lub` y)
    StructV x `lub` StructV y = StructV (x `lub` y)
    _         `lub` _         = top

    TopV      `glb` x         = x
    x         `glb` TopV      = x
    IntV x    `glb` IntV y    = IntV (x `glb` y)
    ArrV x    `glb` ArrV y    = ArrV (x `glb` y)
    StructV x `glb` StructV y = StructV (x `glb` y)
    _         `glb` _         = bot

instance BranchLattice Val where
    _         `bub` UnknownV  = UnknownV
    UnknownV  `bub` _         = UnknownV
    _         `bub` TopV      = TopV
    TopV      `bub` _         = TopV
    IntV x    `bub` IntV y    = IntV (x `glb` y)
    ArrV x    `bub` ArrV y    = ArrV (x `glb` y)
    StructV x `bub` StructV y = StructV (x `bub` y)
    _         `bub` _         = bot

instance BottomLattice Val where
    bot = UnknownV

instance TopLattice Val where
    top = TopV

instance BoundedLattice Val where

-- | Return 'True' when the value may be partial.
partial :: Type -> Val -> Bool
partial _   UnknownV           = True
partial _   (IntV i)          = i == bot
partial _   (ArrV (Arr n xs)) = ArrV (Arr n xs) /= wholeArrV n
-- XXX Should not assume struct field is not an array!
partial _   (StructV flds)    = any (partial intT) (Map.elems flds)
partial tau TopV              = isArrOrRefArrT tau

-- | Ensure that the given value is total.
ensureTotal :: Type -> Val -> Val
ensureTotal = go
  where
    go :: Type -> Val -> Val
    go (ArrT iota _ _)          _ = wholeArrV iota
    go (RefT (ArrT iota _ _) _) _ = wholeArrV iota

    go _ val | val == bot = top
             | otherwise  = val

data NDState = NDState
    { vals        :: !(Map Var Val)
    , usedDefault :: !(Set Var)
    }

instance Monoid NDState where
    mempty = NDState
        { vals        = mempty
        , usedDefault = mempty
        }

    x `mappend` y = NDState
        { usedDefault = usedDefault x <> usedDefault y
        , vals        = vals x <> vals y
        }

newtype ND m a = ND { unND :: StateT NDState m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState NDState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans ND where
    lift m = ND $ lift m

runND :: MonadTc m => ND m a -> m a
runND m = evalStateT (unND m) mempty

lookupVal :: MonadTc m => Var -> ND m Val
lookupVal v = fromMaybe top <$> gets (Map.lookup v . vals)

extendVals :: MonadTc m => [(Var, Val)] -> ND m a -> ND m a
extendVals vvals m = do
    modify $ \s -> s { vals = Map.fromList vvals `Map.union` vals s }
    x <- m
    modify $ \s -> s { vals        = foldl' (flip Map.delete) (vals s) vs
                     , usedDefault = usedDefault s Set.\\ Set.fromList vs
                     }
    return x
  where
    vs :: [Var]
    vs = map fst vvals

putVal :: MonadTc m => Var -> Val -> ND m ()
putVal v val =
    modify $ \s -> s { vals = Map.insert v val (vals s) }

updateArray :: MonadTc m => Var -> Array -> ND m ()
updateArray v arr = do
   old     <- lookupVal v
   let upd =  old `lub` new
   traceNeedDefault $ text "updateArray:" <+> ppr v <+> ppr old <+> ppr arr <+> ppr upd
   putVal v upd
  where
    new :: Val
    new = ArrV arr

needDefault :: Monad m => Var -> ND m ()
needDefault v = modify $ \s -> s { usedDefault = Set.insert v (usedDefault s) }

updateNeedDefault :: MonadTc m => BoundVar -> ND m a -> ND m (a, BoundVar)
updateNeedDefault bv m = do
    x    <- m
    need <- gets (Set.member (bVar bv) . usedDefault)
    traceNeedDefault $ text "updateNeedDefault:" <+> ppr (bVar bv) <+> ppr need
    return (x, bv{bNeedDefault = Just need})

useVar :: MonadTc m => Var -> ND m ()
useVar v = do
    tau <- lookupVar v
    val <- lookupVal v
    when (partial tau val) $
        needDefault v

useField :: MonadTc m => Var -> Field -> ND m ()
useField v f = do
    val  <- lookupVal v
    val' <- case val of
              StructV flds -> maybe err return $ Map.lookup f flds
              _ -> return val
    -- XXX Should not assume struct field is not an array!
    when (partial intT val') $
        needDefault v
  where
    err :: Monad m => m a
    err = faildoc $ text "Struct does not have field" <+> ppr f

defaultsUsedExp :: MonadTc m => Exp -> m (Set Var)
defaultsUsedExp e =
    runND $
    extendVals (Set.toList vs `zip` repeat bot) $ do
    void $ useExp e
    gets usedDefault
  where
    vs :: Set Var
    vs = fvs e

needDefaultProgram :: MonadTc m => Program l -> m (Program l)
needDefaultProgram (Program decls comp tau) = runND $ do
  (decls', comp') <-
      useDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      useComp comp
  return $ Program decls' comp' tau

useDecls :: MonadTc m
         => [Decl l]
         -> ND m a
         -> ND m ([Decl l], a)
useDecls [] m = do
    x <- m
    return ([], x)

useDecls (d:ds) m = do
    (d', (ds', x)) <- useDecl d $ useDecls ds m
    return (d':ds', x)

useDecl :: MonadTc m
        => Decl l
        -> ND m a
        -> ND m (Decl l, a)
useDecl (LetD decl s) m = do
    (decl', x) <- useLocalDecl decl m
    return (LetD decl' s, x)

useDecl (LetFunD f iotas vbs tau_ret e l) m =
    extendVars [(bVar f, tau)] $ do
    e' <- extendLetFun f iotas vbs tau_ret $
          extendVals (map fst vbs `zip` repeat bot) $
          fst <$> useExp e
    x  <- m
    return (LetFunD f iotas vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

useDecl (LetExtFunD f iotas vbs tau_ret l) m = do
    x <- extendExtFuns [(bVar f, tau)] m
    return (LetExtFunD f iotas vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

useDecl (LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (LetStructD s flds l, x)

useDecl (LetCompD v tau comp l) m = do
    comp' <- extendLet v tau $
             useComp comp
    x     <- extendVars [(bVar v, tau)] m
    return (LetCompD v tau comp' l, x)

useDecl (LetFunCompD f iotas vbs tau_ret comp l) m =
    extendVars [(bVar f, tau)] $ do
    comp' <- extendLetFun f iotas vbs tau_ret $
             extendVals (map fst vbs `zip` repeat bot) $
             useComp comp
    x     <- m
    return (LetFunCompD f iotas vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

useLocalDecl :: MonadTc m
             => LocalDecl
             -> ND m a
             -> ND m (LocalDecl, a)
useLocalDecl (LetLD v tau e s) m = do
    (e', val) <- useExp e
    (x, v')   <- extendVars [(bVar v, tau)] $
                 extendVals [(bVar v, ensureTotal tau val)] $
                 updateNeedDefault v m
    return (LetLD v' tau e' s, x)

useLocalDecl (LetRefLD v tau Nothing s) m = do
    (x, v') <- extendVars [(bVar v, refT tau)] $
               extendVals [(bVar v, bot)] $
               updateNeedDefault v m
    return (LetRefLD v' tau Nothing s, x)

useLocalDecl (LetRefLD v tau (Just e) s) m = do
    (e', val) <- useExp e
    (x, v')   <- extendVars [(bVar v, refT tau)] $
                 extendVals [(bVar v, ensureTotal tau val)] $
                 updateNeedDefault v m
    return (LetRefLD v' tau (Just e') s, x)

useLocalDecl LetViewLD{} _ =
    faildoc $ text "Views not supported."

useComp :: MonadTc m => Comp l -> ND m (Comp l)
useComp comp = do
    steps' <- useSteps (unComp comp)
    return comp{ unComp = steps' }

useSteps :: forall l m . MonadTc m
         => [Step l]
         -> ND m [Step l]
useSteps [] =
    return []

useSteps (LetC l decl s : steps) = do
    (decl', steps') <- useLocalDecl decl $
                       useSteps steps
    return $ LetC l decl' s : steps'

useSteps (BindC l WildV tau s : steps) = do
    steps' <- useSteps steps
    return $ BindC l WildV tau s : steps'

useSteps (BindC l (TameV v) tau s : steps) = do
    steps' <- extendVars [(bVar v, tau)] $
              extendVals [(bVar v, ensureTotal tau bot)] $
              useSteps steps
    return $ BindC l (TameV v) tau s : steps'

useSteps (step : steps) =
    (:) <$> useStep step <*> useSteps steps

useStep :: forall l m . MonadTc m => Step l -> ND m (Step l)
useStep (VarC l v s) = do
    useVar v
    return $ VarC l v s

useStep (CallC l f iotas args s) =
    CallC l f iotas <$> mapM useArg args <*> pure s
  where
    useArg :: Arg l -> ND m (Arg l)
    useArg (ExpA e)  = ExpA  <$> (fst <$> useExp e)
    useArg (CompA c) = CompA <$> useComp c

useStep (IfC l e1 c2 c3 s) = do
    e1'        <- fst <$> useExp e1
    (c2', c3') <- useIf (useComp c2) (useComp c3)
    return $ IfC l e1' c2' c3' s

useStep LetC{} =
    faildoc $ text "Cannot use let step."

useStep (WhileC l e c s) =
    WhileC l <$> (fst <$> useExp e) <*> useComp c <*> pure s

useStep (ForC l ann v tau e1 e2 c s) = do
    (e1', val1) <- useExp e1
    (e2', val2) <- useExp e2
    c'          <- extendVars [(v, tau)] $
                   useFor v val1 val2 (useComp c)
    return $ ForC l ann v tau e1' e2' c' s

useStep (LiftC l e s) =
    LiftC l <$> (fst <$> useExp e) <*> pure s

useStep (ReturnC l e s) =
    ReturnC l <$> (fst <$> useExp e) <*> pure s

useStep BindC{} =
    faildoc $ text "Cannot use bind step."

useStep (TakeC l tau s) =
    pure $ TakeC l tau s

useStep (TakesC l n tau s) =
    pure $ TakesC l n tau s

useStep (EmitC l e s) =
    EmitC l <$> (fst <$> useExp e) <*> pure s

useStep (EmitsC l e s) =
    EmitsC l <$> (fst <$> useExp e) <*> pure s

useStep (RepeatC l ann c s) =
    RepeatC l ann <$> useComp c <*> pure s

useStep (ParC ann tau c1 c2 s) =
    ParC ann tau <$> useComp c1 <*> useComp c2 <*> pure s

useExp :: forall m . MonadTc m
       => Exp
       -> ND m (Exp, Val)
useExp e@(ConstE (FixC I _ _ 0 x) _) =
    return (e, intV x)

useExp e@(ConstE (ArrayC cs) _) =
    return (e, wholeArrV n)
  where
    n :: Iota
    n = constI (length cs)

useExp e@ConstE{} =
    return (e, top)

useExp e@(VarE v _) = do
    useVar v
    val <- lookupVal v
    return (e, val)

useExp e@(UnopE Len (VarE v _) _) = do
    (iota, _) <- lookupVar v >>= checkArrOrRefArrT
    return (e, iotaV iota)

useExp (UnopE op e s) =
    topA $ UnopE op <$> (fst <$> useExp e) <*> pure s

useExp (BinopE op e1 e2 s) =
    topA $ BinopE op <$> (fst <$> useExp e1)
                     <*> (fst <$> useExp e2)
                     <*> pure s

useExp (IfE e1 e2 e3 s) = do
    e1'        <- fst <$> useExp e1
    (e2', e3') <- useIf (fst <$> useExp e2) (fst <$> useExp e3)
    return (IfE e1' e2' e3' s, top)

useExp (LetE decl e s) = do
    (decl', e') <- useLocalDecl decl $
                   fst <$> useExp e
    return (LetE decl' e' s, top)

useExp (CallE f iotas es s) = do
    useVar f
    isExt <- isExtFun f
    es'   <- mapM (useArg isExt) es
    return (CallE f iotas es' s, top)
  where
    useArg :: Bool -> Exp -> ND m Exp
    -- We assume that external functions fully initialize any ref passed to
    -- them.
    useArg True e@(VarE v _) = do
        tau <- inferExp e
        if isRefT tau
            then do putVal v (ensureTotal tau top)
                    return e
            else fst <$> useExp e

    useArg _ e =
        fst <$> useExp e

useExp (DerefE e s) =
    topA $ DerefE <$> (fst <$> useExp e) <*> pure s

useExp (AssignE e1 e2 s) = do
    (e2', val) <- useExp e2
    go e1 e2' val
  where
    go :: Exp -> Exp -> Val -> ND m (Exp, Val)
    go e1@(VarE v _) e2' val = do
        tau <- lookupVar v
        putVal v (ensureTotal tau val)
        topA $ return $ AssignE e1 e2' s

    go e1@(IdxE e_v@(VarE v _) e_i len s) e2' _ = do
        traceNeedDefault $ text "Assign IdxE:" <+> ppr e1 <+> ppr e2
        (n, _)        <- lookupVar v >>= checkArrOrRefArrT
        (e_i', val_i) <- useExp e_i
        let e1'       = IdxE e_v e_i' len s
        update n val_i
        topA $ return $ AssignE e1' e2' s
      where
        update :: Iota -> Val -> ND m ()
        update n (IntV i) =
            updateArray v (Arr n (extendPR i len))

        update _ _ =
            return ()

    go e1@(ProjE (VarE v _) f _) e2' val2 =
        lookupVal v >>= go
      where
        go :: Val -> ND m (Exp, Val)
        go val | val == bot = do
            StructDef _ flds _ <- lookupVar v >>=
                                  checkRefT >>=
                                  checkStructT >>=
                                  lookupStruct
            putVal v $ StructV $
                Map.insert f val2 $
                Map.fromList (map fst flds `zip` repeat bot)
            return (AssignE e1 e2' s, top)

        go (StructV flds) = do
            putVal v $ StructV $ Map.insert f val2 flds
            return (AssignE e1 e2' s, top)

        go _ =
            topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

    go e1 e2' _  =
        topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

useExp (WhileE e1 e2 s) =
    topA $ WhileE <$> (fst <$> useExp e1) <*> (fst <$> useExp e2) <*> pure s

useExp (ForE ann v tau e1 e2 e3 s) = do
    (e1', val1) <- useExp e1
    (e2', val2) <- useExp e2
    e3'         <- extendVars [(v, tau)] $
                   useFor v val1 val2 (fst <$> useExp e3)
    topA $ return $ ForE ann v tau e1' e2' e3' s

useExp (ArrayE es s) = do
    es' <- map fst <$> mapM useExp es
    return (ArrayE es' s, wholeArrV n)
  where
    n :: Iota
    n = constI (length es)

useExp (IdxE e1@(VarE v _) e2 len s) = do
    let e1'     =  e1
    val1        <- lookupVal v
    (e2', val2) <- useExp e2
    traceNeedDefault $ text "IdxE:" <+> ppr v <+> ppr val1 <+> ppr val2
    go val1 val2
    topA $ return $ IdxE e1' e2' len s
  where
    go :: Val -> Val -> ND m ()
    go (ArrV (Arr _ xs)) (IntV j) | extendPR j len <= xs =
        return ()

    go _ _ =
        useVar v

useExp (IdxE e1 e2 len s) =
    topA $ IdxE <$> (fst <$> useExp e1) <*> (fst <$> useExp e2) <*> pure len <*> pure s

useExp (StructE struct flds s) =
    topA $ StructE struct <$> (zip fs <$> mapM (fmap fst . useExp) es) <*> pure s
  where
    fs :: [Field]
    es :: [Exp]
    (fs, es) = unzip flds

useExp (ProjE e@(VarE v _) f s) = do
    useField v f
    return (ProjE e f s, top)

useExp (ProjE e f s) =
    topA $ ProjE <$> (fst <$> useExp e) <*> pure f <*> pure s

useExp (PrintE nl es s) =
    (,) <$> (PrintE nl <$> mapM (fmap fst . useExp) es <*> pure s)
        <*> pure top

useExp e@ErrorE{} =
    return (e, top)

useExp (ReturnE ann e s) =
    topA $ ReturnE ann <$> (fst <$> useExp e) <*> pure s

useExp (BindE WildV tau e1 e2 s) =
    topA $ BindE WildV tau <$> (fst <$> useExp e1)
                           <*> (fst <$> useExp e2)
                           <*> pure s

useExp (BindE (TameV v) tau e1 e2 s) =
    topA $ BindE (TameV v) tau <$> (fst <$> useExp e1)
                               <*> (extendVars [(bVar v, tau)] $
                                    extendVals [(bVar v, ensureTotal tau bot)] $
                                    fst <$> useExp e2)
                               <*> pure s

useExp (LutE sz e) =
    topA $ LutE sz <$> (fst <$> useExp e)

useExp (GenE e gs l) = do
    e' <- checkGenerators gs $ \_ -> fst <$> useExp e
    return (GenE e' gs l, top)

useIf :: MonadTc m => ND m a -> ND m b -> ND m (a, b)
useIf ma mb = do
    s   <- get
    x   <- ma
    s_a <- get
    put s
    y   <- mb
    s_b <- get
    put NDState { vals        = vals s_a `bub` vals s_b
                , usedDefault = usedDefault s_a <> usedDefault s_b
                }
    return (x, y)

useFor :: MonadTc m => Var -> Val -> Val -> ND m a -> ND m a
useFor v val_i val_len k | Just i <- fromUnitV val_i, Just len <- fromUnitV val_len =
    extendVals [(v, rangeV i len)] k

useFor _ _ _ k =
    k

topA :: Applicative f => f a -> f (a, Val)
topA m = (,) <$> m <*> pure top
