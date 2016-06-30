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

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Pretty
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice
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

instance Pretty Range where
    ppr (Range lo hi) = brackets $ commasep [ppr lo, ppr hi]

instance Poset Range where
    Range i (ConstI len _) <= Range j (ConstI len' _) | i == j =
        len <= len'

    Range (ConstI i _) (ConstI len _) <= Range (ConstI i' _) (ConstI len' _) =
        i' <= i && i + len <= i' + len'

    i <= j = i == j

-- | An abstract value.
data Val -- | Unknown (not yet defined)
         = UnknownV
         -- | The variable takes on all values in the range, i.e., it may be a
         -- loop variable
         | IntV (Known Range)
         | StructV (Map Field Val)
         -- | Could be anything as far as we know...
         | TopV
  deriving (Eq, Ord, Show)

intV :: Integral a => a -> Val
intV = IntV . Known . unitR

iotaV :: Iota -> Val
iotaV = IntV . Known . iotaR

rangeV :: Iota -> Iota -> Val
rangeV i len = IntV $ Known $ Range i len

fromUnitV :: Val -> Maybe Iota
fromUnitV (IntV (Known r)) = fromUnitR r
fromUnitV _                = Nothing

instance Pretty Val where
    ppr UnknownV       = text "unknown"
    ppr (IntV rng)     = ppr rng
    ppr (StructV flds) = pprStruct (Map.toList flds)
    ppr TopV           = text "top"

instance Poset Val where
    UnknownV  <= _        = True
    _         <= TopV     = True
    IntV x    <= IntV y    = x <= y
    StructV x <= StructV y = x <= y
    _         <= _         = False

instance Lattice Val where
    UnknownV  `lub` UnknownV  = UnknownV
    IntV x    `lub` IntV y    = IntV (x `lub` y)
    StructV x `lub` StructV y = StructV (x `lub` y)
    _         `lub` _         = TopV

    IntV x    `glb` IntV y    = IntV (x `glb` y)
    StructV x `glb` StructV y = StructV (x `glb` y)
    TopV      `glb` TopV      = TopV
    _         `glb` _         = bot

instance BranchLattice Val where
    _         `bub` UnknownV  = UnknownV
    UnknownV  `bub` _         = UnknownV
    IntV x    `bub` IntV y    = IntV (x `glb` y)
    StructV x `bub` StructV y = StructV (x `bub` y)
    _         `bub` TopV      = TopV
    TopV      `bub` _         = TopV
    _         `bub` _         = bot

instance BoundedLattice Val where
    top = TopV
    bot = UnknownV

-- | Return 'True' when the value may be partial.
partial :: Type -> Val -> Bool
partial _ UnknownV       = True
partial _ (IntV i)       = i == bot
partial _ (StructV flds) = any (partial undefined) (Map.elems flds)
partial _ TopV           = False

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
    when (partial undefined val') $
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

useDecl (LetFunD f iotas vbs tau_ret e l) m = do
    (x, e') <-
        extendVars [(bVar f, tau)] $ do
        e' <- extendLetFun f iotas vbs tau_ret $
              fst <$> useExp e
        x  <- m
        return (x, e')
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

useDecl (LetFunCompD f iotas vbs tau_ret comp l) m = do
    (x, comp') <-
        extendVars [(bVar f, tau)] $ do
        comp' <- extendLetFun f iotas vbs tau_ret $
                 useComp comp
        x     <- m
        return (x, comp')
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
                 extendVals [(bVar v, val)] $
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
                 extendVals [(bVar v, val)] $
                 updateNeedDefault v m
    return (LetRefLD v' tau (Just e') s, x)

useComp :: MonadTc m => Comp l -> ND m (Comp l)
useComp (Comp steps card) = Comp <$> useSteps steps <*> pure card

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

useStep LoopC{} =
    faildoc $ text "useStep: saw LoopC"

useExp :: forall m . MonadTc m
       => Exp
       -> ND m (Exp, Val)
useExp e@(ConstE (FixC I _ _ 0 x) _) =
    return (e, intV x)

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
    es'   <- mapM (fmap fst . useArg isExt) es
    return (CallE f iotas es' s, top)
  where
    useArg :: Bool -> Exp -> ND m (Exp, Val)
    -- We assume that external functions fully initialize any ref passed to
    -- them.
    useArg True e@(VarE v _) = do
        tau <- inferExp e
        if isRefT tau
            then do putVal v top
                    return (e, top)
            else useExp e

    useArg _ e =
        useExp e

useExp (DerefE e s) =
    topA $ DerefE <$> (fst <$> useExp e) <*> pure s

useExp (AssignE e1 e2 s) = do
    (e2', val) <- useExp e2
    go e1 e2' val
  where
    go :: Exp -> Exp -> Val -> ND m (Exp, Val)
    go e1@(VarE v _) e2' val = do
        let val' | val == bot = top
                 | otherwise  = val
        putVal v val'
        topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

    go e1@(IdxE (VarE v _) (VarE i _) Nothing _) e2' _ = do
        (n, _) <- lookupVar v >>= checkArrOrRefArrT
        i_val  <- lookupVal i
        case i_val of
          IntV (Known (Range (ConstI 0 _) n')) | n' == n -> putVal v top
          _ -> return ()
        topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

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

useExp (ArrayE es s) =
    topA $ ArrayE <$> mapM (fmap fst . useExp) es <*> pure s

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
                                    fst <$> useExp e2)
                               <*> pure s

useExp (LutE e) =
    topA $ LutE <$> (fst <$> useExp e)

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
