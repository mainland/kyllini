{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

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
    ND,
    runND,

    needDefaultProgram
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (unless)
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
import Data.Ratio (numerator)
import Data.Set (Set)
import qualified Data.Set as Set
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Pretty
import KZC.Trace
import KZC.Uniq
import KZC.Util.Lattice

data Val = RangeV Iota Iota
         | StructV (Map Field (Known Val))
  deriving (Eq, Ord, Show)

instance Pretty Val where
    ppr (RangeV lo hi) = ppr (lo, hi)
    ppr (StructV flds) = pprStruct (Map.toList flds)

instance Poset Val where
    x <= y = x == y

instance Pretty (Known Val) where
    ppr Unknown     = text "unknown"
    ppr (Known val) = ppr val
    ppr Any         = text "any"

isKnown :: Known Val -> Bool
isKnown Unknown                = False
isKnown (Known RangeV{})       = True
isKnown (Known (StructV flds)) = all isKnown (Map.elems flds)
isKnown Any                    = True

data NDState = NDState
    { vals        :: Map Var (Known Val)
    , usedDefault :: Set Var
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

lookupVal :: MonadTc m => Var -> ND m (Known Val)
lookupVal v = do
    maybe_val <- gets (Map.lookup v . vals)
    case maybe_val of
      Nothing  -> faildoc $ text "Variable" <+> ppr v <+> text "not in scope"
      Just val -> return val

extendVals :: MonadTc m => [(Var, Known Val)] -> ND m a -> ND m a
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

putVal :: MonadTc m => Var -> Known Val -> ND m ()
putVal v val =
    modify $ \s -> s { vals = Map.insert v val (vals s) }

updateNeedDefault :: MonadTc m => BoundVar -> ND m a -> ND m (a, BoundVar)
updateNeedDefault bv m = do
    x    <- m
    need <- gets (Set.member (bVar bv) . usedDefault)
    return (x, bv{bNeedDefault = Just need})

useVar :: MonadTc m => Var -> ND m ()
useVar v = do
    val <- lookupVal v
    unless (isKnown val) $
        modify $ \s -> s { usedDefault = Set.insert v (usedDefault s) }

useField :: MonadTc m => Var -> Field -> ND m ()
useField v f = do
    val  <- lookupVal v
    val' <- case val of
              Known (StructV flds) -> maybe err return $ Map.lookup f flds
              _ -> return val
    unless (isKnown val') $
        modify $ \s -> s { usedDefault = Set.insert v (usedDefault s) }
  where
    err :: Monad m => m a
    err = faildoc $ text "Struct does not have field" <+> ppr f

needDefaultProgram :: MonadTc m => Program l -> ND m (Program l)
needDefaultProgram (Program decls comp tau) = do
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
    (d', (ds', x)) <- useDecl d $ useDecls ds $ m
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
        extendVals [(bVar f, top)] $ do
        e' <- extendLetFun f iotas vbs tau_ret $
              extendVals (map fst vbs `zip` repeat top) $ do
              fst <$> useExp e
        x  <- m
        return (x, e')
    return (LetFunD f iotas vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

useDecl (LetExtFunD f iotas vbs tau_ret l) m = do
    x <- extendExtFuns [(bVar f, tau)] $
         extendVals [(bVar f, top)] $
         m
    return (LetExtFunD f iotas vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT iotas (map snd vbs) tau_ret l

useDecl (LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (LetStructD s flds l, x)

useDecl (LetCompD v tau comp l) m = do
    comp' <- extendLet v tau $
             extendVals [(bVar v, top)] $
             useComp comp
    x     <- extendVars [(bVar v, tau)] $
             extendVals [(bVar v, top)] $
             m
    return (LetCompD v tau comp' l, x)

useDecl (LetFunCompD f iotas vbs tau_ret comp l) m = do
    (x, comp') <-
        extendVars [(bVar f, tau)] $
        extendVals [(bVar f, top)] $ do
        comp' <- extendLetFun f iotas vbs tau_ret $
                 extendVals (map fst vbs `zip` repeat top) $
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

useLocalDecl (LetRefLD v tau e s) m = do
    e'      <- traverse (fmap fst . useExp) e
    (x, v') <- extendVars [(bVar v, refT tau)] $
               extendVals [(bVar v, maybe Unknown (const top) e)] $ do
               updateNeedDefault v m
    return (LetRefLD v' tau e' s, x)

useComp :: MonadTc m => Comp l -> ND m (Comp l)
useComp (Comp steps) = Comp <$> useSteps steps

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
              extendVals [(bVar v, top)] $
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

useStep (LetC {}) =
    faildoc $ text "Cannot use let step."

useStep (WhileC l e c s) = do
    WhileC l <$> (fst <$> useExp e) <*> useComp c <*> pure s

useStep (ForC l ann v tau e1 e2 c s) = do
    (e1', val1) <- useExp e1
    (e2', val2) <- useExp e2
    go e1' val1 e2' val2
  where
    go :: Exp -> Known Val -> Exp -> Known Val -> ND m (Step l)
    go e1' (Known (RangeV lo lo')) e2' (Known (RangeV hi hi')) | lo' == lo && hi' == hi =
       ForC l ann v tau <$> pure e1'
                        <*> pure e2'
                        <*> (extendVars [(v, tau)] $
                             extendVals [(v, Known (RangeV lo hi))] $
                             useComp c)
                        <*> pure s

    go e1' _ e2' _ = do
       ForC l ann v tau <$> pure e1'
                        <*> pure e2'
                        <*> (extendVars [(v, tau)] $
                             extendVals [(v, top)] $
                             useComp c)
                        <*> pure s

useStep (LiftC l e s) =
    LiftC l <$> (fst <$> useExp e) <*> pure s

useStep (ReturnC l e s) =
    ReturnC l <$> (fst <$> useExp e) <*> pure s

useStep (BindC {}) =
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

useStep (ParC ann tau c1 c2 s) = do
    ParC ann tau <$> useComp c1 <*> useComp c2 <*> pure s

useStep (LoopC {}) =
    faildoc $ text "useStep: saw LoopC"

useExp :: forall m . MonadTc m
       => Exp
       -> ND m (Exp, Known Val)
useExp e@(ConstE (FixC I _ _ 0 r) s) =
    return (e, Known (RangeV iota iota))
  where
    iota :: Iota
    iota = ConstI (fromIntegral (numerator r)) s

useExp e@(ConstE {}) =
    return (e, top)

useExp e@(VarE v _) = do
    useVar v
    val <- lookupVal v
    return (e, val)

useExp e@(UnopE Len (VarE v _) _) = do
    (iota, _) <- lookupVar v >>= checkArrOrRefArrT
    return (e, Known (RangeV iota iota))

useExp (UnopE op e s) =
    topA $  UnopE op <$> (fst <$> useExp e) <*> pure s

useExp (BinopE op e1 e2 s) =
    topA $  BinopE op <$> (fst <$> useExp e1)
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
    useArg :: Bool -> Exp -> ND m (Exp, Known Val)
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
    x <- go e1 e2' val
    return x
  where
    go :: Exp -> Exp -> Known Val -> ND m (Exp, Known Val)
    go e1@(VarE v _) e2' val = do
        putVal v val
        topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

    go e1@(IdxE (VarE v _) (VarE i _) Nothing _) e2' _ = do
        (iota, _) <- lookupVar v >>= checkArrOrRefArrT
        i_val     <- lookupVal i
        case i_val of
          Known (RangeV (ConstI 0 _) iota_hi) | iota_hi == iota -> putVal v top
          _ -> return ()
        topA $ AssignE <$> (fst <$> useExp e1) <*> pure e2' <*> pure s

    go e1@(ProjE (VarE v _) f _) e2' val2 =
        lookupVal v >>= go
      where
        go :: Known Val -> ND m (Exp, Known Val)
        go Unknown = do
            StructDef _ flds _ <- lookupVar v >>=
                                  checkRefT >>=
                                  checkStructT >>=
                                  lookupStruct
            putVal v $ Known $ StructV $
                Map.insert f val2 $
                Map.fromList (map fst flds `zip` repeat Unknown)
            return (AssignE e1 e2' s, top)

        go (Known (StructV flds)) = do
            putVal v $ Known $ StructV $ Map.insert f val2 flds
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
    go e1' val1 e2' val2
  where
    go :: Exp -> Known Val -> Exp -> Known Val -> ND m (Exp, Known Val)
    go e1' (Known (RangeV lo lo')) e2' (Known (RangeV hi hi')) | lo' == lo && hi' == hi = do
       topA $ ForE ann v tau <$> pure e1'
                             <*> pure e2'
                             <*> (extendVars [(v, tau)] $
                                  extendVals [(v, Known (RangeV lo hi))] $
                                  fst <$> useExp e3)
                             <*> pure s

    go e1' _ e2' _ = do
       topA $ ForE ann v tau <$> pure e1'
                             <*> pure e2'
                             <*> (extendVars [(v, tau)] $
                                  extendVals [(v, top)] $
                                  fst <$> useExp e3)
                             <*> pure s

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
    (,) <$> (PrintE nl <$> (mapM (fmap fst . useExp) es) <*> pure s)
        <*> pure top

useExp e@(ErrorE {}) =
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
                                    extendVals [(bVar v, top)] $
                                    fst <$> useExp e2)
                               <*> pure s

useExp (LutE e) = do
    topA $ LutE <$> (fst <$> useExp e)

useIf :: MonadTc m => ND m a -> ND m b -> ND m (a, b)
useIf ma mb = do
    s   <- get
    x   <- ma
    s_a <- get
    put s
    y   <- mb
    s_b <- get
    put NDState { vals        = vals s_a `glb` vals s_b
                , usedDefault = usedDefault s_a <> usedDefault s_b
                }
    return (x, y)

topA :: Applicative f => f a -> f (a, Known Val)
topA m = (,) <$> m <*> pure top
