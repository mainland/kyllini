{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.RefFlow
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Analysis.RefFlow (
    RF,
    runRF,

    rfProgram
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor,
                             tell)
import Data.Foldable (toList)
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint
import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq

data Ref = VarR !Var
         | QueueR
  deriving (Eq, Ord, Show)

instance Pretty Ref where
    ppr (VarR v) = ppr v
    ppr QueueR   = text "queue"

instance Located Ref where
    locOf (VarR v) = locOf v
    locOf _        = noLoc

-- | Given an expression of type @ref \tau@, return the source variable of type
-- @ref@.
refRoot :: Monad m => Exp -> m Var
refRoot (VarE v _)     = return v
refRoot (IdxE e _ _ _) = refRoot e
refRoot (ProjE e _ _)  = refRoot e
refRoot e              = faildoc $ text "Not a reference:" <+> ppr e

data RFState = RFState
    { -- | Maps a reference to the variables it flows to.
      refFlowsTo :: !(Map Ref (Set Var))
    , -- | Maps a variable to the refs used to define the variable
      varFlowsFrom :: !(Map Var (Set Ref))
    , -- | The set of variables whose ref source has been modified
      tainted :: !(Set Var)
    , -- | The set of tainted variables that have been used
      usedTainted :: !(Set Var)
    }

instance Monoid RFState where
    mempty = RFState
        { refFlowsTo   = mempty
        , varFlowsFrom = mempty
        , tainted      = mempty
        , usedTainted  = mempty
        }

    x `mappend` y = RFState
        { refFlowsTo   = Map.unionWith (<>) (refFlowsTo x) (refFlowsTo y)
        , varFlowsFrom = Map.unionWith (<>) (varFlowsFrom x) (varFlowsFrom y)
        , tainted      = tainted x <> tainted y
        , usedTainted  = usedTainted x <> usedTainted y
        }

type RefSet = Set Ref

newtype RF m a = RF { unRF :: StateT RFState (WriterT RefSet m) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadWriter RefSet,
              MonadState RFState,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

runRF :: MonadTc m => RF m a -> m a
runRF m = fst <$> runWriterT (evalStateT (unRF m) mempty)

-- | @extendVarFlowsFrom v refs k@ specifies that the references in @ref@ flow
-- to the variable @v@ in the scoped computation @k@.
extendVarFlowsFrom :: forall m a . MonadTc m => Var -> Set Ref -> RF m a -> RF m a
extendVarFlowsFrom v refs k = do
    putFlowVars v refs
    x <- k
    modify $ \s -> s { refFlowsTo   = Map.map (Set.delete v) (Map.delete (VarR v) (refFlowsTo s))
                     , varFlowsFrom = Map.map (Set.delete (VarR v)) (Map.delete v (varFlowsFrom s))
                     , tainted      = Set.delete v (tainted s)
                     , usedTainted  = Set.delete v (usedTainted s)
                     }
    return x

-- | @putFlowVars v refs@ specifies that the references in @ref@ flow to the
-- variable @v@.
putFlowVars :: forall m . MonadTc m => Var -> Set Ref -> RF m ()
putFlowVars v refs = do
    modify $ \s -> s { varFlowsFrom = Map.insert v refs (varFlowsFrom s) }
    mapM_ (`flowsTo` v) (toList refs)
  where
    flowsTo :: Ref -> Var -> RF m ()
    flowsTo vref v =
        modify $ \s ->
            s { refFlowsTo = Map.insert vref
                                        (Set.insert v (Map.findWithDefault mempty vref (refFlowsTo s)))
                                        (refFlowsTo s)
              }

-- | Indicated that a ref was potentially modified.
refModified :: MonadTc m => Ref -> RF m ()
refModified v = do
    flowsTo <- gets $ \s -> Map.lookup v (refFlowsTo s)
    case flowsTo of
      Nothing -> return ()
      Just vs -> do traceRefFlow $
                      nest 2 $
                      text "Modification of" <+> ppr v <+> text "is tainting:" </> ppr vs
                    modify $ \s -> s { tainted = tainted s `Set.union` vs }

useVar :: MonadTc m => Var -> RF m ()
useVar v = do
    -- If the variable is tainted, mark it as being used while tainted.
    isTainted <- gets $ \s -> v `Set.member` tainted s
    when isTainted $ do
        traceRefFlow $ text "Use of" <+> ppr v <+> text "is tainted"
        modify $ \s -> s { usedTainted = Set.insert v (usedTainted s) }
    -- Mark the refs used to produce the value of the variable.
    tau <- lookupVar v
    if isRefT tau
      then tell $ Set.singleton (VarR v)
      else do refs <- fromMaybe mempty <$> gets (Map.lookup v . varFlowsFrom)
              tell refs

-- | Collect the set of refs used to produce the result of the computation @k@.
collectUseInfo :: Monad m => RF m a -> RF m (a, RefSet)
collectUseInfo k =
    censor (const mempty) $
    listen k

-- | Throw away the set of refs used to produce the result of the computation
-- @k@.
voidUseInfo :: Monad m => RF m a -> RF m a
voidUseInfo = censor (const mempty)

updateTaint :: MonadTc m => BoundVar -> RF m a -> RF m (a, BoundVar)
updateTaint bv m =
    censor f $ do
    x              <- m
    usedAfterTaint <- gets $ \s -> Set.member (bVar bv) (usedTainted s)
    return (x, bv { bTainted = Just usedAfterTaint })
  where
    f :: RefSet -> RefSet
    f = Set.delete (VarR (bVar bv))

rfProgram :: MonadTc m => Program l -> RF m (Program l)
rfProgram (Program decls comp tau) = do
  (decls', comp') <-
      rfDecls decls $
      inSTScope tau $
      inLocalScope $
      withLocContext comp (text "In definition of main") $
      rfComp comp
  return $ Program decls' comp' tau

rfDecls :: MonadTc m
        => [Decl l]
        -> RF m a
        -> RF m ([Decl l], a)
rfDecls [] m = do
    x <- m
    return ([], x)

rfDecls (d:ds) k = do
    (d', (ds', x)) <- rfDecl d $ rfDecls ds k
    return (d':ds', x)

rfDecl :: MonadTc m
       => Decl l
       -> RF m a
       -> RF m (Decl l, a)
rfDecl (LetD decl s) m = do
    (decl', x) <- rfLocalDecl decl m
    return (LetD decl' s, x)

rfDecl (LetFunD f ivs vbs tau_ret e l) m = do
    (x, e') <-
        extendVars [(bVar f, tau)] $ do
        e' <- extendLetFun f ivs vbs tau_ret $
              rfExp e
        x <- m
        return (x, e')
    return (LetFunD f ivs vbs tau_ret e' l, x)
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

rfDecl (LetExtFunD f ivs vbs tau_ret l) m = do
    x <- extendExtFuns [(bVar f, tau)] m
    return (LetExtFunD f ivs vbs tau_ret l, x)
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

rfDecl decl@(LetStructD s flds l) m = do
    x <- extendStructs [StructDef s flds l] m
    return (decl, x)

rfDecl (LetCompD v tau comp l) m = do
    comp' <- extendLet v tau $
             rfComp comp
    x     <- extendVars [(bVar v, tau)] m
    return (LetCompD v tau comp' l, x)

rfDecl (LetFunCompD f ivs vbs tau_ret comp l) m = do
    (x, comp') <-
        extendVars [(bVar f, tau)] $ do
        comp' <- extendLetFun f ivs vbs tau_ret $
                 rfComp comp
        x <- m
        return (x, comp')
    return (LetFunCompD f ivs vbs tau_ret comp' l, x)
  where
    tau :: Type
    tau = FunT ivs (map snd vbs) tau_ret l

rfLocalDecl :: forall m a . MonadTc m
            => LocalDecl
            -> RF m a
            -> RF m (LocalDecl, a)
rfLocalDecl (LetLD v tau e1 s) k = do
    (e1', refs) <- collectUseInfo $ rfExp e1
    (x, v')     <- extendVars [(bVar v, tau)] $
                   extendVarFlowsFrom (bVar v) refs $
                   updateTaint v k
    return (LetLD v' tau e1' s, x)

rfLocalDecl (LetRefLD v tau maybe_e1 s) k = do
    maybe_e1' <- traverse (voidUseInfo . rfExp) maybe_e1
    x         <- extendVars [(bVar v, refT tau)] k
    return (LetRefLD v tau maybe_e1' s, x)

rfComp :: MonadTc m
       => Comp l
       -> RF m (Comp l)
rfComp (Comp steps) =
    Comp <$> rfSteps steps

rfSteps :: MonadTc m
        => [Step l]
        -> RF m [Step l]
rfSteps [] =
    return []

rfSteps (LetC l decl s : steps) = do
    (decl', steps') <- rfLocalDecl decl $
                       rfSteps steps
    return $ LetC l decl' s : steps'

rfSteps (step : BindC l WildV tau s : steps) = do
    step'  <- voidUseInfo $ rfStep step
    steps' <- rfSteps steps
    return $ step' : BindC l WildV tau s : steps'

rfSteps (step : BindC l (TameV v) tau s : steps) = do
    (step', refs) <- collectUseInfo $ rfStep step
    (steps', v')  <- extendVars [(bVar v, tau)] $
                     extendVarFlowsFrom (bVar v) refs $
                     updateTaint v $
                     rfSteps steps
    return $ step' : BindC l (TameV v') tau s : steps'

rfSteps (step : steps) = do
    step'  <- voidUseInfo $ rfStep step
    steps' <- rfSteps steps
    return $ step' : steps'

rfStep :: forall l m . MonadTc m
       => Step l
       -> RF m (Step l)
rfStep c@(VarC _ v _) = do
    useVar v
    return c

rfStep (CallC l f iotas args s) = do
    -- We taint arguments /before/ we call 'rfArg' so that any arguments that
    -- may be derived from a ref dereference are actually dereferenced. See Note
    -- [Aliasing] in Cg.hs.
    mapM_ taintArg args
    CallC l f iotas <$> mapM rfArg args <*> pure s
  where
    rfArg :: Arg l -> RF m (Arg l)
    rfArg (CompA comp) = CompA <$> rfComp comp
    rfArg (ExpA e)     = ExpA <$> rfExp e

    taintArg :: Arg l -> RF m ()
    taintArg CompA{} =
        return ()

    taintArg (ExpA e) = do
        tau <- inferExp e
        when (isRefT tau) $ do
            v <- refRoot e
            refModified $ VarR v

rfStep (IfC l e1 c2 c3 s) = do
    e1'        <- rfExp e1
    (c2', c3') <- rfIf (rfComp c2) (rfComp c3)
    return $ IfC l e1' c2' c3' s

rfStep LetC{} =
    panicdoc $ text "rfStep: saw let"

rfStep (WhileC l e1 c2 s) =
    WhileC l <$> rfExp e1 <*> rfComp c2 <*> pure s

rfStep (ForC l ann v tau e1 e2 c s) =
    ForC l ann v tau <$> rfExp e1 <*> rfExp e2 <*> extendVars [(v, tau)] (rfComp c) <*> pure s

rfStep (LiftC l e s) =
    LiftC l <$> rfExp e <*> pure s

rfStep (ReturnC l e s) =
    ReturnC l <$> rfExp e <*> pure s

rfStep BindC{} =
    panicdoc $ text "rfStep: saw bind"

rfStep c@TakeC{} = do
    refModified QueueR
    tell $ Set.singleton QueueR
    return c

rfStep c@TakesC{} = do
    refModified QueueR
    tell $ Set.singleton QueueR
    return c

rfStep (EmitC l e s) =
    EmitC l <$> voidUseInfo (rfExp e) <*> pure s

rfStep (EmitsC l e s) =
    EmitsC l <$> voidUseInfo (rfExp e) <*> pure s

rfStep (RepeatC l ann c s) =
    RepeatC l ann <$> rfComp c <*> pure s

rfStep (ParC ann tau c1 c2 s) = do
    -- We need to make sure any refs modified in /either/ branch are seen as
    -- modified in both branches. If the two branches use the same source ref,
    -- we need to re-analyze them to look for use-after-modify. See Note
    -- [Aliasing] in Cg.hs.
    (c1', refs1) <- collectUseInfo $ rfComp c1
    (c2', refs2) <- collectUseInfo $ rfComp c2
    tell $ refs1 <> refs2
    if Set.null (refs1 `Set.intersection` refs2)
      then return $ ParC ann tau c1' c2' s
      else ParC ann tau <$> rfComp c1 <*> rfComp c2 <*> pure s

rfStep LoopC{} =
    faildoc $ text "rfStep: saw LoopC"

rfExp :: forall m . MonadTc m
      => Exp
      -> RF m Exp
rfExp e@ConstE{} =
    pure e

rfExp e@(VarE v _) = do
    useVar v
    return e

rfExp (UnopE op e s) =
    UnopE op <$> rfExp e <*> pure s

rfExp (BinopE op e1 e2 s) =
    BinopE op <$> rfExp e1 <*> rfExp e2 <*> pure s

rfExp (IfE e1 e2 e3 s) = do
    e1'        <- rfExp e1
    (e2', e3') <- rfIf (rfExp e2) (rfExp e3)
    return $ IfE e1' e2' e3' s

rfExp (LetE decl e2 s) = do
    (decl', e2') <- rfLocalDecl decl $
                    rfExp e2
    return $ LetE decl' e2' s

rfExp (CallE f iotas es s) = do
    e' <- CallE f iotas <$> mapM rfExp es <*> pure s
    mapM_ taintArg es
    return e'
  where
    taintArg :: Exp -> RF m ()
    taintArg e = do
        tau <- inferExp e
        when (isRefT tau) $ do
            v <- refRoot e
            refModified $ VarR v

rfExp (DerefE e s) =
    DerefE <$> rfExp e <*> pure s

rfExp (AssignE e1 e2 s) = do
    e1'         <- rfExp e1
    (e2', refs) <- collectUseInfo $ rfExp e2
    v           <- refRoot e1
    refModified (VarR v)
    putFlowVars v refs
    return $ AssignE e1' e2' s

rfExp (WhileE e1 e2 s) =
    WhileE <$> rfExp e1 <*> rfExp e2 <*> pure s

rfExp (ForE ann v tau e1 e2 e3 s) =
    ForE ann v tau <$> rfExp e1 <*> rfExp e2 <*> extendVars [(v, tau)] (rfExp e3) <*> pure s

rfExp (ArrayE es s) =
    ArrayE <$> mapM rfExp es <*> pure s

rfExp (IdxE e1 e2 len s) =
    IdxE <$> rfExp e1 <*> rfExp e2 <*> pure len <*> pure s

rfExp (StructE sname flds s) =
    StructE sname <$> mapM rfField flds <*> pure s
  where
    rfField :: (Field, Exp) -> RF m (Field, Exp)
    rfField (f, e) = (,) <$> pure f <*> rfExp e

rfExp (ProjE e f s) =
    ProjE <$> rfExp e <*> pure f <*> pure s

rfExp (PrintE nl es s) =
    PrintE nl <$> mapM rfExp es <*> pure s

rfExp e@ErrorE{} =
    pure e

rfExp (ReturnE ann e s) =
    ReturnE ann <$> rfExp e <*> pure s

rfExp (BindE WildV tau e1 e2 s) = do
    e1' <- voidUseInfo $ rfExp e1
    e2' <- rfExp e2
    return $ BindE WildV tau e1' e2' s


rfExp (BindE (TameV v) tau e1 e2 s) = do
    (e1', refs) <- collectUseInfo $ rfExp e1
    (e2', v')   <- extendVars [(bVar v, tau)] $
                   extendVarFlowsFrom (bVar v) refs $
                   updateTaint v $
                   rfExp e2
    return $ BindE (TameV v') tau e1' e2' s

rfExp (LutE e) =
    LutE <$> rfExp e

rfIf :: Monad m
     => RF m a
     -> RF m a
     -> RF m (a, a)
rfIf k1 k2 = do
    s <- get
    (x, refs2) <- collectUseInfo k1
    s2 <- get
    put s
    (y, refs3) <- collectUseInfo k2
    s3 <- get
    tell $ refs2 <> refs3
    put $ s2 <> s3
    return (x, y)
