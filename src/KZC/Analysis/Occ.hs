{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Occ
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.Occ (
    occProgram,
    occComp
  ) where

import Prelude hiding ((<=))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>), (<*>), pure)
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Writer (MonadWriter(..),
                             WriterT(..),
                             censor)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */
import Text.PrettyPrint.Mainland

import KZC.Analysis.Lattice
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Util.Error
import KZC.Util.Trace
import KZC.Util.Uniq

type OccsInfo = Map Var OccInfo

data Occs = Occs
    { -- | Variable occurence info in the form of 'OccInfo'
      occInfo :: OccsInfo
      -- | References that are written to
    , occRefs :: Set Var
    }
  deriving (Eq)

instance Monoid Occs where
    mempty  = Occs mempty mempty
    mappend = lub

instance Poset Occs where
    Occs info rs <= Occs info' rs' = info <= info' && rs <= rs'

instance Lattice Occs where
    Occs info rs `lub` Occs info' rs' = Occs (info `lub` info') (rs `lub` rs')
    Occs info rs `glb` Occs info' rs' = Occs (info `glb` info') (rs `glb` rs')

instance BranchLattice Occs where
    Occs info rs `bub` Occs info' rs' = Occs (info `bub` info') (rs `lub` rs')

lookupOccInfo :: Var -> Occs -> OccInfo
lookupOccInfo v occs =
    fromMaybe Dead $ Map.lookup v (occInfo occs)

newtype OccM m a = OccM { unOccM :: WriterT Occs m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadWriter Occs,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadConfig,
              MonadTrace,
              MonadTc)

instance MonadTrans OccM where
    lift = OccM . lift

runOccM :: MonadTc m => OccM m a -> m a
runOccM m = fst <$> runWriterT (unOccM m)

writeRef :: MonadTc m => Var -> OccM m ()
writeRef v = tell mempty { occRefs = Set.singleton v }

-- | Return a flag indicating whether or not the given variable was written to
-- after running the specified action, after which the variable is purged from
-- the static ref environment.
withStaticRefFlag :: MonadTc m => BoundVar -> OccM m a -> OccM m (Bool, a)
withStaticRefFlag v m =
    censor (\env -> env { occRefs = Set.delete (bVar v) (occRefs env)}) $ do
    (x, env) <- listen m
    return (Set.notMember (bVar v) (occRefs env), x)

updStaticInfo :: BoundVar -> Bool -> BoundVar
updStaticInfo v isStatic = v { bStaticRef = Just isStatic }

occVar :: MonadTc m => Var -> OccM m ()
occVar v = tellOcc $ Map.singleton v Once

collectOcc :: MonadTc m => OccM m a -> OccM m (OccsInfo, a)
collectOcc m =
    censor (\env -> env { occInfo = mempty }) $ do
    (x, env) <- listen m
    return (occInfo env, x)

tellOcc :: MonadTc m => OccsInfo -> OccM m ()
tellOcc occs = tell mempty { occInfo = occs }

-- | Return occurrence information for the given variable after running the
-- specified action, after which the variable is purged from the occurrence
-- environment.
withOccInfo :: MonadTc m => BoundVar -> OccM m a -> OccM m (OccInfo, a)
withOccInfo v m =
    censor f $ do
    (x, env) <- listen m
    return (lookupOccInfo (bVar v) env, x)
  where
    f :: Occs -> Occs
    f env = env { occInfo = Map.delete (bVar v) (occInfo env) }

updOccInfo :: BoundVar -> OccInfo -> BoundVar
updOccInfo v occ = v { bOccInfo = Just occ }

occProgram :: MonadTc m => Program l -> m (Program l)
occProgram = runOccM . programT

occComp :: MonadTc m => Comp l -> m (Comp l)
occComp = runOccM . compT

instance MonadTc m => TransformExp (OccM m) where
    localDeclT (LetLD v tau e s) m = do
        e'       <- expT e
        (occ, x) <- extendVars [(bVar v, tau)] $ withOccInfo v m
        return (LetLD (updOccInfo v occ) tau e' s, x)

    localDeclT (LetRefLD v tau e s) m = do
        e'                 <- traverse expT e
        (static, (occ, x)) <- extendVars [(bVar v, refT tau)] $
                              withStaticRefFlag v $
                              withOccInfo v m
        return (LetRefLD (updStaticInfo (updOccInfo v occ) static) tau e' s, x)

    localDeclT LetViewLD{} _ =
        faildoc $ text "Views not supported."

    expT e@(VarE v _) = do
        occVar v
        return e

    expT e@(CallE f _ es _) = do
        occVar f
        mapM_ checkRefArg es
        transExp e

    expT (IfE e1 e2 e3 s) = do
        e1'         <- expT e1
        (occ2, e2') <- collectOcc $ expT e2
        (occ3, e3') <- collectOcc $ expT e3
        tellOcc $ occ2 `bub` occ3
        return $ IfE e1' e2' e3' s

    expT (AssignE e1_0 e2_0 s) =
        AssignE <$> occRef e1_0 <*> expT e2_0 <*> pure s
      where
        occRef :: Exp -> OccM m Exp
        occRef e@(VarE v _) = do
            writeRef v
            return e

        occRef (IdxE e1 e2 len s) =
            IdxE <$> occRef e1 <*> expT e2 <*> pure len <*> pure s

        occRef (ProjE e f s) =
            ProjE <$> occRef e <*> pure f <*> pure s

        occRef e =
            panicdoc $ text "Illegal assignment lhs:" <+> ppr e

    expT (BindE (TameV v) tau e1 e2 s) = do
        e1'        <- expT e1
        (occ, e2') <- extendVars [(bVar v, tau)] $
                      withOccInfo v $
                      expT e2
        return $ BindE (TameV (updOccInfo v occ)) tau e1' e2' s

    expT e =
        transExp e

instance MonadTc m => TransformComp l (OccM m) where
    declT (LetFunD f ns vbs tau_ret e l) m =
        extendVars [(bVar f, tau)] $ do
        e'       <- extendLetFun f ns vbs tau_ret $
                    expT e
        (occ, x) <- withOccInfo f m
        return (LetFunD (updOccInfo f occ) ns vbs tau_ret e' l, x)
      where
        tau :: Type
        tau = funT ns (map snd vbs) tau_ret l

    declT (LetExtFunD f ns vbs tau_ret l) m = do
        (occ, x) <- extendExtFuns [(bVar f, tau)] $
                    withOccInfo f m
        return (LetExtFunD (updOccInfo f occ) ns vbs tau_ret l, x)
      where
        tau :: Type
        tau = funT ns (map snd vbs) tau_ret l

    declT (LetCompD v tau comp l) m = do
        comp'    <- extendLet v tau $
                    compT comp
        (occ, x) <- extendVars [(bVar v, tau)] $ withOccInfo v m
        return (LetCompD (updOccInfo v occ) tau comp' l, x)

    declT (LetFunCompD f ns vbs tau_ret comp l) m =
        extendVars [(bVar f, tau)] $ do
        comp'    <- extendLetFun f ns vbs tau_ret $
                    compT comp
        (occ, x) <- withOccInfo f m
        return (LetFunCompD (updOccInfo f occ) ns vbs tau_ret comp' l, x)
      where
        tau :: Type
        tau = funT ns (map snd vbs) tau_ret l

    declT decl m =
        transDecl decl m

    stepsT (BindC l (TameV v) tau s : steps) = do
        (occ, steps') <- extendVars [(bVar v, tau)] $
                         withOccInfo v $
                         stepsT steps
        return $ BindC l (TameV (updOccInfo v occ)) tau s : steps'

    stepsT steps =
        transSteps steps

    stepT step@(VarC _ v _) = do
        occVar v
        transStep step

    stepT step@(CallC _ f _ _ _) = do
        occVar f
        transStep step

    stepT (IfC l e1 c2 c3 s) = do
        e1'         <- expT e1
        (occ2, c2') <- collectOcc $ compT c2
        (occ3, c3') <- collectOcc $ compT c3
        tellOcc $ occ2 `bub` occ3
        return $ IfC l e1' c2' c3' s

    stepT step =
        transStep step

    argT arg@(ExpA e) = do
        checkRefArg e
        transArg arg

    argT arg =
        transArg arg

checkRefArg :: MonadTc m => Exp -> OccM m ()
checkRefArg e = do
    tau <- inferExp e
    when (isRefT tau) $
        refPathRoot e >>= writeRef
