{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      :  KZC.Analysis.StaticRef
Copyright   :  (c) 2015-2016 Drexel University
License     :  BSD-style
Maintainer  :  mainland@cs.drexel.edu

Determine whether or not a ref is actually written to.
-}

module KZC.Analysis.StaticRef (
    SR,
    runSR,

    staticRefsProgram
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
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Set (Set)
import qualified Data.Set as Set
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif /* !MIN_VERSION_base(4,8,0) */

import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Trace
import KZC.Uniq

type RefSet = Set Var

newtype SR m a = SR { unSR :: WriterT RefSet m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadWriter RefSet,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

instance MonadTrans SR where
    lift m = SR $ lift m

runSR :: MonadTc m => SR m a -> m a
runSR m = fst <$> runWriterT (unSR m)

writeRef :: MonadTc m => Var -> SR m ()
writeRef v = tell $ Set.singleton v

-- | Return a flag indicating whether or not the given variable was written to
-- after running the specified action, after which the variable is purged from
-- the static ref environment.
withStaticRefFlag :: MonadTc m => BoundVar -> SR m a -> SR m (Bool, a)
withStaticRefFlag v m =
    censor (Set.delete (bVar v)) $ do
    (x, refs) <- listen m
    return (Set.notMember (bVar v) refs, x)

updStaticInfo :: BoundVar -> Bool -> BoundVar
updStaticInfo v isStatic = v { bStaticRef = Just isStatic }

staticRefsProgram :: MonadTc m => Program l -> SR m (Program l)
staticRefsProgram = programT

instance MonadTc m => Transform (SR m) where
    localDeclT (LetRefLD v tau e s) m = do
        e'            <- traverse expT e
        (isStatic, x) <- extendVars [(bVar v, refT tau)] $ withStaticRefFlag v m
        return (LetRefLD (updStaticInfo v isStatic) tau e' s, x)

    localDeclT decl m =
        transLocalDecl decl m

    argT arg@(ExpA e) = do
        checkRefArg e
        transArg arg

    argT arg =
        transArg arg

    expT e@(CallE _ _ es _) = do
        mapM_ checkRefArg es
        transExp e

    expT e@(AssignE e1 _ _) = do
        refPathRoot e1 >>= writeRef
        transExp e

    expT e =
        transExp e

checkRefArg :: MonadTc m => Exp -> SR m ()
checkRefArg e = do
    tau <- inferExp e
    when (isRefT tau) $
        refPathRoot e >>= writeRef
