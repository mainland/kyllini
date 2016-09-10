{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  KZC.Util.Uniq
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Util.Uniq (
    Uniq(..),
    MonadUnique(..),
    maybeNewUnique,

    Gensym(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..))
import Control.Monad.Exception (ExceptionT(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))
import Data.Loc (Located,
                 Loc,
                 noLoc,
                 srclocOf)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid)
#endif /* !MIN_VERSION_base(4,8,0) */
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Config

newtype Uniq = Uniq Int
  deriving (Eq, Ord, Read, Show)

instance Pretty Uniq where
    ppr (Uniq u) = ppr u

class (Monad m, MonadConfig m) => MonadUnique m where
    newUnique :: m Uniq

maybeNewUnique :: MonadUnique m => m (Maybe Uniq)
maybeNewUnique = do
    noGensym <- asksConfig $ testDynFlag NoGensym
    if noGensym
        then return Nothing
        else Just <$> newUnique

instance MonadUnique m => MonadUnique (MaybeT m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ContT r m) where
    newUnique = lift newUnique

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadUnique m) => MonadUnique (ErrorT e m) where
    newUnique = lift newUnique
#endif /* !MIN_VERSION_base(4,8,0) */

instance MonadUnique m => MonadUnique (ExceptT e m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ExceptionT m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ReaderT r m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (S.StateT s m) where
    newUnique = lift newUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    newUnique = lift newUnique

instance (Monoid w, MonadUnique m) => MonadUnique (S.WriterT w m) where
    newUnique = lift newUnique

class Gensym a where
    -- | Gensym a symbol using the given string as a basis.
    gensym :: MonadUnique m => String -> m a
    gensym s = gensymAt s (noLoc :: Loc)

    -- | Gensym a symbol using the given string and location as a basis.
    gensymAt :: (MonadUnique m, Located l) => String -> l -> m a
    gensymAt s _ = gensym s

    -- | Ensure the symbol is unique
    uniquify :: MonadUnique m => a -> m a

instance Gensym C.Id where
    gensymAt s l = do
        maybe_u <- maybeNewUnique
        case maybe_u of
          Nothing       -> return $ C.Id s (srclocOf l)
          Just (Uniq u) -> return $ C.Id (s ++ "__" ++ show u) (srclocOf l)

    uniquify cid@(C.Id s l) = do
        maybe_u <- maybeNewUnique
        case maybe_u of
          Nothing       -> return cid
          Just (Uniq u) -> return $ C.Id (s ++ "__" ++ show u) l

    uniquify cid =
        return cid
