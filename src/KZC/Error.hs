{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Error
-- Copyright   :  (c) Drexel University 2014-2015
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Error (
    MonadErr(..),
    withLocContext,
    panicdoc,
    errdoc,
    warndoc,

    ErrorContext(..),
    ContextException(..),
    toContextException,
    throwContextException,
    catchContextException,

    FailException(..),
    WarnException(..),

    checkDuplicates
  ) where

import Control.Monad.Error
import Control.Monad.Exception
import Control.Monad.Reader
import Control.Monad.State
import Data.List (sortBy)
import Data.Loc
import Data.Ord (comparing)
import Data.Typeable
import Text.PrettyPrint.Mainland

import KZC.Pretty

class MonadException m => MonadErr m where
    askErrCtx    :: m [ErrorContext]
    localErrCtx  :: ([ErrorContext] -> [ErrorContext]) -> m a -> m a

    warnIsError  :: m Bool

    displayWarning :: ContextException -> m ()

    panic :: Exception e => e -> m a
    panic ex = do
        ctx <- askErrCtx
        throw $ toException (toContextException ctx ex)

    err :: Exception e => e -> m ()
    err ex = do
        ctx <- askErrCtx
        throw $ toException (toContextException ctx ex)

    warn :: Exception e => e -> m ()
    warn ex = do
        werror <- warnIsError
        if werror
          then err ex_warn
          else do ctx <- askErrCtx
                  displayWarning (toContextException ctx ex_warn)
      where
        ex_warn :: WarnException
        ex_warn = WarnException (toException ex)

instance (Error e, MonadErr m) => MonadErr (ErrorT e m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = ErrorT $ localErrCtx ctx (runErrorT m)

    warnIsError = lift warnIsError

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance MonadErr m => MonadErr (ReaderT r m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = ReaderT $ \r -> localErrCtx ctx (runReaderT m r)

    warnIsError = lift warnIsError

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance MonadErr m => MonadErr (StateT r m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = StateT $ \s -> localErrCtx ctx (runStateT m s)

    warnIsError = lift warnIsError

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

withErrCtx :: MonadErr m => ErrorContext -> m a -> m a
withErrCtx ctx m = localErrCtx (ctx :) m

withLocContext :: (Located a, MonadErr m) => a -> Doc -> m b -> m b
withLocContext a doc m =
    withErrCtx (ErrorContext loc doc) m
  where
    loc :: Loc
    loc = locOf a

panicdoc :: MonadErr m => Doc -> m a
panicdoc msg = panic (FailException msg)

errdoc :: MonadErr m => Doc -> m ()
errdoc msg = err (FailException msg)

warndoc :: MonadErr m => Doc -> m ()
warndoc msg = warn (FailException msg)

data ErrorContext = ErrorContext { ctxLoc :: Loc
                                 , ctxDoc :: Doc
                                 }
  deriving (Typeable)

data ContextException = ContextException [ErrorContext] SomeException
  deriving (Typeable)

instance Exception ContextException where

toContextException :: Exception e => [ErrorContext] -> e -> ContextException
toContextException ctx e = ContextException ctx (toException e)

throwContextException :: (Exception e, MonadErr m)
                      => (forall e' . Exception e' => e' -> m a)
                      -> e
                      -> m a
throwContextException throw' e =
    case (fromException . toException) e of
      Just (e' :: ContextException) -> throw' e'
      Nothing -> do ctx <- askErrCtx
                    throw' (toException (toContextException ctx e))

catchContextException :: (Exception e, MonadException m)
                      => m a
                      -> (e -> m a)
                      -> m a
m `catchContextException` h =
    m `catch` \e ->
      case fromException e of
        Just e' -> h e'
        Nothing -> case fromException e of
                     Just (ContextException _ e') ->
                         case fromException e' of
                           Just e'' -> h e''
                           Nothing  -> throw e
                     Nothing -> throw e

instance Pretty ContextException where
    ppr (ContextException ctx e) =
        case [loc | ErrorContext loc@(Loc {}) _ <- ctx'] of
          loc : _  ->  nest 4 $
                       ppr loc <> text ":" </>
                       (string . show) e <> pprDocs (map ctxDoc ctx')
          _        -> (string . show) e <> pprDocs (map ctxDoc ctx')
      where
        pprDocs :: [Doc] -> Doc
        pprDocs []    = empty
        pprDocs docs  = line <> stack docs

        ctx' :: [ErrorContext]
        ctx' = take 4 ctx

instance Show ContextException where
    show = pretty 80 . ppr

data FailException = FailException Doc
  deriving (Typeable)

instance Show FailException where
    show (FailException msg) = pretty 80 msg

instance Exception FailException

data WarnException = WarnException SomeException
  deriving (Typeable)

instance Exception WarnException where

instance Pretty WarnException where
    ppr (WarnException e) =
        text "Warning:" <+> (string . show) e

instance Show WarnException where
    show = pretty 80 . ppr

checkDuplicates :: forall m a . (Eq a, Ord a, Located a, Pretty a, MonadErr m)
                => Doc -> [a] -> m ()
checkDuplicates desc vs =
    case filter  (\x -> length x /= 1)
                 (equivalence (comparing fst) binds) of
      []    ->  return ()
      dups  ->  faildoc $ nest 4 $
                stack (map pprGroup dups)
  where
    binds = [(n, locOf n) | n <- vs]

    pprGroup :: [(a, Loc)] -> Doc
    pprGroup ns = nest 4 $
        desc <+> quote ((fst . head) ns) <+> text "at:" </>
        stack (map (ppr . snd) ns)

equivalence :: forall a . (a -> a -> Ordering) -> [a] -> [[a]]
equivalence cmp as = go $ sortBy cmp as
  where
    go :: [a] -> [[a]]
    go  []                                =  []
    go  [x]                               =  [[x]]
    go  l@(x : y : ys)  |  cmp x y == EQ  =  same  : go rest
                        |  otherwise      =  [x]   : go (y : ys)
      where
        (same, rest) = span (\z -> cmp x z == EQ) l
