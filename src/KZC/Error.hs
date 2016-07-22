{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Error
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Error (
    PrettyException(..),
    prettyToException,
    prettyFromException,

    MonadErr(..),
    withLocContext,
    alwaysWithLocContext,
    panicdoc,
    errdoc,
    warndoc,

    warnWhen,
    warndocWhen,

    ErrorContext(..),
    ContextException(..),
    toContextException,
    throwContextException,
    catchContextException,

    FailException(..),
    WarnException(..),

    checkDuplicates
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Monad.Error (Error, ErrorT(..))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Exception (Exception(..),
                                MonadException,
                                SomeException,
                                catch,
                                throw)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State.Strict as S (StateT(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer.Strict as S (WriterT(..))
import Data.List (sortBy)
import Data.Loc
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid)
#endif /* !MIN_VERSION_base(4,8,0) */
import Data.Ord (comparing)
import Data.Typeable (Typeable, cast)
import Text.PrettyPrint.Mainland

import KZC.Flags
import KZC.Globals
import KZC.Pretty

data PrettyException = forall a . (Pretty a, Exception a) => PrettyException a
  deriving (Typeable)

instance Pretty PrettyException where
    ppr (PrettyException e) = ppr e

instance Show PrettyException where
    show = pretty 80 . ppr

instance Exception PrettyException

prettyToException :: (Pretty a, Exception a)
                  => a -> SomeException
prettyToException = toException . PrettyException

prettyFromException :: (Pretty a, Exception a)
                    => SomeException -> Maybe a
prettyFromException x = do
    PrettyException a <- fromException x
    cast a

class (MonadFlags m, MonadException m) => MonadErr m where
    askErrCtx    :: m [ErrorContext]
    localErrCtx  :: ([ErrorContext] -> [ErrorContext]) -> m a -> m a

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
        ctx <- askErrCtx
        displayWarning (toContextException ctx ex_warn)
      where
        ex_warn :: WarnException
        ex_warn = WarnException (toException ex)

instance MonadErr m => MonadErr (MaybeT m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = MaybeT $ localErrCtx ctx (runMaybeT m)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

#if !MIN_VERSION_base(4,8,0)
instance (Error e, MonadErr m) => MonadErr (ErrorT e m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = ErrorT $ localErrCtx ctx (runErrorT m)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn
#endif /* !MIN_VERSION_base(4,8,0) */

instance (MonadErr m) => MonadErr (ExceptT e m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = ExceptT $ localErrCtx ctx (runExceptT m)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance MonadErr m => MonadErr (ReaderT r m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = ReaderT $ \r -> localErrCtx ctx (runReaderT m r)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance MonadErr m => MonadErr (StateT r m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = StateT $ \s -> localErrCtx ctx (runStateT m s)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance MonadErr m => MonadErr (S.StateT r m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = S.StateT $ \s -> localErrCtx ctx (S.runStateT m s)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance (Monoid w, MonadErr m) => MonadErr (WriterT w m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = WriterT $ localErrCtx ctx (runWriterT m)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

instance (Monoid w, MonadErr m) => MonadErr (S.WriterT w m) where
    askErrCtx         = lift askErrCtx
    localErrCtx ctx m = S.WriterT $ localErrCtx ctx (S.runWriterT m)

    displayWarning = lift . displayWarning

    panic = lift . panic
    err   = lift . err
    warn  = lift . warn

withErrCtx :: MonadErr m => ErrorContext -> m a -> m a
withErrCtx ctx = localErrCtx (ctx :)

withLocContext :: (Located a, MonadErr m) => a -> Doc -> m b -> m b
withLocContext a doc = withErrCtx (ErrorContext False loc doc)
  where
    loc :: Loc
    loc = locOf a

alwaysWithLocContext :: (Located a, MonadErr m) => a -> Doc -> m b -> m b
alwaysWithLocContext a doc = withErrCtx (ErrorContext True loc doc)
  where
    loc :: Loc
    loc = locOf a

panicdoc :: MonadErr m => Doc -> m a
panicdoc msg = panic (FailException msg)

errdoc :: MonadErr m => Doc -> m ()
errdoc msg = err (FailException msg)

warndoc :: MonadErr m => Doc -> m ()
warndoc msg = warn (FailException msg)

warnWhen :: (Exception e, MonadErr m) => WarnFlag -> e -> m ()
warnWhen f e =
    whenWarnFlag f $ do
      isErr <- asksFlags (testWerrorFlag f)
      if isErr
        then err e
        else warn e

warndocWhen :: MonadErr m => WarnFlag -> Doc -> m ()
warndocWhen f msg = warnWhen f (FailException msg)

data ErrorContext = ErrorContext { ctxAlways :: Bool
                                 , ctxLoc    :: Loc
                                 , ctxDoc    :: Doc
                                 }
  deriving (Typeable)

data ContextException = ContextException [ErrorContext] SomeException
  deriving (Typeable)

instance Pretty ContextException where
    ppr (ContextException ctx e) =
        case [loc | ErrorContext _ loc@Loc{} _ <- ctx'] of
          loc : _  -> nest 4 $
                      ppr loc <> text ":" </>
                      pprEx <> pprDocs (map ctxDoc ctx')
          _        -> pprEx <> pprDocs (map ctxDoc ctx')
      where
        pprDocs :: [Doc] -> Doc
        pprDocs []    = empty
        pprDocs docs  = line <> stack docs

        ctx' :: [ErrorContext]
        ctx' = go maxErrContext ctx
          where
            go :: Int -> [ErrorContext] -> [ErrorContext]
            go _ []                                  = []
            go n (ctx@(ErrorContext True _ _):ctxs)  = ctx : go n ctxs
            go 0 (ErrorContext False _ _:ctxs)       = go 0 ctxs
            go n (ctx@(ErrorContext False _ _):ctxs) = ctx : go (n-1) ctxs

        pprEx :: Doc
        pprEx = case fromException e of
                  Just (PrettyException e') -> ppr e'
                  _                         -> (string . show) e

instance Show ContextException where
    show = pretty 80 . ppr

instance Exception ContextException where
    toException   = prettyToException
    fromException = prettyFromException

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

data FailException = FailException Doc
  deriving (Typeable)

instance Show FailException where
    show = pretty 80 . ppr

instance Pretty FailException where
    ppr (FailException msg) = msg

instance Exception FailException where
    toException   = prettyToException
    fromException = prettyFromException

data WarnException = WarnException SomeException
  deriving (Typeable)

instance Exception WarnException where
    toException   = prettyToException
    fromException = prettyFromException

instance Pretty WarnException where
    ppr (WarnException e) =
        text "Warning:" <+>
        case fromException e of
          Just (PrettyException e') -> ppr e'
          _                         -> (string . show) e

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
