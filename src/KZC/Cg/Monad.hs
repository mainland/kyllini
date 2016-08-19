{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    Thread(..),

    GuardTakeK,
    TakeK,
    TakesK,
    EmitK,
    EmitsK,
    ExitK,

    Cg,
    CgEnv,
    CgStats(..),
    evalCg,

    saveCgEnv,

    withGuardTakeK,
    withTakeK,
    withTakesK,
    withEmitK,
    withEmitsK,
    withExitK,

    cgGuardTake,
    cgTake,
    cgTakes,
    cgEmit,
    cgEmits,
    cgExit,

    isFreeRunning,
    withFreeRunning,

    extendVarCExps,
    lookupVarCExp,

    extendIVarCExps,
    lookupIVarCExp,

    extendTyVarTypes,
    lookupTyVarType,
    askTyVarTypeSubst,

    addThread,
    getThreads,

    setUsesConsumerThread,
    getUsesConsumerThread,
    whenUsesConsumerThread,

    getStats,
    incDefaultInits,
    incMemCopies,
    incBitArrayCopies,

    collectLabels,
    useLabel,
    useLabels,
    isLabelUsed,

    tell,
    collect,
    collectDefinitions,
    collectDefinitions_,
    collectThreadDecls,
    collectThreadDecls_,
    collectDecls,
    collectDecls_,
    collectStms,
    collectStms_,
    collectCodeBlock,
    collectBlock,

    inNewCodeBlock,
    inNewCodeBlock_,
    inNewBlock,
    inNewBlock_,

    appendTopDef,
    appendTopDefs,
    appendTopFunDef,
    appendTopFunDefs,
    appendTopDecl,
    appendTopDecls,
    appendThreadDecl,
    appendThreadDecls,
    appendThreadInitStm,
    appendThreadCleanupStm,
    appendDecl,
    appendDecls,
    appendStm,
    appendStms,
    appendBlock,

    collectUsed,
    collectUsed_,

    newThreadScope,
    newLabelScope,
    newScope,
    promoteScope,
    useCIds,
    useCId,
    useCExp,

    hasLabel
  ) where

import Prelude hiding (elem)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad (when)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Primitive (PrimMonad(..))
import Control.Monad.Ref (MonadRef)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT,
                            execStateT,
                            gets,
                            modify)
import Data.Foldable (toList)
import Data.IORef (IORef)
import Data.Loc
import Data.Map (Map)
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Cg.CExp
import KZC.Cg.Code
import KZC.Core.Lint
import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Quote.C
import KZC.Staged
import KZC.Trace
import KZC.Uniq
import KZC.Util.Env

data Thread l = Thread
    { -- | Thread info struct, of type kz_tinfo_t
      threadInfo :: CExp l
     -- | Thread struct, of type kz_thread_t
    , thread  :: CExp l
     -- | Thread result
    , threadRes :: CExp l
     -- | Thread function
    , threadFun :: C.Id
    }
  deriving (Eq, Ord, Show)

-- | Generate code to guard a take.
type GuardTakeK l = Cg l ()

-- | Generate code to take a value of the specified type, jumping to the
-- specified label when the take is complete. A 'CExp' representing the taken
-- value is returned. We assume that the continuation labels the code that will
-- be generated immediately after the take.
type TakeK l = forall a . Type -> l -> (CExp l -> Cg l a) -> Cg l a

-- | Generate code to take multiple values.
type TakesK l = forall a . Int -> Type -> l -> (CExp l -> Cg l a) -> Cg l a

-- | Generate code to emit the specified value at the specified type, jumping to
-- the specified label when the take is complete. We assume that the
-- continuation labels the code that will be generated immediately after the
-- emit.
type EmitK l = forall a . Type -> CExp l -> l -> Cg l a -> Cg l a

-- | Generate code to emit multiple values.
type EmitsK l = forall a . Iota -> Type -> CExp l -> l -> Cg l a -> Cg l a

-- | Generate code to exit a computation. A computation is exited either when it
-- has no more input, or when it computes a result.
type ExitK l = Cg l ()

data CgEnv l = CgEnv
    { guardTakeCg :: GuardTakeK l
    , takeCg      :: TakeK l
    , takesCg     :: TakesK l
    , emitCg      :: EmitK l
    , emitsCg     :: EmitsK l
    , exitCg      :: ExitK l

    -- | 'True' if we are compiling in a free-running context, i.e., where we
    -- are the final consumer of input.
    , freeRunning :: !Bool

    , varCExps   :: !(Map Var (CExp l))
    , ivarCExps  :: !(Map IVar (CExp l))
    , tyvarTypes :: !(Map TyVar Type)
    }

instance Show (CgEnv l) where
    show _ = "<Env>"

defaultCgEnv :: CgEnv l
defaultCgEnv = CgEnv
    { guardTakeCg = error "no guard take code generator"
    , takeCg      = error "no take code generator"
    , takesCg     = error "no takes code generator"
    , emitCg      = error "no emit code generator"
    , emitsCg     = error "no emits code generator"
    , exitCg      = error "no exit continuation"

    , freeRunning = True

    , varCExps   = mempty
    , ivarCExps  = mempty
    , tyvarTypes = mempty
    }

data CgStats = CgStats
    { defaultInits   :: !Int
    , memCopies      :: !Int
    , bitArrayCopies :: !Int
    }

instance Monoid CgStats where
    mempty = CgStats
        { defaultInits   = 0
        , memCopies      = 0
        , bitArrayCopies = 0
        }

    x `mappend` y =
        CgStats { defaultInits   = defaultInits x + defaultInits y
                , memCopies      = memCopies x + memCopies y
                , bitArrayCopies = bitArrayCopies x + bitArrayCopies y
                }

instance Pretty CgStats where
    ppr stats =
        text "Defaulted values:" <+> ppr (defaultInits stats) </>
        text "   Memory copies:" <+> ppr (memCopies stats) </>
        text "Bit array copies:" <+> ppr (bitArrayCopies stats)

data CgState l = CgState
    { -- | Codegen statistics
      stats :: CgStats
    , -- | Threads
      threads :: [Thread l]
    , -- | All labels used
      labels :: Set l
    , -- | Generated code
      code :: Code
    , -- | C identifiers that have been used
      used :: Set C.Id
    , -- | C identifiers that are currently declared in thread scope.
      threadDeclared :: Set C.Id
    , -- | C identifiers that were declared but are now out of scope due to a
      -- new thread.
      outOfThreadScope :: Set C.Id
    , -- | C identifiers that are currently locally declared. This is not the
      -- same as the set of identifiers in the 'code' field of our 'CgState'
      -- because we may be in a nested scope.
      localDeclared :: Set C.Id
    , -- | C identifiers that were declared but are now out of scope due to an
      -- intervening code label. If we use one of these, we need to promote its
      -- declaration.
      outOfLocalScope :: Set C.Id
    , -- | Set if consumer threads were used
      usesConsumerThreads :: Bool
    }

defaultCgState :: IsLabel l => CgState l
defaultCgState = CgState
    { stats               = mempty
    , threads             = mempty
    , labels              = mempty
    , code                = mempty
    , used                = mempty
    , threadDeclared      = mempty
    , outOfThreadScope    = mempty
    , localDeclared       = mempty
    , outOfLocalScope     = mempty
    , usesConsumerThreads = False
    }

-- | The 'Cg' monad.
newtype Cg l a = Cg { unCg :: ReaderT (CgEnv l) (StateT (CgState l) Tc) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadException,
              MonadReader (CgEnv l),
              MonadState (CgState l),
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadRef IORef,
              MonadTc,
              MonadTcRef)

instance PrimMonad (Cg l) where
    type PrimState (Cg l) = PrimState Tc
    primitive = Cg . primitive

-- | Evaluate a 'Cg' action and return a list of 'C.Definition's.
evalCg :: IsLabel l => Cg l () -> KZC [C.Definition]
evalCg m = do
    s <- liftTc $ execStateT (runReaderT (unCg m) defaultCgEnv) defaultCgState
    return $ toList $ (codeDefs . code) s <> (codeFunDefs . code) s

-- | Save the current codegen environment in the form of a function that can
-- restore it.
saveCgEnv :: Cg l (Cg l a -> Cg l a)
saveCgEnv = do
    (s, a, c)   <- askSTIndTypes
    env         <- ask
    return $ localSTIndTypes (Just (s, a, c)) . local (const env)

withGuardTakeK :: GuardTakeK l -> Cg l a -> Cg l a
withGuardTakeK f = local (\env -> env { guardTakeCg = f})

withTakeK :: TakeK l -> Cg l a -> Cg l a
withTakeK f = local (\env -> env { takeCg = f})

withTakesK :: TakesK l -> Cg l a -> Cg l a
withTakesK f = local (\env -> env { takesCg = f})

withEmitK :: EmitK l -> Cg l a -> Cg l a
withEmitK f = local (\env -> env { emitCg = f})

withEmitsK :: EmitsK l -> Cg l a -> Cg l a
withEmitsK f = local (\env -> env { emitsCg = f})

withExitK :: ExitK l -> Cg l a -> Cg l a
withExitK f = local (\env -> env { exitCg = f})

cgGuardTake :: GuardTakeK l
cgGuardTake = do
    f <- asks guardTakeCg
    f

cgTake :: TakeK l
cgTake tau klbl k = do
    f <- asks takeCg
    cgGuardTake
    f tau klbl k

cgTakes :: TakesK l
cgTakes n tau klbl k = do
    f <- asks takesCg
    cgGuardTake
    f n tau klbl k

cgEmit :: EmitK l
cgEmit tau ce klbl k = do
    f <- asks emitCg
    f tau ce klbl k

cgEmits :: EmitsK l
cgEmits iota tau ce klbl k = do
    f <- asks emitsCg
    f iota tau ce klbl k

cgExit :: ExitK l
cgExit = do
    f <- asks exitCg
    f

isFreeRunning :: Cg l Bool
isFreeRunning = asks freeRunning

withFreeRunning :: Bool -> Cg l a -> Cg l a
withFreeRunning free = local $ \env -> env { freeRunning = free }

extendVarCExps :: [(Var, CExp l)] -> Cg l a -> Cg l a
extendVarCExps = extendEnv varCExps (\env x -> env { varCExps = x })

lookupVarCExp :: Var -> Cg l (CExp l)
lookupVarCExp v = do
    ce <- lookupEnv varCExps onerr v
    useCExp ce
    return ce
  where
    onerr = faildoc $
            text "Compiled variable" <+> ppr v <+> text "not in scope"

extendIVarCExps :: [(IVar, CExp l)] -> Cg l a -> Cg l a
extendIVarCExps = extendEnv ivarCExps (\env x -> env { ivarCExps = x })

lookupIVarCExp :: IVar -> Cg l (CExp l)
lookupIVarCExp v =
    lookupEnv ivarCExps onerr v
  where
    onerr = faildoc $
            text "Compiled array size variable" <+> ppr v <+>
            text "not in scope"

extendTyVarTypes :: [(TyVar, Type)] -> Cg l a -> Cg l a
extendTyVarTypes = extendEnv tyvarTypes (\env x -> env { tyvarTypes = x })

lookupTyVarType :: TyVar -> Cg l Type
lookupTyVarType alpha =
    lookupEnv tyvarTypes onerr alpha
  where
    onerr = faildoc $
            text "Instantiated type variable" <+> ppr alpha <+>
            text "not in scope"

-- | Return a function that substitutes type variables for their current
-- instantiation.
askTyVarTypeSubst :: Cg l (Map TyVar Type)
askTyVarTypeSubst = asks tyvarTypes

addThread :: Thread l -> Cg l ()
addThread t = modify $ \s -> s { threads = t : threads s }

getThreads :: Cg l [Thread l]
getThreads = gets (reverse . threads)

setUsesConsumerThread :: Cg l ()
setUsesConsumerThread = modify $ \s -> s { usesConsumerThreads = True }

getUsesConsumerThread :: Cg l Bool
getUsesConsumerThread = gets usesConsumerThreads

whenUsesConsumerThread :: Cg l () -> Cg l ()
whenUsesConsumerThread m = do
    flag <- getUsesConsumerThread
    when flag m

getStats :: Cg l CgStats
getStats = gets stats

modifyStats :: (CgStats -> CgStats) -> Cg l ()
modifyStats f = modify $ \s -> s { stats = f (stats s) }

incDefaultInits :: Cg l ()
incDefaultInits =
    modifyStats $ \s -> s { defaultInits = defaultInits s + 1 }

incMemCopies :: Cg l ()
incMemCopies =
    modifyStats $ \s -> s { memCopies = memCopies s + 1 }

incBitArrayCopies :: Cg l ()
incBitArrayCopies =
    modifyStats $ \s -> s { bitArrayCopies =bitArrayCopies s + 1 }

collectLabels :: IsLabel l => Cg l a -> Cg l (Set l, a)
collectLabels m = do
    old_labels <- gets labels
    modify $ \s -> s { labels = mempty }
    x    <- m
    lbls <- gets labels
    modify $ \s -> s { labels = old_labels }
    return (lbls, x)

useLabel :: IsLabel l => l -> Cg l ()
useLabel lbl =
    modify $ \s -> s { labels = Set.insert lbl (labels s) }

useLabels :: IsLabel l => Set l -> Cg l ()
useLabels lbls =
    modify $ \s -> s { labels = labels s `Set.union` lbls }

isLabelUsed :: IsLabel l => l -> Cg l Bool
isLabelUsed lbl =
    gets (Set.member lbl . labels)

tell :: Code -> Cg l ()
tell c = modify $ \s -> s { code = code s <> c }

collect :: Cg l a -> Cg l (Code, a)
collect m = do
    old_code <- gets code
    modify $ \s -> s { code = mempty }
    x <- m
    c <- gets code
    modify $ \s -> s { code = old_code }
    return (c, x)

collectDefinitions :: Cg l a -> Cg l ([C.Definition], a)
collectDefinitions m = do
    (c, x) <- collect m
    tell c { codeDefs = mempty }
    return (toList (codeDefs c), x)

collectDefinitions_ :: Cg l () -> Cg l [C.Definition]
collectDefinitions_ m = fst <$> collectDefinitions m

collectThreadDecls :: Cg l a -> Cg l ([C.InitGroup], a)
collectThreadDecls m = do
    (c, x) <- collect m
    tell c { codeThreadDecls = mempty }
    return (toList (codeThreadDecls c), x)

collectThreadDecls_ :: Cg l () -> Cg l [C.InitGroup]
collectThreadDecls_ m = fst <$> collectThreadDecls m

collectDecls :: Cg l a -> Cg l ([C.InitGroup], a)
collectDecls m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty }
    return (toList (codeDecls c), x)

collectDecls_ :: Cg l () -> Cg l [C.InitGroup]
collectDecls_ m = fst <$> collectDecls m

collectStms :: Cg l a -> Cg l ([C.Stm], a)
collectStms m = do
    (c, x) <- collect m
    tell c { codeStms = mempty }
    return (toList (codeStms c), x)

collectStms_ :: Cg l () -> Cg l [C.Stm]
collectStms_ m = fst <$> collectStms m

collectCodeBlock :: Cg l a -> Cg l (CodeBlock, a)
collectCodeBlock m = do
    (c, x) <- collect $ do
              (decls, stms, x) <- collectBlock m
              tell mempty { codeDecls = decls, codeStms = stms }
              return x

    tell c { codeThreadDecls       = mempty
           , codeThreadInitStms    = mempty
           , codeThreadCleanupStms = mempty
           , codeDecls             = mempty
           , codeStms              = mempty
           }

    -- Figure out which local declarations we need to promote.
    outOfScope                  <- gets outOfThreadScope
    (promote, retain, initStms) <- promoteOutOfScope outOfScope (codeThreadDecls c)

    -- Remove retained declarations from user-tracking state.
    removeUsed retain
    removeThreadDeclared (codeThreadDecls c)

    -- Promote declarations to top level.
    appendTopDecls (toList promote)

    return (CodeBlock { blockDecls       = retain <> codeDecls c
                      , blockInitStms    = initStms <> codeThreadInitStms c
                      , blockStms        = codeStms c
                      , blockCleanupStms = codeThreadCleanupStms c
                      }
           ,x)
  where
    removeThreadDeclared :: Seq C.InitGroup -> Cg l ()
    removeThreadDeclared decls =
        modify $ \s -> s { threadDeclared    = threadDeclared s Set.\\ cids
                         , outOfThreadScope  = outOfThreadScope s Set.\\ cids
                         }
     where
        cids :: Set C.Id
        cids = Set.fromList (initsIdents (toList decls))

collectBlock :: Cg l a -> Cg l (Seq C.InitGroup, Seq C.Stm, a)
collectBlock m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty
           , codeStms  = mempty
           }

    -- Figure out which local declarations we need to promote.
    outOfScope                  <- gets outOfLocalScope
    (promote, retain, initStms) <- promoteOutOfScope outOfScope (codeDecls c)

    -- Remove retained declarations from user-tracking state.
    removeUsed retain
    removeLocalDeclared (codeDecls c)

    -- Promote declarations to thread scope.
    appendThreadDecls (toList promote)

    -- Return the untainted declarations
    return (retain, initStms <> codeStms c, x)
  where
    removeLocalDeclared :: Seq C.InitGroup -> Cg l ()
    removeLocalDeclared decls =
        modify $ \s -> s { localDeclared    = localDeclared s Set.\\ cids
                         , outOfLocalScope  = outOfLocalScope s Set.\\ cids
                         }
      where
        cids :: Set C.Id
        cids = Set.fromList (initsIdents (toList decls))

removeUsed :: Seq C.InitGroup -> Cg l ()
removeUsed decls =
    modify $ \s -> s { used = used s Set.\\ cids }
  where
    cids :: Set C.Id
    cids = Set.fromList (initsIdents (toList decls))

promoteOutOfScope :: Set C.Id
                  -> Seq C.InitGroup
                  -> Cg l (Seq C.InitGroup,
                           Seq C.InitGroup,
                           Seq C.Stm)
promoteOutOfScope outOfScope cdecls = do
    -- Figure out the set of variables that were used after they went out of
    -- scope.
    escaped <- Set.intersection <$> gets used <*> pure outOfScope

    -- Partition the declarations into those that involve tainted variables and
    -- those that do not
    let promote, retain :: Seq C.InitGroup
        (promote, retain) = Seq.partition (declIn escaped) cdecls

    let promoteInits :: [C.InitGroup]
        promoteInitStms0 :: [Seq C.Stm]
        promoteInitStms :: Seq C.Stm
        (promoteInits, promoteInitStms0) =
            unzip $ map splitInitialization $ toList promote
        promoteInitStms = mconcat promoteInitStms0

    when (not (Seq.null promoteInitStms)) $
      traceCg $ nest 2 $ text "Promoted uninitialized:" </>
        stack (map ppr (toList promoteInitStms))

    return (Seq.fromList promoteInits, retain, promoteInitStms)
  where
    declIn :: Set C.Id -> C.InitGroup -> Bool
    declIn cids decl = not $ Set.null $ cids' `Set.intersection` cids
      where
        cids' :: Set C.Id
        cids' = Set.fromList (initIdents decl)

    splitInitialization :: C.InitGroup -> (C.InitGroup, Seq C.Stm)
    splitInitialization (C.InitGroup dspec attr inits s) =
        (C.InitGroup dspec attr inits' s, mconcat stms)
      where
        inits' :: [C.Init]
        stms :: [Seq C.Stm]
        (inits', stms) = unzip $ map splitInit inits

        splitInit :: C.Init -> (C.Init, Seq C.Stm)
        splitInit (C.Init cid decl asm (Just (C.ExpInitializer e _)) attr s) =
            (C.Init cid decl asm Nothing attr s,
             Seq.singleton [cstm|$id:cid = $e;|])

        splitInit (C.Init cid decl asm (Just C.CompoundInitializer{}) attr s) =
            (C.Init cid decl asm Nothing attr s,
             Seq.singleton (czero ctau cid))
          where
            ctau :: C.Type
            ctau = C.Type dspec decl s

        splitInit ini =
            (ini, mempty)

    splitInitialization group = (group, mempty)

    czero :: C.Type -> C.Id -> C.Stm
    czero ctau cid
        | isArray ctau = [cstm|kz_zero($id:cid, sizeof($ty:ctau));|]
        | otherwise    = [cstm|kz_zero(&$id:cid, sizeof($ty:ctau));|]
      where
        isArray :: C.Type -> Bool
        isArray (C.Type _ C.Array{} _) = True
        isArray _                      = False

inNewCodeBlock :: Cg l a -> Cg l (CodeBlock, a)
inNewCodeBlock = collectCodeBlock

inNewCodeBlock_ :: Cg l a -> Cg l CodeBlock
inNewCodeBlock_ m =
    fst <$> inNewCodeBlock m

inNewBlock :: Cg l a -> Cg l ([C.BlockItem], a)
inNewBlock m = do
    (decls, stms, x) <- collectBlock m
    return ((map C.BlockDecl . toList) decls ++
            (map C.BlockStm .  toList) stms
           ,x)

inNewBlock_ :: Cg l a -> Cg l [C.BlockItem]
inNewBlock_ m =
    fst <$> inNewBlock m

-- | Append a top-level definition.
appendTopDef :: C.Definition -> Cg l ()
appendTopDef cdef =
  tell mempty { codeDefs = Seq.singleton cdef }

-- | Append top-level definitions.
appendTopDefs :: [C.Definition] -> Cg l ()
appendTopDefs cdefs =
  tell mempty { codeDefs = Seq.fromList cdefs }

-- | Append a top-level function definition. Function definitions appear after
-- regular top-level definitions.
appendTopFunDef :: C.Definition -> Cg l ()
appendTopFunDef cdef =
  tell mempty { codeFunDefs = Seq.singleton cdef }

-- | Append top-level functions definitions.
appendTopFunDefs :: [C.Definition] -> Cg l ()
appendTopFunDefs cdefs =
  tell mempty { codeFunDefs = Seq.fromList cdefs }

appendTopDecl :: C.InitGroup -> Cg l ()
appendTopDecl cdecl =
  tell mempty { codeDefs = Seq.singleton (C.DecDef cdecl noLoc) }

appendTopDecls :: [C.InitGroup] -> Cg l ()
appendTopDecls cdecls =
  tell mempty { codeDefs = Seq.fromList [C.DecDef decl noLoc | decl <- cdecls] }

appendThreadDecl :: C.InitGroup -> Cg l ()
appendThreadDecl cdecl = do
    tell mempty { codeThreadDecls = Seq.singleton cdecl }
    modify $ \s ->
      s { threadDeclared = threadDeclared s <> Set.fromList (initIdents cdecl) }

appendThreadDecls :: [C.InitGroup] -> Cg l ()
appendThreadDecls cdecls = do
    tell mempty { codeThreadDecls = Seq.fromList cdecls }
    modify $ \s ->
      s { threadDeclared = threadDeclared s <> Set.fromList (initsIdents cdecls) }

appendThreadInitStm :: C.Stm -> Cg l ()
appendThreadInitStm cstm =
  tell mempty { codeThreadInitStms = Seq.singleton cstm }

appendThreadCleanupStm :: C.Stm -> Cg l ()
appendThreadCleanupStm cstm =
  tell mempty { codeThreadCleanupStms = Seq.singleton cstm }

appendDecl :: C.InitGroup -> Cg l ()
appendDecl cdecl = do
    tell mempty { codeDecls = Seq.singleton cdecl }
    modify $ \s ->
      s { localDeclared = localDeclared s <> Set.fromList (initIdents cdecl) }

appendDecls :: [C.InitGroup] -> Cg l ()
appendDecls cdecls = do
    tell mempty { codeDecls = Seq.fromList cdecls }
    modify $ \s ->
      s { localDeclared = localDeclared s <> Set.fromList (initsIdents cdecls) }

appendStm :: C.Stm -> Cg l ()
appendStm cstm = tell mempty { codeStms = Seq.singleton cstm }

appendStms :: [C.Stm] -> Cg l ()
appendStms cstms = tell mempty { codeStms = Seq.fromList cstms }

appendBlock :: [C.BlockItem] -> Cg l ()
appendBlock citems
    | all isBlockStm citems = appendStms [stm | C.BlockStm stm <- citems]
    | otherwise             = appendStm [cstm|{ $items:citems }|]
  where
    isBlockStm :: C.BlockItem -> Bool
    isBlockStm C.BlockStm{} = True
    isBlockStm _            = False

-- | Collect the C identifiers used in a computation.
collectUsed :: Cg l a -> Cg l (Set C.Id, a)
collectUsed m = do
    vs_old <- gets used
    modify $ \s -> s { used = mempty }
    x <- m
    vs <- gets used
    modify $ \s -> s { used = vs_old <> vs }
    return (vs, x)

collectUsed_ :: Cg l () -> Cg l (Set C.Id)
collectUsed_ m = fst <$> collectUsed m

-- | Start a new thread scope.
newThreadScope :: Cg l ()
newThreadScope = do
    cids <- (<>) <$> gets localDeclared <*> gets threadDeclared
    modify $ \s -> s { outOfThreadScope = outOfThreadScope s <> cids }

-- | Start a new label scope.
newLabelScope :: Cg l ()
newLabelScope = do
    cids <- gets localDeclared
    modify $ \s -> s { outOfLocalScope = outOfLocalScope s <> cids }

-- | Run the continuation, enclosing the code it produces in a single block.
newScope :: Cg l a -> Cg l a
newScope k = do
    isTop <- isInTopScope
    if isTop
      then k
      else do
        (decls, stms, x) <- collectBlock k
        appendStms $ mkBlock decls stms
        return x
  where
    mkBlock :: Seq C.InitGroup -> Seq C.Stm -> [C.Stm]
    mkBlock decls stms | Seq.null decls =
        toList stms

    mkBlock decls stms =
        [cstm|{ $items:citems }|] : toList cafter
      where
        cbefore, cafter :: Seq C.Stm
        (cbefore, cafter) = Seq.spanl (not . hasLabel) stms

        citems :: [C.BlockItem]
        citems = (map C.BlockDecl . toList) decls ++
                 (map C.BlockStm . toList) cbefore

-- | Promote the identifier used in a 'CExp' out of local scope.
promoteScope :: forall l . CExp l -> Cg l ()
promoteScope ce = do
    cid <- cexpId ce
    modify $ \s -> s { used            = Set.insert cid (used s)
                     , outOfLocalScope = Set.insert cid (outOfLocalScope s)
                     }
  where
    cexpId :: forall m . Monad m => CExp l -> m C.Id
    cexpId (CExp ce) = go ce
      where
        go :: C.Exp -> m C.Id
        go (C.Var cid _)          = return cid
        go (C.Member ce _ _)      = go ce
        go (C.PtrMember ce _ _)   = go ce
        go (C.Index ce _ _)       = go ce
        go (C.UnOp C.Deref ce _ ) = go ce
        go _                      = faildoc $ text "Cannot find root identifier:" <+> ppr ce

    cexpId (CPtr ce)         = cexpId ce
    cexpId (CBitSlice ce)    = cexpId ce
    cexpId (CIdx _ ce _)     = cexpId ce
    cexpId (CSlice _ ce _ _) = cexpId ce
    cexpId (CAlias _ ce)     = cexpId ce
    cexpId ce                = faildoc $ text "Cannot find root identifier:" <+> ppr ce

-- | Mark a set of C identifiers as used. This allows us to
-- track which C declarations are used after they have been tainted by an
-- intervening label.
useCIds :: Set C.Id -> Cg l ()
useCIds cids =
    modify $ \s -> s { used = used s <> cids }

-- | Mark a C identifier as used.
useCId :: C.Id -> Cg l ()
useCId cid =
    useCIds (Set.singleton cid)

-- | Mark a 'CExp' as having been used. This allows us to track which C
-- declarations are used after they have been tainted by an intervening label.
useCExp :: forall l . CExp l -> Cg l ()
useCExp = use
  where
    use ::CExp l -> Cg l ()
    use (CExp ce) = go ce
      where
        go :: C.Exp -> Cg l ()
        go (C.Var cid _)          = useCId cid
        go (C.BinOp _ ce1 ce2 _)  = go ce1 >> go ce2
        go (C.Assign ce1 _ ce2 _) = go ce1 >> go ce2
        go (C.PreInc ce _)        = go ce
        go (C.PostInc ce _)       = go ce
        go (C.PreDec ce _)        = go ce
        go (C.PostDec ce _)       = go ce
        go (C.UnOp _ ce _)        = go ce
        go (C.Cast _ ce _)        = go ce
        go (C.Cond ce1 ce2 ce3 _) = go ce1 >> go ce2 >> go ce3
        go (C.Member ce _ _)      = go ce
        go (C.PtrMember ce _ _)   = go ce
        go (C.Index ce1 ce2 _)    = go ce1 >> go ce2
        go _                      = return ()

    use (CPtr ce)            = use ce
    use (CIdx _ ce1 ce2)     = use ce1 >> use ce2
    use (CSlice _ ce1 ce2 _) = use ce1 >> use ce2
    use (CStruct flds)       = mapM_ (use . snd) flds
    use (CAlias _ ce)        = use ce
    use _                    = return ()

initIdents :: C.InitGroup -> [C.Id]
initIdents (C.InitGroup _ _ inits _) = [ident | C.Init ident _ _ _ _ _ <- inits]
initIdents _                         = []

initsIdents :: [C.InitGroup] -> [C.Id]
initsIdents decls = [ident | C.InitGroup _ _ inits _ <- decls,
                             C.Init ident _ _ _ _ _ <- inits]

-- | Return 'True' if the given 'C.Stm' contains a label.
hasLabel :: C.Stm -> Bool
hasLabel C.Label{}               = True
hasLabel (C.Case _ s _)          = hasLabel s
hasLabel (C.Default s _)         = hasLabel s
hasLabel (C.Block items _)       = any hasLabel [s | C.BlockStm s <- items]
hasLabel (C.If _ s Nothing _)    = hasLabel s
hasLabel (C.If _ s1 (Just s2) _) = hasLabel s1 || hasLabel s2
hasLabel (C.Switch _ s _)        = hasLabel s
hasLabel (C.While _ s _)         = hasLabel s
hasLabel (C.DoWhile s _ _)       = hasLabel s
hasLabel (C.For _ _ _ s _)       = hasLabel s
hasLabel (C.Comment _ s _)       = hasLabel s
hasLabel (C.AntiComment _ s _)   = hasLabel s
hasLabel _                       = False

instance IfThenElse C.Exp (Cg l ()) where
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]

instance IfThenElse (CExp l) (Cg l ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]
