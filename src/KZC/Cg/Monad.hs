{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    TakeK,
    TakesK,
    EmitK,
    EmitsK,

    Cg,
    CgEnv,
    CgStats(..),
    evalCg,

    withTakeK,
    withTakesK,
    withEmitK,
    withEmitsK,

    wrapTakeK,
    wrapTakesK,

    cgTake,
    cgTakes,
    cgEmit,
    cgEmits,

    extendVarCExps,
    lookupVarCExp,

    extendIVarCExps,
    lookupIVarCExp,

    extendTyVarTypes,
    lookupTyVarType,
    askTyVarTypeSubst,

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
    collectThreadBlock,
    collectBlock,

    inNewThreadBlock,
    inNewThreadBlock_,
    inNewBlock,
    inNewBlock_,

    appendTopDef,
    appendTopDefs,
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
    taintScope,
    newScope,
    taintAndUseCExp,
    useCIds,
    useCId,
    useCExp,

    hasLabel
  ) where

import Prelude hiding (elem)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)
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
import KZC.Core.Lint (Tc, liftTc, isInTopScope)
import KZC.Core.Syntax
import KZC.Label
import KZC.Monad
import KZC.Quote.C
import KZC.Staged
import KZC.Util.Env

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

-- | The 'Cg' monad.
type Cg l a = ReaderT (CgEnv l) (StateT (CgState l) Tc) a

data CgEnv l = CgEnv
    { takeCg     :: TakeK l
    , takesCg    :: TakesK l
    , emitCg     :: EmitK l
    , emitsCg    :: EmitsK l

    , varCExps   :: !(Map Var (CExp l))
    , ivarCExps  :: !(Map IVar (CExp l))
    , tyvarTypes :: !(Map TyVar Type)
    }

instance Show (CgEnv l) where
    show _ = "<Env>"

defaultCgEnv :: CgEnv l
defaultCgEnv = CgEnv
    { takeCg     = error "no take code generator"
    , takesCg    = error "no takes code generator"
    , emitCg     = error "no emit code generator"
    , emitsCg    = error "no emits code generator"

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
      stats   :: CgStats
    , -- | All labels used
      labels  :: Set l
    , -- | Current code block being generated
      code    :: Code
    , -- | C identifiers that are currently declared
      declared :: Set C.Id
    , -- | C identifiers that have been used
      used :: Set C.Id
    , -- | C identifiers that were declared prior to a code label
      tainted :: Set C.Id
    , -- | The set of tainted variables that have been used
      usedTainted :: Set C.Id
    }

defaultCgState :: IsLabel l => CgState l
defaultCgState = CgState
    { stats       = mempty
    , labels      = mempty
    , code        = mempty
    , declared    = mempty
    , used        = mempty
    , tainted     = mempty
    , usedTainted = mempty
    }

-- | Evaluate a 'Cg' action and return a list of 'C.Definition's.
evalCg :: IsLabel l => Cg l () -> KZC [C.Definition]
evalCg m = do
    s <- liftTc $ execStateT (runReaderT m defaultCgEnv) defaultCgState
    return $ (toList . codeDefs . code) s

withTakeK :: TakeK l -> Cg l a -> Cg l a
withTakeK f = local (\env -> env { takeCg = f})

withTakesK :: TakesK l -> Cg l a -> Cg l a
withTakesK f = local (\env -> env { takesCg = f})

withEmitK :: EmitK l -> Cg l a -> Cg l a
withEmitK f = local (\env -> env { emitCg = f})

withEmitsK :: EmitsK l -> Cg l a -> Cg l a
withEmitsK f = local (\env -> env { emitsCg = f})

wrapTakeK :: (TakeK l -> TakeK l) -> Cg l a -> Cg l a
wrapTakeK f = local (\env -> env { takeCg = f (takeCg env)})

wrapTakesK :: (TakesK l -> TakesK l) -> Cg l a -> Cg l a
wrapTakesK f = local (\env -> env { takesCg = f (takesCg env)})

cgTake :: TakeK l
cgTake tau klbl k = do
    f <- asks takeCg
    f tau klbl k

cgTakes :: TakesK l
cgTakes n tau klbl k = do
    f <- asks takesCg
    f n tau klbl k

cgEmit :: EmitK l
cgEmit tau ce klbl k = do
    f <- asks emitCg
    f tau ce klbl k

cgEmits :: EmitsK l
cgEmits iota tau ce klbl k = do
    f <- asks emitsCg
    f iota tau ce klbl k

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

collectThreadBlock :: Cg l a -> Cg l (Seq C.InitGroup, Seq C.Stm, a)
collectThreadBlock m = do
    (c, x) <- collect m
    tell c { codeThreadDecls       = mempty
           , codeThreadInitStms    = mempty
           , codeThreadCleanupStms = mempty
           , codeDecls             = mempty
           , codeStms              = mempty
           }
    return (codeThreadDecls c <> codeDecls c
           ,codeThreadInitStms c <> codeStms c <> codeThreadCleanupStms c
           ,x)

collectBlock :: Cg l a -> Cg l (Seq C.InitGroup, Seq C.Stm, a)
collectBlock m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty
           , codeStms  = mempty
           }

    -- Figure out the set of variables that were used after a label that
    -- occurred between their use and their declaration.
    usedAfterTaint <- gets usedTainted

    -- Partition the declarations into those that involve tainted variables and
    -- those that do not
    let isTainted :: C.InitGroup -> Bool
        isTainted decl = not $ Set.null $ cids `Set.intersection` usedAfterTaint
          where
            cids :: Set C.Id
            cids = Set.fromList (initIdents decl)

        taintedDecls, untaintedDecl :: Seq C.InitGroup
        (taintedDecls, untaintedDecl) = Seq.partition isTainted (codeDecls c)

    -- Any tainted declaration gets promoted to a thread-level declaration. The
    -- rest end up being returned.
    tell mempty { codeThreadDecls = taintedDecls }

    -- Remove declared variables from the state
    let vs :: Set C.Id
        vs = Set.fromList (initsIdents (toList (codeDecls c)))

    modify $ \s -> s { used        = used s Set.\\ vs
                     , declared    = declared s Set.\\ vs
                     , tainted     = tainted s Set.\\ vs
                     , usedTainted = usedTainted s Set.\\ vs
                     }

    -- Return the untainted declarations
    return (untaintedDecl, codeStms c, x)

inNewThreadBlock :: Cg l a -> Cg l ([C.BlockItem], a)
inNewThreadBlock m = do
    (decls, stms, x) <- collectThreadBlock m
    return ((map C.BlockDecl . toList) decls ++
            (map C.BlockStm .  toList) stms
           ,x)

inNewThreadBlock_ :: Cg l a -> Cg l [C.BlockItem]
inNewThreadBlock_ m =
    fst <$> inNewThreadBlock m

inNewBlock :: Cg l a -> Cg l ([C.BlockItem], a)
inNewBlock m = do
    (decls, stms, x) <- collectBlock m
    return ((map C.BlockDecl . toList) decls ++
            (map C.BlockStm .  toList) stms
           ,x)

inNewBlock_ :: Cg l a -> Cg l [C.BlockItem]
inNewBlock_ m =
    fst <$> inNewBlock m

appendTopDef :: C.Definition -> Cg l ()
appendTopDef cdef =
  tell mempty { codeDefs = Seq.singleton cdef }

appendTopDefs :: [C.Definition] -> Cg l ()
appendTopDefs cdefs =
  tell mempty { codeDefs = Seq.fromList cdefs }

appendTopDecl :: C.InitGroup -> Cg l ()
appendTopDecl cdecl =
  tell mempty { codeDefs = Seq.singleton (C.DecDef cdecl noLoc) }

appendTopDecls :: [C.InitGroup] -> Cg l ()
appendTopDecls cdecls =
  tell mempty { codeDefs = Seq.fromList [C.DecDef decl noLoc | decl <- cdecls] }

appendThreadDecl :: C.InitGroup -> Cg l ()
appendThreadDecl cdecl = tell mempty { codeThreadDecls = Seq.singleton cdecl }

appendThreadDecls :: [C.InitGroup] -> Cg l ()
appendThreadDecls cdecls = tell mempty { codeThreadDecls = Seq.fromList cdecls }

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
        s { declared = declared s <> Set.fromList (initIdents cdecl) }

appendDecls :: [C.InitGroup] -> Cg l ()
appendDecls cdecls = do
    tell mempty { codeDecls = Seq.fromList cdecls }
    modify $ \s ->
        s { declared = declared s <> Set.fromList (initsIdents cdecls) }

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

-- | Taint current declarations.
taintScope :: Cg l ()
taintScope = do
    cids <- gets declared
    modify $ \s -> s { tainted = tainted s <> cids }

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

-- | Taint and use a 'CExp'.
taintAndUseCExp :: forall l . CExp l -> Cg l ()
taintAndUseCExp ce = do
    cid <- taint ce
    modify $ \s -> s { tainted     = tainted s <> Set.singleton cid
                     , usedTainted = Set.insert cid (usedTainted s)
                     }
  where
    taint :: forall m . Monad m => CExp l -> m C.Id
    taint (CExp ce) = go ce
      where
        go :: C.Exp -> m C.Id
        go (C.Var cid _)          = return cid
        go (C.Member ce _ _)      = go ce
        go (C.PtrMember ce _ _)   = go ce
        go (C.Index ce _ _)       = go ce
        go (C.UnOp C.Deref ce _ ) = go ce
        go _                      = faildoc $ text "Cannot taint:" <+> ppr ce

    taint (CPtr ce)         = taint ce
    taint (CBitSlice ce)    = taint ce
    taint (CIdx _ ce _)     = taint ce
    taint (CSlice _ ce _ _) = taint ce
    taint (CAlias _ ce)     = taint ce
    taint ce                = faildoc $ text "Cannot taint:" <+> ppr ce

-- | Mark a set of C identifiers as used. This allows us to
-- track which C declarations are used after they have been tainted by an
-- intervening label.
useCIds :: Set C.Id -> Cg l ()
useCIds cids = do
    modify $ \s -> s { used = used s <> cids }
    taint <- gets tainted
    modify $ \s ->
        s { usedTainted = usedTainted s <>
                          Set.filter (`Set.member` taint) cids }

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

instance IfThenElse (CExp l) (Cg l ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]
