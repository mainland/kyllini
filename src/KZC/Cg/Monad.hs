{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2014-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    Cg,
    CgEnv,
    CgStats(..),
    evalCg,

    extendVarCExps,
    lookupVarCExp,

    extendIVarCExps,
    lookupIVarCExp,

    extendTyVarTypes,
    lookupTyVarType,
    askTyVarTypeSubst,

    localRefFlowModVars,
    askRefFlowModVar,

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

    gensym,

    collectLabels,
    useLabel,
    useLabels,
    isLabelUsed,

    getStats,
    incMemCopies,
    incBitArrayCopies
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
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Auto.Lint (Tc, liftTc)
import KZC.Auto.Syntax
import KZC.Cg.CExp
import KZC.Cg.Code
import KZC.Label
import KZC.Monad
import KZC.Monad.SEFKT
import KZC.Quote.C
import KZC.Staged
import KZC.Uniq
import KZC.Util.Env

-- | The 'Cg' monad.
type Cg l a = SEFKT (ReaderT (CgEnv l) (StateT (CgState l) Tc)) a

data CgEnv l = CgEnv
    { varCExps    :: Map Var (CExp l)
    , ivarCExps   :: Map IVar (CExp l)
    , tyvarTypes  :: Map TyVar Type
    , -- | Variables defined using refs that are then modified before some use
      -- of the variable.
      refFlowModVars :: Set Var
    }

instance Show (CgEnv l) where
    show _ = "<Env>"

defaultCgEnv :: CgEnv l
defaultCgEnv = CgEnv
    { varCExps       = mempty
    , ivarCExps      = mempty
    , tyvarTypes     = mempty
    , refFlowModVars = mempty
    }

data CgStats = CgStats
    { memCopies      :: !Int
    , bitArrayCopies :: !Int
    }

instance Monoid CgStats where
    mempty = CgStats
        { memCopies      = 0
        , bitArrayCopies = 0
        }

    x `mappend` y =
        CgStats { memCopies      = memCopies x + memCopies y
                , bitArrayCopies = bitArrayCopies x + bitArrayCopies y
                }

instance Pretty CgStats where
    ppr stats =
        text "   Memory copies:" <+> ppr (memCopies stats) </>
        text "Bit array copies:" <+> ppr (bitArrayCopies stats)

data CgState l = CgState
    { labels :: Set l
    , code   :: Code
    , stats  :: CgStats
    }

defaultCgState :: IsLabel l => CgState l
defaultCgState = CgState
    { labels = mempty
    , code   = mempty
    , stats  = mempty
    }

-- | Evaluate a 'Cg' action and return a list of 'C.Definition's.
evalCg :: IsLabel l => Cg l () -> KZC [C.Definition]
evalCg m = do
    s <- liftTc $ execStateT (runReaderT (runSEFKT m) defaultCgEnv) defaultCgState
    return $ (toList . codeDefs . code) s

extendVarCExps :: [(Var, CExp l)] -> Cg l a -> Cg l a
extendVarCExps ves m =
    extendEnv varCExps (\env x -> env { varCExps = x }) ves m

lookupVarCExp :: Var -> Cg l (CExp l)
lookupVarCExp v =
    lookupEnv varCExps onerr v
  where
    onerr = faildoc $
            text "Compiled variable" <+> ppr v <+> text "not in scope"

extendIVarCExps :: [(IVar, CExp l)] -> Cg l a -> Cg l a
extendIVarCExps ves m =
    extendEnv ivarCExps (\env x -> env { ivarCExps = x }) ves m

lookupIVarCExp :: IVar -> Cg l (CExp l)
lookupIVarCExp v =
    lookupEnv ivarCExps onerr v
  where
    onerr = faildoc $
            text "Compiled array size variable" <+> ppr v <+>
            text "not in scope"

extendTyVarTypes :: [(TyVar, Type)] -> Cg l a -> Cg l a
extendTyVarTypes tvtaus m =
    extendEnv tyvarTypes (\env x -> env { tyvarTypes = x }) tvtaus m

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

-- | Specify the set of variables defined using refs that are then modified
-- before some use of the variable they flow to.
localRefFlowModVars :: Set Var -> Cg l a -> Cg l a
localRefFlowModVars vs k =
    local (\env -> env { refFlowModVars = vs }) k

-- | Ask if a variable is defined by a ref that is then modified before some use
-- of the variable.
askRefFlowModVar :: Var -> Cg l Bool
askRefFlowModVar v = asks $ \env -> Set.member v (refFlowModVars env)

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

collectDefinitions_ :: Cg l () -> Cg l ([C.Definition])
collectDefinitions_ m = fst <$> collectDefinitions m

collectThreadDecls :: Cg l a -> Cg l ([C.InitGroup], a)
collectThreadDecls m = do
    (c, x) <- collect m
    tell c { codeThreadDecls = mempty }
    return (toList (codeThreadDecls c), x)

collectThreadDecls_ :: Cg l () -> Cg l ([C.InitGroup])
collectThreadDecls_ m = fst <$> collectThreadDecls m

collectDecls :: Cg l a -> Cg l ([C.InitGroup], a)
collectDecls m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty }
    return (toList (codeDecls c), x)

collectDecls_ :: Cg l () -> Cg l ([C.InitGroup])
collectDecls_ m = fst <$> collectDecls m

collectStms :: Cg l a -> Cg l ([C.Stm], a)
collectStms m = do
    (c, x) <- collect m
    tell c { codeStms = mempty }
    return (toList (codeStms c), x)

collectStms_ :: Cg l () -> Cg l ([C.Stm])
collectStms_ m = fst <$> collectStms m

inNewThreadBlock :: Cg l a -> Cg l ([C.BlockItem], a)
inNewThreadBlock m = do
    (c, x) <- collect m
    tell c { codeThreadDecls       = mempty
           , codeThreadInitStms    = mempty
           , codeThreadCleanupStms = mempty
           , codeDecls             = mempty
           , codeStms              = mempty
           }
    return ((map C.BlockDecl . toList . codeThreadDecls) c ++
            (map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeThreadInitStms) c ++
            (map C.BlockStm .  toList . codeStms) c ++
            (map C.BlockStm .  toList . codeThreadCleanupStms) c
           ,x)

inNewThreadBlock_ :: Cg l a -> Cg l [C.BlockItem]
inNewThreadBlock_ m =
    fst <$> inNewThreadBlock m

inNewBlock :: Cg l a -> Cg l ([C.BlockItem], a)
inNewBlock m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty, codeStms  = mempty }
    return ((map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeStms) c, x)

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
appendDecl cdecl = tell mempty { codeDecls = Seq.singleton cdecl }

appendDecls :: [C.InitGroup] -> Cg l ()
appendDecls cdecls = tell mempty { codeDecls = Seq.fromList cdecls }

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
    isBlockStm (C.BlockStm {}) = True
    isBlockStm _               = False

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

getStats :: Cg l CgStats
getStats = gets stats

modifyStats :: (CgStats -> CgStats) -> Cg l ()
modifyStats f = modify $ \s -> s { stats = f (stats s) }

incMemCopies :: Cg l ()
incMemCopies =
    modifyStats $ \s -> s { memCopies = memCopies s + 1 }

incBitArrayCopies :: Cg l ()
incBitArrayCopies =
    modifyStats $ \s -> s { bitArrayCopies =bitArrayCopies s + 1 }

instance IfThenElse (CExp l) (Cg l ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]
