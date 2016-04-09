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

    inNewMainThreadBlock,
    inNewMainThreadBlock_,
    inNewThreadBlock,
    inNewThreadBlock_,
    inNewBlock,
    inNewBlock_,

    appendTopDef,
    appendTopDefs,
    appendTopDecl,
    appendTopDecls,
    appendInitStm,
    appendCleanupStm,
    appendThreadDecl,
    appendThreadDecls,
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
import KZC.Flags
import KZC.Label
import KZC.Monad
import KZC.Monad.SEFKT
import KZC.Quote.C
import KZC.Staged
import KZC.Uniq
import KZC.Util.Env

-- | The 'Cg' monad.
type Cg a = SEFKT (ReaderT CgEnv (StateT CgState Tc)) a

data CgEnv = CgEnv
    { varCExps    :: Map Var CExp
    , ivarCExps   :: Map IVar CExp
    , tyvarTypes  :: Map TyVar Type
    , -- | Variables defined using refs that are then modified before some use
      -- of the variable.
      refFlowModVars :: Set Var
    }

instance Show CgEnv where
    show _ = "<Env>"

defaultCgEnv :: CgEnv
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

data CgState = CgState
    { labels :: Set Label
    , code   :: Code
    , stats  :: CgStats
    }

defaultCgState :: CgState
defaultCgState = CgState
    { labels = mempty
    , code   = mempty
    , stats  = mempty
    }

-- | Evaluate a 'Cg' action and return a list of 'C.Definition's.
evalCg :: Cg () -> KZC [C.Definition]
evalCg m = do
    s <- liftTc $ execStateT (runReaderT (runSEFKT m) defaultCgEnv) defaultCgState
    return $ (toList . codeDefs . code) s

extendVarCExps :: [(Var, CExp)] -> Cg a -> Cg a
extendVarCExps ves m =
    extendEnv varCExps (\env x -> env { varCExps = x }) ves m

lookupVarCExp :: Var -> Cg CExp
lookupVarCExp v =
    lookupEnv varCExps onerr v
  where
    onerr = faildoc $
            text "Compiled variable" <+> ppr v <+> text "not in scope"

extendIVarCExps :: [(IVar, CExp)] -> Cg a -> Cg a
extendIVarCExps ves m =
    extendEnv ivarCExps (\env x -> env { ivarCExps = x }) ves m

lookupIVarCExp :: IVar -> Cg CExp
lookupIVarCExp v =
    lookupEnv ivarCExps onerr v
  where
    onerr = faildoc $
            text "Compiled array size variable" <+> ppr v <+>
            text "not in scope"

extendTyVarTypes :: [(TyVar, Type)] -> Cg a -> Cg a
extendTyVarTypes tvtaus m =
    extendEnv tyvarTypes (\env x -> env { tyvarTypes = x }) tvtaus m

lookupTyVarType :: TyVar -> Cg Type
lookupTyVarType alpha =
    lookupEnv tyvarTypes onerr alpha
  where
    onerr = faildoc $
            text "Instantiated type variable" <+> ppr alpha <+>
            text "not in scope"

-- | Return a function that substitutes type variables for their current
-- instantiation.
askTyVarTypeSubst :: Cg (Map TyVar Type)
askTyVarTypeSubst = asks tyvarTypes

-- | Specify the set of variables defined using refs that are then modified
-- before some use of the variable they flow to.
localRefFlowModVars :: Set Var -> Cg a -> Cg a
localRefFlowModVars vs k =
    local (\env -> env { refFlowModVars = vs }) k

-- | Ask if a variable is defined by a ref that is then modified before some use
-- of the variable.
askRefFlowModVar :: Var -> Cg Bool
askRefFlowModVar v = asks $ \env -> Set.member v (refFlowModVars env)

tell :: ToCode a => a -> Cg ()
tell c = modify $ \s -> s { code = code s <> toCode c }

class ToCode a where
    toCode :: a -> Code

instance ToCode Code where
    toCode code = code

instance ToCode C.Definition where
    toCode cdef = mempty { codeDefs = Seq.singleton cdef }

instance ToCode [C.Definition] where
    toCode cdefs = mempty { codeDefs = Seq.fromList cdefs }

instance ToCode C.InitGroup where
    toCode cdecl = mempty { codeDecls = Seq.singleton cdecl }

instance ToCode [C.InitGroup] where
    toCode cdecls = mempty { codeDecls = Seq.fromList cdecls }

instance ToCode C.Stm where
    toCode cstm = mempty { codeStms = Seq.singleton cstm }

instance ToCode [C.Stm] where
    toCode cstms = mempty { codeStms = Seq.fromList cstms }

collect :: Cg a -> Cg (Code, a)
collect m = do
    old_code <- gets code
    modify $ \s -> s { code = mempty }
    x <- m
    c <- gets code
    modify $ \s -> s { code = old_code }
    return (c, x)

collectDefinitions :: Cg a -> Cg ([C.Definition], a)
collectDefinitions m = do
    (c, x) <- collect m
    tell c { codeDefs = mempty }
    return (toList (codeDefs c), x)

collectDefinitions_ :: Cg () -> Cg ([C.Definition])
collectDefinitions_ m = fst <$> collectDefinitions m

collectThreadDecls :: Cg a -> Cg ([C.InitGroup], a)
collectThreadDecls m = do
    (c, x) <- collect m
    tell c { codeThreadDecls = mempty }
    return (toList (codeThreadDecls c), x)

collectThreadDecls_ :: Cg () -> Cg ([C.InitGroup])
collectThreadDecls_ m = fst <$> collectThreadDecls m

collectDecls :: Cg a -> Cg ([C.InitGroup], a)
collectDecls m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty }
    return (toList (codeDecls c), x)

collectDecls_ :: Cg () -> Cg ([C.InitGroup])
collectDecls_ m = fst <$> collectDecls m

collectStms :: Cg a -> Cg ([C.Stm], a)
collectStms m = do
    (c, x) <- collect m
    tell c { codeStms = mempty }
    return (toList (codeStms c), x)

collectStms_ :: Cg () -> Cg ([C.Stm])
collectStms_ m = fst <$> collectStms m

inNewMainThreadBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewMainThreadBlock m = do
    (c, x) <- collect m
    tell c { codeInitStms    = mempty
           , codeCleanupStms = mempty
           , codeThreadDecls = mempty
           , codeDecls       = mempty
           , codeStms        = mempty
           }
    return ((map C.BlockDecl . toList . codeThreadDecls) c ++
            (map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeInitStms) c ++
            (map C.BlockStm .  toList . codeStms) c ++
            (map C.BlockStm .  toList . codeCleanupStms) c
           ,x)

inNewMainThreadBlock_ :: Cg a -> Cg [C.BlockItem]
inNewMainThreadBlock_ m =
    fst <$> inNewMainThreadBlock m

inNewThreadBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewThreadBlock m = do
    (c, x) <- collect m
    tell c { codeThreadDecls = mempty, codeDecls = mempty, codeStms  = mempty }
    return ((map C.BlockDecl . toList . codeThreadDecls) c ++
            (map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeStms) c, x)

inNewThreadBlock_ :: Cg a -> Cg [C.BlockItem]
inNewThreadBlock_ m =
    fst <$> inNewThreadBlock m

inNewBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewBlock m = do
    (c, x) <- collect m
    tell c { codeDecls = mempty, codeStms  = mempty }
    return ((map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeStms) c, x)

inNewBlock_ :: Cg a -> Cg [C.BlockItem]
inNewBlock_ m =
    fst <$> inNewBlock m

appendTopDef :: C.Definition -> Cg ()
appendTopDef cdef =
  tell mempty { codeDefs = Seq.singleton cdef }

appendTopDefs :: [C.Definition] -> Cg ()
appendTopDefs cdefs =
  tell mempty { codeDefs = Seq.fromList cdefs }

appendTopDecl :: C.InitGroup -> Cg ()
appendTopDecl cdecl =
  tell mempty { codeDefs = Seq.singleton (C.DecDef cdecl noLoc) }

appendTopDecls :: [C.InitGroup] -> Cg ()
appendTopDecls cdecls =
  tell mempty { codeDefs = Seq.fromList [C.DecDef decl noLoc | decl <- cdecls] }

appendInitStm :: C.Stm -> Cg ()
appendInitStm cstm =
  tell mempty { codeInitStms = Seq.singleton cstm }

appendCleanupStm :: C.Stm -> Cg ()
appendCleanupStm cstm =
  tell mempty { codeCleanupStms = Seq.singleton cstm }

appendThreadDecl :: C.InitGroup -> Cg ()
appendThreadDecl cdecl = tell mempty { codeThreadDecls = Seq.singleton cdecl }

appendThreadDecls :: [C.InitGroup] -> Cg ()
appendThreadDecls cdecls = tell mempty { codeThreadDecls = Seq.fromList cdecls }

appendDecl :: C.InitGroup -> Cg ()
appendDecl cdecl = tell cdecl

appendDecls :: [C.InitGroup] -> Cg ()
appendDecls cdecls = tell cdecls

appendStm :: C.Stm -> Cg ()
appendStm cstm = tell cstm

appendStms :: [C.Stm] -> Cg ()
appendStms cstms = tell cstms

appendBlock :: [C.BlockItem] -> Cg ()
appendBlock citems
    | all isBlockStm citems = appendStms [stm | C.BlockStm stm <- citems]
    | otherwise             = appendStm [cstm|{ $items:citems }|]
  where
    isBlockStm :: C.BlockItem -> Bool
    isBlockStm (C.BlockStm {}) = True
    isBlockStm _               = False

gensym :: String -> Cg C.Id
gensym s = do
    noGensym <- asksFlags $ testDynFlag NoGensym
    if noGensym
      then return $ C.Id s noLoc
      else do Uniq u <- newUnique
              return $ C.Id (s ++ "__" ++ show u) noLoc

collectLabels :: Cg a -> Cg (Set Label, a)
collectLabels m = do
    old_labels <- gets labels
    modify $ \s -> s { labels = mempty }
    x    <- m
    lbls <- gets labels
    modify $ \s -> s { labels = old_labels }
    return (lbls, x)

useLabel :: Label -> Cg ()
useLabel lbl =
    modify $ \s -> s { labels = Set.insert lbl (labels s) }

useLabels :: Set Label -> Cg ()
useLabels lbls =
    modify $ \s -> s { labels = labels s `Set.union` lbls }

isLabelUsed :: Label -> Cg Bool
isLabelUsed lbl =
    gets (Set.member lbl . labels)

getStats :: Cg CgStats
getStats = gets stats

modifyStats :: (CgStats -> CgStats) -> Cg ()
modifyStats f = modify $ \s -> s { stats = f (stats s) }

incMemCopies :: Cg ()
incMemCopies =
    modifyStats $ \s -> s { memCopies = memCopies s + 1 }

incBitArrayCopies :: Cg ()
incBitArrayCopies =
    modifyStats $ \s -> s { bitArrayCopies =bitArrayCopies s + 1 }

instance IfThenElse CExp (Cg ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]
