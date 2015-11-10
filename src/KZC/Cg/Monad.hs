{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    Cg,
    evalCg,

    extend,
    lookupBy,

    extendVarCExps,
    lookupVarCExp,

    extendIVarCExps,
    lookupIVarCExp,

    extendTyVarTypes,
    lookupTyVarType,
    askTyVarTypeSubst,

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

    getLabels,

    appendTopDef,
    appendTopDefs,
    appendTopDecl,
    appendTopDecls,
    appendThreadDecl,
    appendThreadDecls,
    appendDecl,
    appendDecls,
    appendStm,
    appendStms,

    gensym,

    useLabel,
    useLabels,
    isLabelUsed,

    cgBitArrayWrite
  ) where

import Prelude hiding (elem)

import Control.Applicative ((<$>))
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)
import Data.List (foldl')
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Auto.Syntax
import KZC.Cg.CExp
import KZC.Cg.Code
import KZC.Label
import KZC.Lint.Monad
import KZC.Monad
import KZC.Monad.SEFKT
import KZC.Platform
import KZC.Quote.C
import KZC.Staged
import KZC.Uniq

-- | The 'Cg' monad.
type Cg a = SEFKT (ReaderT CgEnv (StateT CgState Tc)) a

data CgEnv = CgEnv
    { varCExps   :: Map Var CExp
    , ivarCExps  :: Map IVar CExp
    , tyvarTypes :: Map TyVar Type
    }

defaultCgEnv :: CgEnv
defaultCgEnv = CgEnv
    { varCExps   = mempty
    , ivarCExps  = mempty
    , tyvarTypes = mempty
    }

data CgState = CgState
    { labels :: Set Label
    , code   :: Code
    }

defaultCgState :: CgState
defaultCgState = CgState
    { labels = mempty
    , code   = mempty
    }

-- | Evaluate a 'Cg' action and return a list of 'C.Definition's.
evalCg :: Cg () -> KZC [C.Definition]
evalCg m = do
    s <- liftTc $ execStateT (runReaderT (runSEFKT m) defaultCgEnv) defaultCgState
    return $ (toList . codeDefs . code) s

extend :: forall k v a . Ord k
       => (CgEnv -> Map k v)
       -> (CgEnv -> Map k v -> CgEnv)
       -> [(k, v)]
       -> Cg a
       -> Cg a
extend _ _ [] m = m

extend proj upd kvs m = do
    local (\env -> upd env (foldl' insert (proj env) kvs)) m
  where
    insert :: Map k v -> (k, v) -> Map k v
    insert mp (k, v) = Map.insert k v mp

lookupBy :: Ord k
         => (CgEnv -> Map k v)
         -> Cg v
         -> k
         -> Cg v
lookupBy proj onerr k = do
    maybe_v <- asks (Map.lookup k . proj)
    case maybe_v of
      Nothing  -> onerr
      Just v   -> return v

extendVarCExps :: [(Var, CExp)] -> Cg a -> Cg a
extendVarCExps ves m =
    extend varCExps (\env x -> env { varCExps = x }) ves m

lookupVarCExp :: Var -> Cg CExp
lookupVarCExp v =
    lookupBy varCExps onerr v
  where
    onerr = faildoc $ text "Compiled variable" <+> ppr v <+> text "not in scope"

extendIVarCExps :: [(IVar, CExp)] -> Cg a -> Cg a
extendIVarCExps ves m =
    extend ivarCExps (\env x -> env { ivarCExps = x }) ves m

lookupIVarCExp :: IVar -> Cg CExp
lookupIVarCExp v =
    lookupBy ivarCExps onerr v
  where
    onerr = faildoc $ text "Compiled array size variable" <+> ppr v <+> text "not in scope"

extendTyVarTypes :: [(TyVar, Type)] -> Cg a -> Cg a
extendTyVarTypes tvtaus m =
    extend tyvarTypes (\env x -> env { tyvarTypes = x }) tvtaus m

lookupTyVarType :: TyVar -> Cg Type
lookupTyVarType alpha =
    lookupBy tyvarTypes onerr alpha
  where
    onerr = faildoc $ text "Instantiated type variable" <+> ppr alpha <+> text "not in scope"

-- | Return a function that substitutes type variables for their current
-- instantiation.
askTyVarTypeSubst :: Cg (Map TyVar Type)
askTyVarTypeSubst = asks tyvarTypes

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

collect :: Cg a -> Cg (a, Code)
collect m = do
    old_code <- gets code
    modify $ \s -> s { code = mempty }
    x <- m
    c <- gets code
    modify $ \s -> s { code = old_code }
    return (x, c)

collectDefinitions :: Cg a -> Cg ([C.Definition], a)
collectDefinitions m = do
    (x, c) <- collect m
    tell c { codeDefs = mempty }
    return (toList (codeDefs c), x)

collectDefinitions_ :: Cg () -> Cg ([C.Definition])
collectDefinitions_ m = do
    (defs, _) <- collectDefinitions m
    return defs

collectThreadDecls :: Cg a -> Cg ([C.InitGroup], a)
collectThreadDecls m = do
    (x, c) <- collect m
    tell c { codeThreadDecls = mempty }
    return (toList (codeThreadDecls c), x)

collectThreadDecls_ :: Cg () -> Cg ([C.InitGroup])
collectThreadDecls_ m = do
    (decls, _) <- collectThreadDecls m
    return decls

collectDecls :: Cg a -> Cg ([C.InitGroup], a)
collectDecls m = do
    (x, c) <- collect m
    tell c { codeDecls = mempty }
    return (toList (codeDecls c), x)

collectDecls_ :: Cg () -> Cg ([C.InitGroup])
collectDecls_ m = do
    (decls, _) <- collectDecls m
    return decls

collectStms :: Cg a -> Cg ([C.Stm], a)
collectStms m = do
    (x, c) <- collect m
    tell c { codeStms = mempty }
    return (toList (codeStms c), x)

collectStms_ :: Cg () -> Cg ([C.Stm])
collectStms_ m = do
    (stms, _) <- collectStms m
    return stms

inNewThreadBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewThreadBlock m = do
    (x, c) <- collect m
    tell c { codeThreadDecls = mempty, codeDecls = mempty, codeStms  = mempty }
    return ((map C.BlockDecl . toList . codeThreadDecls) c ++
            (map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeStms) c, x)

inNewThreadBlock_ :: Cg a -> Cg [C.BlockItem]
inNewThreadBlock_ m =
    fst <$> inNewThreadBlock m

inNewBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewBlock m = do
    (x, c) <- collect m
    tell c { codeDecls = mempty, codeStms  = mempty }
    return ((map C.BlockDecl . toList . codeDecls) c ++
            (map C.BlockStm .  toList . codeStms) c, x)

inNewBlock_ :: Cg a -> Cg [C.BlockItem]
inNewBlock_ m =
    fst <$> inNewBlock m

getLabels :: Cg [Label]
getLabels = gets (Set.toList . labels)

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

gensym :: String -> Cg C.Id
gensym s = do
    Uniq u <- newUnique
    return $ C.Id (s ++ "__" ++ show u) noLoc

useLabel :: Label -> Cg ()
useLabel lbl =
    modify $ \s -> s { labels = Set.insert lbl (labels s) }

useLabels :: Set Label -> Cg ()
useLabels lbls =
    modify $ \s -> s { labels = labels s `Set.union` lbls }

isLabelUsed :: Label -> Cg Bool
isLabelUsed lbl =
    gets (Set.member lbl . labels)

instance IfThenElse CExp (Cg ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]

-- XXX: Should use more efficient bit twiddling code here. See:
--
--   http://realtimecollisiondetection.net/blog/?p=78
--   https://graphics.stanford.edu/~seander/bithacks.html
--   https://stackoverflow.com/questions/18561655/bit-set-clear-in-c
--
-- | Read an element of a bit array.
cgBitArrayWrite :: CExp -> CExp -> CExp -> Cg ()
cgBitArrayWrite carr ci cx =
    if cx
    then appendStm [cstm|$carr[$cbitIdx] |= $cbitMask;|]
    else appendStm [cstm|$carr[$cbitIdx] &= ~$cbitMask;|]
  where
    cbitIdx, cbitOff :: CExp
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp
    cbitMask = 1 `shiftL'` cbitOff
