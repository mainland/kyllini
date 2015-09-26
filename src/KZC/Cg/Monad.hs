{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Lint.Monad
-- Copyright   :  (c) 2014-2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.Monad (
    Cg,
    evalCg,

    Code(..),

    CExp(..),

    Label,
    Comp(..),
    CComp,

    codeC,
    takeC,
    takesC,
    emitC,
    emitsC,
    ifC,
    parC,
    bindC,
    doneC,
    gotoC,

    ccompLabel,

    extend,
    lookupBy,

    extendVarCExps,
    lookupVarCExp,

    extendIVarCExps,
    lookupIVarCExp,

    tell,
    collect,
    collectDefinitions,
    collectDefinitions_,
    collectStms,
    collectStms_,

    inNewBlock,
    inNewBlock_,

    getLabels,

    appendTopDef,
    appendTopDefs,
    appendTopDecl,
    appendTopDecls,
    appendDecl,
    appendDecls,
    appendStm,
    appendStms,

    gensym,

    genLabel,
    useLabel,
    isLabelUsed,

    traceNest,
    traceCg
  ) where

import Prelude hiding (elem)

import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (elem,
                      toList)
import Data.List (foldl')
import Data.Loc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Language.C.Quote.C
import qualified Language.C.Syntax as C
import System.IO (stderr)
import Text.PrettyPrint.Mainland

import KZC.Core.Syntax
import KZC.Error
import KZC.Flags
import KZC.Lint.Monad hiding (traceNest)
import KZC.Monad
import KZC.Uniq

-- | Contains generated code.
data Code = Code
    { -- | Top-level definitions
      defs  :: !(Seq C.Definition)
      -- | Local declarations
    , decls :: !(Seq C.InitGroup)
      -- | Local statements
    , stmts :: !(Seq C.Stm)
    }
  deriving (Eq, Ord, Show)

instance Pretty Code where
    ppr c = stack $
            (map ppr . toList . defs)  c ++
            (map ppr . toList . decls) c ++
            (map ppr . toList . stmts) c

instance Monoid Code where
    mempty = Code { defs     = mempty
                  , decls    = mempty
                  , stmts    = mempty
                  }

    a `mappend` b = Code { defs  = defs a <> defs b
                         , decls = decls a <> decls b
                         , stmts = stmts a <> stmts b
                         }

-- | The type of "compiled" expressions.
data CExp = CVoid
          | CInt Integer     -- ^ Integer constant
          | CFloat Rational  -- ^ Float constant
          | CExp C.Exp       -- ^ C expression
          | CArray CExp CExp -- ^ Array. The first argument is the array's
                             -- length, and the second is its contents.
          | CPtr CExp        -- ^ A pointer.
          | CComp CComp      -- ^ A computation.
          | CDelay (Cg CExp) -- ^ A delayed CExp

instance Num CExp where
    CInt x   + CInt y   = CInt (x + y)
    CFloat x + CFloat y = CFloat (x + y)
    x        + y        = CExp [cexp|$x + $y|]

    CInt x   - CInt y   = CInt (x - y)
    CFloat x - CFloat y = CFloat (x - y)
    x        - y        = CExp [cexp|$x - $y|]

    CInt x   * CInt y   = CInt (x * y)
    CFloat x * CFloat y = CFloat (x * y)
    x        * y        = CExp [cexp|$x * $y|]

    negate (CInt x)   = CInt (-x)
    negate (CFloat x) = CFloat (-x)
    negate x          = CExp [cexp|-$x|]

    abs _ = error "Num CExp: abs not implemented"

    signum _ = error "Num CExp: signum not implemented"

    fromInteger i = CInt i

instance Fractional CExp where
    CFloat x / CFloat y = CFloat (x / y)
    x        / y        = CExp [cexp|$x / $y|]

    recip (CFloat x) = CFloat (recip x)
    recip x          = CExp [cexp|1/$x|]

    fromRational r = CFloat r

instance ToExp CExp where
    toExp CVoid             = error "toExp: void compiled expression"
    toExp (CInt i)          = \_ -> [cexp|$int:i|]
    toExp (CFloat r)        = \_ -> [cexp|$double:r|]
    toExp (CExp e)          = \_ -> e
    toExp (CArray _ e)      = toExp e
    toExp (CPtr e)          = toExp e
    toExp (CComp (Pure ce)) = toExp ce
    toExp (CComp {})        = error "toExp: cannot convert CComp to a C expression"
    toExp (CDelay {})       = error "toExp: cannot convert CDelay to a C expression"

instance Pretty CExp where
    ppr CVoid        = text "<void>"
    ppr (CInt i)     = ppr i
    ppr (CFloat f)   = ppr f
    ppr (CExp e)     = ppr e
    ppr (CPtr e)     = ppr [cexp|*$e|]
    ppr (CArray _ e) = ppr (toExp e noLoc)
    ppr (CComp {})   = text "<computation>"
    ppr (CDelay {})  = text "<delayed compiled expression>"

-- | A code label
type Label = C.Id

-- | A free monad representation of computations. All computations are labeled,
-- but not all labels are 'Require'. Any computation that is used as a
-- continuation /must/ have a required label, which results in a label in the
-- generated code.

-- Why do we need 'BindC'? Because the bind's continuation needs a /known,
-- fixed/ place to look for its input. If the continuation had type @Cg CComp@
-- instead of @CComp@, things would be different, but that would bring its own
-- set of problems. See the @cgExp@ case for 'BindE'.
data Comp l a = CodeC l Code a
              | TakeC l Type (CExp -> a)
              | TakesC l Int Type (CExp -> a)
              | EmitC l CExp a
              | EmitsC l Iota CExp a
              | IfC l CExp CExp a a (CExp -> a)
              | ParC Type a a
              | BindC l Type CExp CExp a
              | DoneC l
              | GotoC l
  deriving (Functor)

type CComp = Free (Comp Label) CExp

codeC :: Label -> Code -> CComp
codeC l code = liftF $ CodeC l code CVoid

takeC :: Label -> Type -> CComp
takeC l tau = liftF $ TakeC l tau id

takesC :: Label -> Int -> Type -> CComp
takesC l i tau = liftF $ TakesC l i tau id

emitC :: Label -> CExp -> CComp
emitC l ce = liftF $ EmitC l ce CVoid

emitsC :: Label -> Iota -> CExp -> CComp
emitsC l iota ce = liftF $ EmitsC l iota ce CVoid

ifC :: Label -> CExp -> CExp -> CComp -> CComp -> CComp
ifC l cv ce thenc elsec =
    Free $ IfC l cv ce thenc elsec return

doneC :: Label -> CComp
doneC l = liftF $ DoneC l

parC :: Type -> CComp -> CComp -> CComp
parC tau c1 c2 = Free $ ParC tau c1 c2

bindC :: Label -> Type -> CExp -> CExp -> CComp
bindC l tau cv ce = liftF $ BindC l tau cv ce CVoid

gotoC :: Label -> CComp
gotoC l = Free (GotoC l)

ccompLabel :: CComp -> Cg Label
ccompLabel (Pure {})   = fail "ccompLabel: saw Pure"
ccompLabel (Free comp) = compLabel comp
  where
    compLabel :: Comp Label CComp -> Cg Label
    compLabel (CodeC l c k)
        | stmts c == mempty     = ccompLabel k
        | otherwise             = useLabel l
    compLabel (TakeC l _ _)     = useLabel l
    compLabel (TakesC l _ _ _)  = useLabel l
    compLabel (EmitC l _ _)     = useLabel l
    compLabel (EmitsC l _ _ _)  = useLabel l
    compLabel (IfC l _ _ _ _ _) = useLabel l
    compLabel (ParC _ _ right)  = ccompLabel right
    compLabel (BindC l _ _ _ _) = useLabel l
    compLabel (DoneC l)         = useLabel l
    compLabel (GotoC l)         = useLabel l

-- | The 'Cg' monad.
type Cg a = Tc CgEnv CgState a

data CgEnv = CgEnv
    { errctx    :: ![ErrorContext]
    , nestdepth :: {-# UNPACK #-} !Int
    , varCExps  :: Map Var CExp
    , ivarCExps :: Map IVar CExp
    }

defaultCgEnv :: CgEnv
defaultCgEnv = CgEnv
    { errctx    = []
    , nestdepth = 0
    , varCExps  = mempty
    , ivarCExps = mempty
    }

data CgState = CgState
    { labels :: Seq Label
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
    s <- liftTc defaultCgEnv defaultCgState (m >> get)
    return $ (toList . defs . code) s

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
    onerr = faildoc $ text "Compiled variable" <+> ppr v <+> text "not in scope"

tell :: ToCode a => a -> Cg ()
tell c = modify $ \s -> s { code = code s <> toCode c }

class ToCode a where
    toCode :: a -> Code

instance ToCode Code where
    toCode code = code

instance ToCode C.Definition where
    toCode cdef = mempty { defs = Seq.singleton cdef }

instance ToCode [C.Definition] where
    toCode cdefs = mempty { defs = Seq.fromList cdefs }

instance ToCode C.InitGroup where
    toCode cdecl = mempty { decls = Seq.singleton cdecl }

instance ToCode [C.InitGroup] where
    toCode cdecls = mempty { decls = Seq.fromList cdecls }

instance ToCode C.Stm where
    toCode cstm = mempty { stmts = Seq.singleton cstm }

instance ToCode [C.Stm] where
    toCode cstms = mempty { stmts = Seq.fromList cstms }

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
    tell c { defs = mempty }
    return (toList (defs c), x)

collectDefinitions_ :: Cg () -> Cg ([C.Definition])
collectDefinitions_ m = do
    (defs, _) <- collectDefinitions m
    return defs

collectStms :: Cg a -> Cg ([C.Stm], a)
collectStms m = do
    (x, c) <- collect m
    tell c { stmts = mempty }
    return (toList (stmts c), x)

collectStms_ :: Cg () -> Cg ([C.Stm])
collectStms_ m = do
    (stms, _) <- collectStms m
    return stms

inNewBlock :: Cg a -> Cg ([C.BlockItem], a)
inNewBlock m = do
    (x, c) <- collect m
    tell c { decls = mempty, stmts  = mempty }
    return ((map C.BlockDecl . toList . decls) c ++
            (map C.BlockStm .  toList . stmts) c, x)

inNewBlock_ :: Cg a -> Cg [C.BlockItem]
inNewBlock_ m =
    fst <$> inNewBlock m

getLabels :: Cg [Label]
getLabels = gets (toList . labels)

appendTopDef :: C.Definition -> Cg ()
appendTopDef cdef =
  tell mempty { defs = Seq.singleton cdef }

appendTopDefs :: [C.Definition] -> Cg ()
appendTopDefs cdefs =
  tell mempty { defs = Seq.fromList cdefs }

appendTopDecl :: C.InitGroup -> Cg ()
appendTopDecl cdecl =
  tell mempty { defs = Seq.singleton (C.DecDef cdecl noLoc) }

appendTopDecls :: [C.InitGroup] -> Cg ()
appendTopDecls cdecls =
  tell mempty { defs = Seq.fromList [C.DecDef decl noLoc | decl <- cdecls] }

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
    return $ C.Id (s ++ show u) noLoc

genLabel :: String -> Cg Label
genLabel s =
    gensym s

useLabel :: Label -> Cg Label
useLabel lbl = do
    modify $ \s -> s { labels = labels s |> lbl }
    return lbl

isLabelUsed :: Label -> Cg Bool
isLabelUsed lbl =
    gets (elem lbl . labels)

traceNest :: Int -> Cg a -> Cg a
traceNest d = local (\env -> env { nestdepth = nestdepth env + d })

traceCg :: Doc -> Cg ()
traceCg doc = do
    doTrace <- liftKZC $ asksFlags (testTraceFlag TraceCg)
    when doTrace $ do
        d <- asks nestdepth
        liftIO $ hPutDocLn stderr $ text "traceCg:" <+> indent d (align doc)
