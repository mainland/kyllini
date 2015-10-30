{-# LANGUAGE DeriveFunctor #-}
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

    CExp(..),

    Label,
    Comp(..),
    CComp,

    codeC,
    takeC,
    takesC,
    emitC,
    ifC,
    parC,
    bindC,
    endC,
    doneC,
    labelC,
    gotoC,

    ccompLabel,

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
    collectDecls,
    collectDecls_,
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

    cgBitArrayRead,
    cgBitArrayWrite
  ) where

import Prelude hiding (elem)

import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits
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

import KZC.Cg.Code
import KZC.Core.Syntax
import KZC.Lint.Monad
import KZC.Monad
import KZC.Platform
import KZC.Quote.C
import KZC.Staged
import KZC.Uniq
import KZC.Vars

-- | The type of "compiled" expressions.
data CExp = CVoid
          | CBool Bool
          | CBit Bool
          | CInt Integer     -- ^ Integer constant
          | CFloat Rational  -- ^ Float constant
          | CExp C.Exp       -- ^ C expression
          | CPtr CExp        -- ^ A pointer.
          | CIdx Type CExp CExp
            -- ^ An array element. The data constructors arguments are the type
            -- of the array's elements, the array, and the index.
          | CSlice Type CExp CExp Int
            -- ^ An array slice. The data constructors arguments are the type of
            -- the array's elements, the array, the offset, the length of the
            -- slice.
          | CComp CComp      -- ^ A computation.
          | CDelay [IVar] [(Var, Type)] (Cg CExp)
            -- ^ A delayed CExp. This represents a computation that may take
            -- and/or emit.

instance Located CExp where
    locOf CVoid               = NoLoc
    locOf (CBool {})          = NoLoc
    locOf (CBit {})           = NoLoc
    locOf (CInt {})           = NoLoc
    locOf (CFloat {})         = NoLoc
    locOf (CExp ce)           = locOf ce
    locOf (CPtr ce)           = locOf ce
    locOf (CIdx _ _ cidx)     = locOf cidx
    locOf (CSlice _ _ cidx _) = locOf cidx
    locOf (CComp {})          = NoLoc
    locOf (CDelay {})         = NoLoc

instance IfThenElse CExp CExp where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c             t e = CExp [cexp|$c ? $t : $e|]

instance IfThenElse CExp (Cg ()) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c t e = do
       cthen_items <- inNewBlock_ t
       celse_items <- inNewBlock_ e
       if null celse_items
         then appendStm [cstm|if ($c) { $items:cthen_items }|]
         else appendStm [cstm|if ($c) { $items:cthen_items } else { $items:celse_items }|]

instance Eq CExp where
    CVoid          == CVoid          = True
    CBool x        == CBool y        = x == y
    CBit x         == CBit y         = x == y
    CInt x         == CInt y         = x == y
    CFloat x       == CFloat y       = x == y
    CPtr x         == CPtr y         = x == y
    CIdx r s t     == CIdx x y z     = (r,s,t) == (x,y,z)
    CSlice q r s t == CSlice w x y z = (q,r,s,t) == (w,x,y,z)
    _              == _              = error "Eq CExp: incomparable"

instance Ord CExp where
    compare CVoid            CVoid            = EQ
    compare (CBool x)        (CBool y)        = compare x y
    compare (CBit x)         (CBit y)         = compare x y
    compare (CInt x)         (CInt y)         = compare x y
    compare (CFloat x)       (CFloat y)       = compare x y
    compare (CPtr x)         (CPtr y)         = compare x y
    compare (CIdx r s t)     (CIdx x y z)     = compare (r,s,t) (x,y,z)
    compare (CSlice q r s t) (CSlice w x y z) = compare (q,r,s,t) (w,x,y,z)
    compare _                _                = error "Ord CExp: incomparable"

instance Enum CExp where
    toEnum n = CInt (fromIntegral n)

    fromEnum (CInt n) = fromIntegral n
    fromEnum _        = error "Enum Exp: fromEnum not implemented"

instance IsEq CExp where
    CBool x  .==. CBool y =  CBool (x == y)
    CBit x   .==. CBit y   = CBool (x == y)
    CInt x   .==. CInt y   = CBool (x == y)
    CFloat x .==. CFloat y = CBool (x == y)
    ce1      .==. ce2      = CExp [cexp|$ce1 == $ce2|]

    CBool x  ./=. CBool y =  CBool (x /= y)
    CBit x   ./=. CBit y   = CBool (x /= y)
    CInt x   ./=. CInt y   = CBool (x /= y)
    CFloat x ./=. CFloat y = CBool (x /= y)
    ce1      ./=. ce2      = CExp [cexp|$ce1 != $ce2|]

instance IsOrd CExp where
    CInt x   .<. CInt y   = CBool (x < y)
    CFloat x .<. CFloat y = CBool (x < y)
    ce1      .<. ce2      = CExp [cexp|$ce1 < $ce2|]

    CInt x   .<=. CInt y   = CBool (x <= y)
    CFloat x .<=. CFloat y = CBool (x <= y)
    ce1      .<=. ce2      = CExp [cexp|$ce1 <= $ce2|]

    CInt x   .>=. CInt y   = CBool (x >= y)
    CFloat x .>=. CFloat y = CBool (x >= y)
    ce1      .>=. ce2      = CExp [cexp|$ce1 >= $ce2|]

    CInt x   .>. CInt y   = CBool (x > y)
    CFloat x .>. CFloat y = CBool (x > y)
    ce1      .>. ce2      = CExp [cexp|$ce1 > $ce2|]

instance Num CExp where
    CInt 0   + y        = y
    x        + CInt 0   = x
    CInt x   + CInt y   = CInt (x + y)

    CFloat 0 + y        = y
    x        + CFloat 0 = x
    CFloat x + CFloat y = CFloat (x + y)

    x        + y        = CExp [cexp|$x + $y|]

    x        - CInt 0   = x
    CInt 0   - x        = -x
    CInt x   - CInt y   = CInt (x - y)

    x        - CFloat 0 = x
    CFloat 0 - x        = -x
    CFloat x - CFloat y = CFloat (x - y)

    x        - y        = CExp [cexp|$x - $y|]

    CInt 1   * y        = y
    x        * CInt 1   = x
    CInt x   * CInt y   = CInt (x * y)

    CFloat 1 * y        = y
    x        * CFloat 1 = x
    CFloat x * CFloat y = CFloat (x * y)

    x        * y        = CExp [cexp|$x * $y|]

    negate (CInt x)   = CInt (-x)
    negate (CFloat x) = CFloat (-x)
    negate x          = CExp [cexp|-$x|]

    abs (CInt x)   = CInt (abs x)
    abs (CFloat x) = CFloat (abs x)
    abs _          = error "Num CExp: abs not implemented"

    signum (CInt x)   = CInt (signum x)
    signum (CFloat x) = CFloat (signum x)
    signum ce         = error $ "Num CExp: signum not implemented: " ++ pretty 80 (ppr ce)

    fromInteger i = CInt i

instance Real CExp where
    toRational (CInt n)   = toRational n
    toRational (CFloat n) = n
    toRational _          = error "Real CExp: toRational not implemented"

instance Integral CExp where
    CInt x `quot` CInt y = CInt (x `quot` y)
    x      `quot` y      = CExp [cexp|$x / $y|]

    CInt x `quotRem` CInt y = (CInt q, CInt r)
      where
        (q, r) = x `quotRem` y

    ce1 `quotRem` ce2@(CInt i) | isPowerOf2 i =
        (CExp [cexp|$ce1 / $ce2|], CExp [cexp|$ce1 & $(ce2-1)|])
      where
        isPowerOf2 0 = False
        isPowerOf2 1 = False
        isPowerOf2 2 = True
        isPowerOf2 n | r == 0    = isPowerOf2 q
                     | otherwise = False
          where
            (q,r) = n `quotRem` 2

    ce1 `quotRem` ce2 =
        (CExp [cexp|$ce1 / $ce2|], CExp [cexp|$ce1 % $ce2|])

    toInteger (CInt i) = i
    toInteger _        = error "Integral CExp: fromInteger not implemented"

instance Fractional CExp where
    CFloat x / CFloat y = CFloat (x / y)
    x        / y        = CExp [cexp|$x / $y|]

    recip (CFloat x) = CFloat (recip x)
    recip x          = CExp [cexp|1/$x|]

    fromRational r = CFloat r

instance Bits CExp where
    CInt x .&. CInt y = CInt (x .&. y)
    ce1    .&. ce2    = CExp [cexp|$ce1 & $ce2|]

    CInt 0 .|. y      = y
    x      .|. CInt 0 = x
    CInt x .|. CInt y = CInt (x .|. y)
    ce1    .|. ce2    = CExp [cexp|$ce1 | $ce2|]

    CInt x `xor` CInt y = CInt (x .|. y)
    ce1    `xor` ce2    = CExp [cexp|$ce1 ^ $ce2|]

    complement (CInt x) = CInt (complement x)
    complement ce       = CExp [cexp|~$ce|]

    CInt x `shiftL` i = CInt (x `shiftL` i)
    x      `shiftL` 0 = x
    ce     `shiftL` i = CExp [cexp|$ce << $int:i|]

    CInt x `shiftR` i = CInt (x `shiftR` i)
    x      `shiftR` 0 = x
    ce     `shiftR` i = CExp [cexp|$ce >> $int:i|]

    -- See http://blog.regehr.org/archives/1063
    CInt x `rotateL` i = CInt (x `rotateL` i)
    x      `rotateL` 0 = x
    ce     `rotateL` i = CExp [cexp|($ce << $int:i) | ($ce >> ((-$int:i) & $mask))|]
      where
        mask :: C.Exp
        mask = [cexp|(CHAR_BIT*sizeof($ce)-1)|]

    CInt x `rotateR` i = CInt (x `rotateR` i)
    x      `rotateR` 0 = x
    ce     `rotateR` i = CExp [cexp|($ce >> $int:i) | ($ce << ((-$int:i) & $mask))|]
      where
        mask :: C.Exp
        mask = [cexp|(CHAR_BIT*sizeof($ce)-1)|]

    bit i = CInt $ bit i

    bitSize _ = error "Bits CExp: bitSize not implemented"
    bitSizeMaybe _ = error "Bits CExp: bitSizeMaybe not implemented"
    isSigned _ = error "Bits CExp: isSigned not implemented"
    testBit _ _ = error "Bits CExp: testBit not implemented"
    popCount _ = error "Bits CExp: popCount not implemented"

instance IsBool CExp where
    CBool True  .&&. ce  = ce
    CBool False .&&. _   = CBool False
    ce1         .&&. ce2 = CExp [cexp|$ce1 && $ce2|]

    CBool True  .||. _   = CBool True
    CBool False .||. ce  = ce
    ce1         .||. ce2 = CExp [cexp|$ce1 || $ce2|]

instance IsBits CExp where
    bit' (CInt i) = CInt $ bit (fromIntegral i)
    bit' ci       = CExp [cexp|1 << $ci|]

    CInt x `shiftL'` CInt i = CInt (x `shiftL` fromIntegral i)
    x      `shiftL'` CInt 0 = x
    ce     `shiftL'` i      = CExp [cexp|$ce << $i|]

    CInt x `shiftR'` CInt i = CInt (x `shiftR` fromIntegral i)
    x      `shiftR'` CInt 0 = x
    ce     `shiftR'` i      = CExp [cexp|$ce >> $i|]

instance ToExp CExp where
    toExp CVoid                      = error "toExp: void compiled expression"
    toExp (CBool i)                  = \_ -> [cexp|$int:(if i then 1::Integer else 0)|]
    toExp (CBit i)                   = \_ -> [cexp|$int:(if i then 1::Integer else 0)|]
    toExp (CInt i)                   = \_ -> [cexp|$int:i|]
    toExp (CFloat r)                 = \_ -> [cexp|$double:r|]
    toExp (CExp e)                   = \_ -> e
    toExp (CPtr e)                   = toExp e
    toExp (CIdx tau carr cidx)       = \_ -> lowerCIdx tau carr cidx
    toExp (CSlice tau carr cidx len) = \_ -> lowerCSlice tau carr cidx len
    toExp (CComp (Pure ce))          = toExp ce
    toExp (CComp {})                 = error "toExp: cannot convert CComp to a C expression"
    toExp (CDelay {})                = error "toExp: cannot convert CDelay to a C expression"

instance Pretty CExp where
    ppr CVoid                    = text "<void>"
    ppr (CBool True)             = text "true"
    ppr (CBool False)            = text "false"
    ppr (CBit True)              = text "'1"
    ppr (CBit False)             = text "'0"
    ppr (CInt i)                 = ppr i
    ppr (CFloat f)               = ppr f
    ppr (CExp e)                 = ppr e
    ppr (CPtr e)                 = ppr [cexp|*$e|]
    ppr (CIdx _ carr cidx)       = ppr carr <> brackets (ppr cidx)
    ppr (CSlice _ carr cidx len) = ppr carr <> brackets (ppr cidx <> colon <> ppr len)
    ppr (CComp {})               = text "<computation>"
    ppr (CDelay {})              = text "<delayed compiled expression>"

lowerCIdx :: Type -> CExp -> CExp -> C.Exp
lowerCIdx (BitT _) carr cidx = cgBitArrayRead carr cidx
lowerCIdx _        carr cidx = [cexp|$carr[$cidx]|]

lowerCSlice :: Type -> CExp -> CExp -> Int -> C.Exp
lowerCSlice (BitT _) carr (CInt i) _ | bitOff == 0 =
    [cexp|&$carr[$int:bitIdx]|]
  where
    bitIdx, bitOff :: Integer
    (bitIdx, bitOff) = i `quotRem` bIT_ARRAY_ELEM_BITS

lowerCSlice tau@(BitT _) carr ce len =
    errordoc $
    nest 4 $
    ppr (locOf ce) <> text ":" </>
    text "lowerCSlice: cannot take slice of bit array where index is not a divisor of the bit width:" </>
    ppr (CSlice tau carr ce len)

lowerCSlice _ carr cidx _ =
    [cexp|&$carr[$cidx]|]

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
              | EmitC l Type CExp a
              | IfC l CExp CExp a a (CExp -> a)
              | ParC Type Type CExp a a (CExp -> a)
              | BindC l Type CExp CExp a
              | EndC l
              | DoneC l CExp
              | LabelC l a
              | GotoC l
  deriving (Functor)

type CComp = Free (Comp Label) CExp

codeC :: Label -> Code -> CComp
codeC l code = liftF $ CodeC l code CVoid

takeC :: Label -> Type -> CComp
takeC l tau = liftF $ TakeC l tau id

takesC :: Label -> Int -> Type -> CComp
takesC l i tau = liftF $ TakesC l i tau id

-- emit and emits always need a continuation to return to, so we must insert a
-- label after them in case their continuation is a @Pure@ computation.
emitC :: Type -> CExp -> Cg CComp
emitC tau ce = do
    beforel <- genLabel "emitk"
    afterl  <- genLabel "emitk_after"
    return $ (liftF $ EmitC beforel tau ce CVoid) >>= \ce -> labelC afterl >> return ce

ifC :: Label -> CExp -> CExp -> CComp -> CComp -> CComp
ifC l cv ce thenc elsec =
    Free $ IfC l cv ce thenc elsec return

endC :: Label -> CComp
endC l = liftF $ EndC l

doneC :: Label -> CExp -> CComp
doneC l ce = liftF $ DoneC l ce

parC :: Type -> Type -> CExp -> CComp -> CComp -> CComp
parC tau tau_res ce_res c1 c2 = Free $ ParC tau tau_res ce_res c1 c2 return

bindC :: Label -> Type -> CExp -> CExp -> CComp
bindC l tau cv ce = liftF $ BindC l tau cv ce CVoid

labelC :: Label -> CComp
labelC l = liftF $ LabelC l CVoid

gotoC :: Label -> CComp
gotoC l = Free (GotoC l)

ccompLabel :: CComp -> Cg Label
ccompLabel (Pure {})   = fail "ccompLabel: saw Pure"
ccompLabel (Free comp) = compLabel comp
  where
    compLabel :: Comp Label CComp -> Cg Label
    compLabel (CodeC l _ (Pure {})) = useLabel l
    compLabel (CodeC l c k)
        | codeStms c == mempty       = ccompLabel k
        | otherwise                  = useLabel l
    compLabel (TakeC l _ _)          = useLabel l
    compLabel (TakesC l _ _ _)       = useLabel l
    compLabel (EmitC l _ _ _)        = useLabel l
    compLabel (IfC l _ _ _ _ _)      = useLabel l
    compLabel (ParC _ _ _ _ right _) = ccompLabel right
    compLabel (BindC l _ _ _ _)      = useLabel l
    compLabel (EndC l)               = useLabel l
    compLabel (DoneC l _)            = useLabel l
    compLabel (LabelC l (Pure {}))   = useLabel l
    compLabel (LabelC _ k)           = ccompLabel k
    compLabel (GotoC l)              = useLabel l

-- | The 'Cg' monad.
type Cg a = Tc CgEnv CgState a

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
    s <- liftTc defaultCgEnv defaultCgState (m >> get)
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
askTyVarTypeSubst :: Cg (Type -> Type)
askTyVarTypeSubst = do
    theta <- asks tyvarTypes
    return $ subst theta mempty

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

genLabel :: String -> Cg Label
genLabel s =
    gensym s

useLabel :: Label -> Cg Label
useLabel lbl = do
    modify $ \s -> s { labels = Set.insert lbl (labels s) }
    return lbl

isLabelUsed :: Label -> Cg Bool
isLabelUsed lbl =
    gets (Set.member lbl . labels)

-- | Read an element from a bit array.
cgBitArrayRead :: CExp -> CExp -> C.Exp
cgBitArrayRead carr ci =
    [cexp|($carr[$cbitIdx] & $cbitMask) ? 1 : 0|]
  where
    cbitIdx, cbitOff :: CExp
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp
    cbitMask = 1 `shiftL'` cbitOff

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
