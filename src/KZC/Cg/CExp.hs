{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  KZC.Cg.CExp
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.CExp (
    Kont(..),

    TakeK,
    TakesK,
    EmitK,
    EmitsK,
    CompC,
    FunCompC,

    CExp(..),

    calias,

    unCSlice,
    unBitCSliceBase,

    toInit
  ) where

import Prelude hiding (elem)

import Data.Bits
import Data.Loc
import Data.Monoid
import qualified Language.C.Quote as C
import Text.PrettyPrint.Mainland

import {-# SOURCE #-} KZC.Cg.Monad
import KZC.Core.Lint (refPath)
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Platform
import KZC.Pretty
import KZC.Quote.C
import KZC.Staged

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

-- | A 'Kont a' is a code generator continuation---it takes a 'CExp' and
-- executes an action in the 'Cg' monad. This is distinct from a continuation
-- 'Label', as passed to take/emit/emits, which represents /the continuation of
-- the code being generated/, not the code generator's continuation.
data Kont l a -- | A continuation that may only be called once because calling
              -- it more than once may generate duplicate code. The 'Type' of
              -- the 'CExp' expected as an argument is specified. An optional
              -- binder name can be provided, which will be used if this
              -- continuation needs to be converted into a multishot
              -- continuation.
              = OneshotK (Maybe BoundVar) Type (CExp l -> Cg l a)

              -- | A continuation that may be called multiple times, i.e., it does
              -- not generate duplicate code. Note that the result of the
              -- continuation must be the same every time it is invoked, e.g., it
              -- may return a 'CExp' consisting of the same identifier every time
              -- it is invoked. When called multiple times, only one of the
              -- returned results will be used; however, the monadic side effects
              -- of all invocations will be executed.
              | MultishotK (CExp l -> Cg l a)

              -- | Like 'MultishotK', but given the explicit destination in which
              -- to place the result. The result will have been placed in the
              -- destination before the continuation is called.
              | MultishotBindK Type (CExp l) (CExp l -> Cg l a)

-- | A computation compiler, which produces a compiled computation when given
-- the appropriate arguments.
type CompC l a =  TakeK l  -- Code generator for take
               -> TakesK l -- Code generator for takes
               -> EmitK l  -- Code generator for emit
               -> EmitsK l -- Code generator for emits
               -> l        -- Label of our continuation
               -> Kont l a -- Continuation accepting the compilation result
               -> Cg l a   -- Value returned by the computation.

instance Show (CompC l a) where
    show _ = "<comp>"

-- | A computation function compiler, which produces a compiled call to a
-- computation function when given the appropriate arguments.
type FunCompC l a =  [Iota]   -- Array length arguments
                  -> [Arg l]  -- Function arguments
                  -> TakeK l  -- Code generator for take
                  -> TakesK l -- Code generator for takes
                  -> EmitK l  -- Code generator for emit
                  -> EmitsK l -- Code generator for emits
                  -> l        -- Label of our continuation
                  -> Kont l a -- Continuation accepting the compilation result
                  -> Cg l a

instance Show (FunCompC l a) where
    show _ = "<funcomp>"

-- | The type of "compiled" expressions.
data CExp l = CVoid
            | CBool !Bool
            | CInt !Integer    -- ^ Integer constant
            | CFloat !Rational -- ^ Float constant
            | CExp C.Exp       -- ^ C expression
            | CInit C.Initializer
              -- ^ A list of C initializers for a constant
            | CPtr (CExp l)    -- ^ A pointer.
            | CIdx Type (CExp l) (CExp l)
              -- ^ An array element. The data constructor's arguments are the type
              -- of the array's elements, the array, and the index.
            | CSlice Type (CExp l) (CExp l) Int
              -- ^ An array slice. The data constructor's arguments are the type
              -- of the array's elements, the array, the offset, the length of the
              -- slice.
            | CStruct [(Field, CExp l)]
              -- ^ A struct
            | CBits (CExp l)
              -- ^ A bit array represented as an integer
            | CAlias Exp (CExp l)
              -- ^ The 'CAlias' data constructor indicates a 'CExp' that aliases
              -- an expression. See Note [Aliasing].
            | CComp (forall a . CompC l a)
              -- ^ A computation.
            | CFunComp (forall a. FunCompC l a)
              -- ^ A computation function.

deriving instance Show (CExp l)

instance Located (CExp l) where
    locOf CVoid               = NoLoc
    locOf CBool{}             = NoLoc
    locOf CInt{}              = NoLoc
    locOf CFloat{}            = NoLoc
    locOf (CExp ce)           = locOf ce
    locOf (CInit cinit)       = locOf cinit
    locOf (CPtr ce)           = locOf ce
    locOf (CIdx _ _ cidx)     = locOf cidx
    locOf (CSlice _ _ cidx _) = locOf cidx
    locOf (CStruct flds)      = locOf (map snd flds)
    locOf (CBits ce)          = locOf ce
    locOf (CAlias _ ce)       = locOf ce
    locOf CComp{}             = NoLoc
    locOf CFunComp{}          = NoLoc

instance Relocatable (CExp l) where
    reloc _ ce@CVoid                   = ce
    reloc _ ce@CBool{}                 = ce
    reloc _ ce@CInt{}                  = ce
    reloc _ ce@CFloat{}                = ce
    reloc l (CExp ce)                  = CExp $ reloc l ce
    reloc l (CInit cinit)              = CInit $ reloc l cinit
    reloc l (CPtr ce)                  = CPtr $ reloc l ce
    reloc l (CIdx tau carr cidx)       = CIdx tau (reloc l carr) (reloc l cidx)
    reloc l (CSlice tau carr cidx len) = CSlice tau (reloc l carr) (reloc l cidx) len
    reloc l (CStruct flds)             = CStruct [(f, reloc l ce) | (f, ce) <- flds]
    reloc l (CBits ce)                 = CBits (reloc l ce)
    reloc l (CAlias e ce)              = CAlias e (reloc l ce)
    reloc _ ce@CComp{}                 = ce
    reloc _ ce@CFunComp{}              = ce

instance IfThenElse (CExp l) (CExp l) where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c             t e = CExp [cexp|$c ? $t : $e|]

instance Eq (CExp l) where
    CVoid          == CVoid          = True
    CBool x        == CBool y        = x == y
    CInt x         == CInt y         = x == y
    CFloat x       == CFloat y       = x == y
    CPtr x         == CPtr y         = x == y
    CIdx r s t     == CIdx x y z     = (r,s,t) == (x,y,z)
    CSlice q r s t == CSlice w x y z = (q,r,s,t) == (w,x,y,z)
    CBits x        == CBits y        = x == y
    CAlias r s     == CAlias x y     = (r,s) == (x,y)
    ce1            == ce2            = errordoc $
                                       text "Eq CExp incomparable:" <+>
                                       (text . show) ce1 <+>
                                       (text . show) ce2

instance Ord (CExp l) where
    compare CVoid            CVoid            = EQ
    compare (CBool x)        (CBool y)        = compare x y
    compare (CInt x)         (CInt y)         = compare x y
    compare (CFloat x)       (CFloat y)       = compare x y
    compare (CPtr x)         (CPtr y)         = compare x y
    compare (CIdx r s t)     (CIdx x y z)     = compare (r,s,t) (x,y,z)
    compare (CSlice q r s t) (CSlice w x y z) = compare (q,r,s,t) (w,x,y,z)
    compare (CBits x)        (CBits y)        = compare x y
    compare (CAlias r s)     (CAlias x y)     = compare (r,s) (x,y)
    compare ce1              ce2              = errordoc $
                                                text "Ord CExp incomparable:" <+>
                                                (text . show) ce1 <+>
                                                (text . show) ce2

instance Enum (CExp l) where
    toEnum n = CInt (fromIntegral n)

    fromEnum (CInt n) = fromIntegral n
    fromEnum _        = error "Enum Exp: fromEnum not implemented"

instance IsEq (CExp l) where
    CBool x  .==. CBool y =  CBool (x == y)
    CInt x   .==. CInt y   = CBool (x == y)
    CFloat x .==. CFloat y = CBool (x == y)
    ce1      .==. ce2      = CExp [cexp|$ce1 == $ce2|]

    CBool x  ./=. CBool y =  CBool (x /= y)
    CInt x   ./=. CInt y   = CBool (x /= y)
    CFloat x ./=. CFloat y = CBool (x /= y)
    ce1      ./=. ce2      = CExp [cexp|$ce1 != $ce2|]

instance IsOrd (CExp l) where
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

instance Num (CExp l) where
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

    fromInteger = CInt

instance Real (CExp l) where
    toRational (CInt n)   = toRational n
    toRational (CFloat n) = n
    toRational _          = error "Real CExp: toRational not implemented"

instance Integral (CExp l) where
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

instance Fractional (CExp l) where
    CFloat x / CFloat y = CFloat (x / y)
    x        / y        = CExp [cexp|$x / $y|]

    recip (CFloat x) = CFloat (recip x)
    recip x          = CExp [cexp|1/$x|]

    fromRational = CFloat

instance Bits (CExp l) where
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

instance IsBool (CExp l) where
    CBool True  .&&. ce  = ce
    CBool False .&&. _   = CBool False
    ce1         .&&. ce2 = CExp [cexp|$ce1 && $ce2|]

    CBool True  .||. _   = CBool True
    CBool False .||. ce  = ce
    ce1         .||. ce2 = CExp [cexp|$ce1 || $ce2|]

instance IsBits (CExp l) where
    CInt x ..&.. CInt i = CInt (x .&. i)
    ce     ..&.. i      = CExp [cexp|$ce & $i|]

    CInt x ..|.. CInt i = CInt (x .|. i)
    ce     ..|.. i      = CExp [cexp|$ce | $i|]

    CInt x `shiftL'` CInt i = CInt (x `shiftL` fromIntegral i)
    x      `shiftL'` CInt 0 = x
    ce     `shiftL'` i      = CExp [cexp|$ce << $i|]

    CInt x `shiftR'` CInt i = CInt (x `shiftR` fromIntegral i)
    x      `shiftR'` CInt 0 = x
    ce     `shiftR'` i      = CExp [cexp|$ce >> $i|]

instance C.ToExp (CExp l) where
    toExp CVoid                      = locatedError $
                                       text "toExp: void compiled expression"
    toExp (CBool i)                  = const [cexp|$int:(if i then 1::Integer else 0)|]
    toExp (CInt i)                   = const [cexp|$int:i|]
    toExp (CFloat r)                 = const [cexp|$double:r|]
    toExp (CExp e)                   = const e
    toExp ce@(CInit _)               = locatedError $
                                       text "toExp: cannot convert CInit to a C expression" </> ppr ce
    toExp (CPtr e)                   = C.toExp e
    toExp (CIdx tau carr cidx)       = const $ lowerIdx tau carr cidx
    toExp (CSlice tau carr cidx len) = const $ lowerSlice tau carr cidx len
    toExp ce@CStruct{}               = locatedError $
                                       text "toExp: cannot convert CStruct to a C expression" </> ppr ce
    toExp (CBits ce)                 = C.toExp ce
    toExp (CAlias _ ce)              = C.toExp ce
    toExp ce@CComp{}                 = locatedError $
                                       text "toExp: cannot convert CComp to a C expression" </> ppr ce
    toExp ce@CFunComp{}              = locatedError $
                                       text "toExp: cannot convert CFunComp to a C expression" </> ppr ce

locatedError :: Located a => Doc -> a -> b
locatedError doc loc =
    errordoc $ ppr (locOf loc) <> text ":" </> doc

instance Pretty (CExp l) where
    ppr CVoid                    = text "<void>"
    ppr (CBool True)             = text "true"
    ppr (CBool False)            = text "false"
    ppr (CInt i)                 = ppr i
    ppr (CFloat f)               = ppr f
    ppr (CExp e)                 = ppr e
    ppr (CInit cinit)            = ppr cinit
    ppr (CPtr e)                 = ppr [cexp|*$e|]
    ppr (CIdx _ carr cidx)       = ppr carr <> brackets (ppr cidx)
    ppr (CSlice _ carr cidx len) = ppr carr <> brackets (ppr cidx <> colon <> ppr len)
    ppr (CStruct flds)           = pprStruct flds
    ppr (CBits e)                = ppr e
    ppr (CAlias _ e)             = ppr e
    ppr CComp{}                  = text "<comp>"
    ppr CFunComp{}               = text "<fun comp>"

-- | Tag the translation of an expression with the expression is aliases.
calias :: Exp -> CExp l -> CExp l
calias _ ce@CVoid    = ce
calias _ ce@CBool{}  = ce
calias _ ce@CInt{}   = ce
calias _ ce@CFloat{} = ce
calias _ ce@CInit{}  = ce
calias e ce          = case refPath e of
                         Nothing -> ce
                         Just _  -> CAlias e ce

-- | Given a 'CExp' that is potentially a slice of an array, return the base
-- array and the index at which the slice begins. If the input 'CExp' is not a
-- slice, the returned index is 0.
unCSlice :: CExp l -> (CExp l, CExp l)
unCSlice (CSlice _ carr cidx _) = (carr, cidx)
unCSlice carr                   = (carr, 0)

-- | Given a 'CExp' that is potentially a slice of a /bit/ array, return the
-- array base of the slice, i.e., a pointer to the beginning of the slice. This
-- function is partial; the base array can only be calculated if the index of
-- the slice is certain to be divisible by 'bIT_ARRAY_ELEM_BITS'.
unBitCSliceBase :: CExp l -> Maybe (CExp l)
unBitCSliceBase (CSlice _ carr (CInt i) _) | bitOff == 0 =
    Just $ CExp [cexp|&$carr[$int:bitIdx]|]
  where
    bitIdx, bitOff :: Integer
    (bitIdx, bitOff) = i `quotRem` bIT_ARRAY_ELEM_BITS

unBitCSliceBase (CSlice _ carr (CExp [cexp|$int:n * $ce|]) _)
    | q == 1 && r == 0 = Just $ CExp [cexp|&$carr[$ce]|]
    | r == 0           = Just $ CExp [cexp|&$carr[$int:q * $ce]|]
  where
    q, r :: Integer
    (q, r) = n `quotRem` bIT_ARRAY_ELEM_BITS

unBitCSliceBase (CSlice _ carr (CExp [cexp|$ce * $int:n|]) _)
    | q == 1 && r == 0 = Just $ CExp [cexp|&$carr[$ce]|]
    | r == 0           = Just $ CExp [cexp|&$carr[$int:q * $ce]|]
  where
    q, r :: Integer
    (q, r) = n `quotRem` bIT_ARRAY_ELEM_BITS

unBitCSliceBase CSlice{}    =
    Nothing

unBitCSliceBase ce =
    Just ce

toInit :: CExp l -> C.Initializer
toInit (CInit cinit) = cinit
toInit ce            = [cinit|$ce|]

-- | Lower an array indexing operation to a 'C.Exp'
lowerIdx :: forall l . Type -> CExp l -> CExp l -> C.Exp
lowerIdx tau carr ci
    | isBitT tau = C.toExp (CExp [cexp|($carr[$cbitIdx] & $cbitMask)|] `shiftR'` cbitOff) l
    | otherwise  = [cexp|$carr[$ci]|]
  where
    cbitIdx, cbitOff :: CExp l
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp l
    cbitMask = 1 `shiftL'` cbitOff

    l :: SrcLoc
    l = carr `srcspan` ci

-- | Lower a slice operation to a 'C.Exp'
lowerSlice :: Type -> CExp l -> CExp l -> Int -> C.Exp
lowerSlice tau carr cidx len | isBitT tau =
    case unBitCSliceBase (CSlice tau carr cidx len) of
      Just (CExp ce) -> ce
      _ -> errordoc $ nest 4 $
           ppr (locOf cidx) <> text ":" </>
           text "lowerCSlice: cannot take slice of bit array where index is not a divisor of the bit width:" </>
           ppr (CSlice tau carr cidx len)

lowerSlice _ carr cidx _ =
    [cexp|&$carr[$cidx]|]
