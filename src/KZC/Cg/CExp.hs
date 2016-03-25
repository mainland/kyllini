{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg.CExp
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.CExp (
    TakeK,
    EmitK,
    CompC,
    FunCompC,

    CExp(..),

    toInit
  ) where

import Prelude hiding (elem)

import Data.Bits
import Data.Loc
import Data.Monoid
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Auto.Smart
import KZC.Auto.Syntax
import KZC.Label
import {-# SOURCE #-} KZC.Cg.Monad
import KZC.Platform
import KZC.Quote.C
import KZC.Staged

-- | Generate code to take the specified number of elements of the specified
-- type, jumping to the specified label when the take is complete. A 'CExp'
-- representing the taken value(s) is returned. We assume that the continuation
-- labels the code that will be generated immediately after the take.
type TakeK l = Int -> Type -> l -> Cg CExp

-- | Generate code to emit the specified value at the specified type jumping to
-- the specified label when the take is complete. We assume that the
-- continuation labels the code that will be generated immediately after the
-- emit.
type EmitK l = Type -> CExp -> l -> Cg ()

-- | A computation compiler, which produces a compiled computation when given
-- the appropriate arguments.
type CompC =  TakeK Label -- Code generator for take
           -> EmitK Label -- Code generator for emit
           -> Label       -- Label of our continuation
           -> Cg CExp     -- Value returned by the computation.

instance Show CompC where
    show _ = "<comp>"

-- | A computation function compiler, which produces a compiled call to a
-- computation function when given the appropriate arguments.
type FunCompC =  [Iota]      -- Array length arguments
              -> [LArg]      -- Function arguments
              -> TakeK Label -- Code generator for take
              -> EmitK Label -- Code generator for emit
              -> Label       -- Label of our continuation
              -> Cg CExp     -- Value returned by the computation.

instance Show FunCompC where
    show _ = "<funcomp>"

-- | The type of "compiled" expressions.
data CExp = CVoid
          | CBool Bool
          | CBit Bool
          | CInt Integer     -- ^ Integer constant
          | CFloat Rational  -- ^ Float constant
          | CExp C.Exp       -- ^ C expression
          | CInit C.Initializer
            -- ^ A list of C initializers for a constant
          | CPtr CExp        -- ^ A pointer.
          | CIdx Type CExp CExp
            -- ^ An array element. The data constructor's arguments are the type
            -- of the array's elements, the array, and the index.
          | CSlice Type CExp CExp Int
            -- ^ An array slice. The data constructor's arguments are the type
            -- of the array's elements, the array, the offset, the length of the
            -- slice.
          | CBits CExp
            -- ^ A bit array represented as an integer
          | CComp CompC
            -- ^ A computation.
          | CFunComp FunCompC
            -- ^ A computation function.
  deriving (Show)

instance Located CExp where
    locOf CVoid               = NoLoc
    locOf (CBool {})          = NoLoc
    locOf (CBit {})           = NoLoc
    locOf (CInt {})           = NoLoc
    locOf (CFloat {})         = NoLoc
    locOf (CExp ce)           = locOf ce
    locOf (CInit cinit)       = locOf cinit
    locOf (CPtr ce)           = locOf ce
    locOf (CIdx _ _ cidx)     = locOf cidx
    locOf (CSlice _ _ cidx _) = locOf cidx
    locOf (CBits ce)          = locOf ce
    locOf (CComp {})          = NoLoc
    locOf (CFunComp {})       = NoLoc

instance Relocatable CExp where
    reloc _ ce@CVoid                   = ce
    reloc _ ce@(CBool {})              = ce
    reloc _ ce@(CBit {})               = ce
    reloc _ ce@(CInt {})               = ce
    reloc _ ce@(CFloat {})             = ce
    reloc l (CExp ce)                  = CExp $ reloc l ce
    reloc l (CInit cinit)              = CInit $ reloc l cinit
    reloc l (CPtr ce)                  = CPtr $ reloc l ce
    reloc l (CIdx tau carr cidx)       = CIdx tau (reloc l carr) (reloc l cidx)
    reloc l (CSlice tau carr cidx len) = CSlice tau (reloc l carr) (reloc l cidx) len
    reloc l (CBits ce)                 = CBits (reloc l ce)
    reloc _ ce@(CComp {})              = ce
    reloc _ ce@(CFunComp {})           = ce

instance IfThenElse CExp CExp where
    ifThenElse (CBool True)  t _ = t
    ifThenElse (CBool False) _ e = e
    ifThenElse c             t e = CExp [cexp|$c ? $t : $e|]

instance Eq CExp where
    CVoid          == CVoid          = True
    CBool x        == CBool y        = x == y
    CBit x         == CBit y         = x == y
    CInt x         == CInt y         = x == y
    CFloat x       == CFloat y       = x == y
    CPtr x         == CPtr y         = x == y
    CIdx r s t     == CIdx x y z     = (r,s,t) == (x,y,z)
    CSlice q r s t == CSlice w x y z = (q,r,s,t) == (w,x,y,z)
    CBits x        == CBits y        = x == y
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
    compare (CBits x)        (CBits y)        = compare x y
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

instance ToExp CExp where
    toExp CVoid                      = error "toExp: void compiled expression"
    toExp (CBool i)                  = \_ -> [cexp|$int:(if i then 1::Integer else 0)|]
    toExp (CBit i)                   = \_ -> [cexp|$int:(if i then 1::Integer else 0)|]
    toExp (CInt i)                   = \_ -> [cexp|$int:i|]
    toExp (CFloat r)                 = \_ -> [cexp|$double:r|]
    toExp (CExp e)                   = \_ -> e
    toExp (CInit _)                  = error "toExp: cannot convert CInit to a C expression"
    toExp (CPtr e)                   = toExp e
    toExp (CIdx tau carr cidx)       = \_ -> lowerIdx tau carr cidx
    toExp (CSlice tau carr cidx len) = \_ -> lowerSlice tau carr cidx len
    toExp (CBits ce)                 = toExp ce
    toExp (CComp {})                 = error "toExp: cannot convert CComp to a C expression"
    toExp (CFunComp {})              = error "toExp: cannot convert CFunComp to a C expression"

instance Pretty CExp where
    ppr CVoid                    = text "<void>"
    ppr (CBool True)             = text "true"
    ppr (CBool False)            = text "false"
    ppr (CBit True)              = text "'1"
    ppr (CBit False)             = text "'0"
    ppr (CInt i)                 = ppr i
    ppr (CFloat f)               = ppr f
    ppr (CExp e)                 = ppr e
    ppr (CInit cinit)            = ppr cinit
    ppr (CPtr e)                 = ppr [cexp|*$e|]
    ppr (CIdx _ carr cidx)       = ppr carr <> brackets (ppr cidx)
    ppr (CSlice _ carr cidx len) = ppr carr <> brackets (ppr cidx <> colon <> ppr len)
    ppr (CBits e)                = ppr e
    ppr (CComp {})               = text "<comp>"
    ppr (CFunComp {})            = text "<fun comp>"

toInit :: CExp -> C.Initializer
toInit (CInit cinit) = cinit
toInit ce            = [cinit|$ce|]

-- | Lower an array indexing operation to a 'C.Exp'
lowerIdx :: Type -> CExp -> CExp -> C.Exp
lowerIdx tau carr ci
    | isBitT tau = toExp (CExp [cexp|($carr[$cbitIdx] & $cbitMask)|] `shiftR'` cbitOff) l
    | otherwise  = [cexp|$carr[$ci]|]
  where
    cbitIdx, cbitOff :: CExp
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp
    cbitMask = 1 `shiftL'` cbitOff

    l :: SrcLoc
    l = carr `srcspan` ci

-- | Lower a slice operation to a 'C.Exp'
lowerSlice :: Type -> CExp -> CExp -> Int -> C.Exp
lowerSlice tau carr ce@(CInt i) len | isBitT tau =
    if bitOff == 0
    then [cexp|&$carr[$int:bitIdx]|]
    else errordoc $ nest 4 $
         ppr (locOf ce) <> text ":" </>
         text "lowerCSlice: cannot take slice of bit array where index is not a divisor of the bit width:" </>
         ppr (CSlice tau carr ce len)
  where
    bitIdx, bitOff :: Integer
    (bitIdx, bitOff) = i `quotRem` bIT_ARRAY_ELEM_BITS

lowerSlice _ carr cidx _ =
    [cexp|&$carr[$cidx]|]
