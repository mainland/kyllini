{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Cg.CExp
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Cg.CExp (
    CExp(..),

    cgBitArrayRead
  ) where

import Prelude hiding (elem)

import Data.Bits
import Data.Loc
import Data.Monoid
import qualified Language.C.Syntax as C
import Text.PrettyPrint.Mainland

import KZC.Auto.Syntax
import KZC.Platform
import KZC.Quote.C
import KZC.Staged

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
          | CComp Var [IVar] [(Var, Type)] Type LComp
            -- ^ A computation, which may take arguments.
  deriving (Show)

instance Located CExp where
    locOf CVoid                = NoLoc
    locOf (CBool {})           = NoLoc
    locOf (CBit {})            = NoLoc
    locOf (CInt {})            = NoLoc
    locOf (CFloat {})          = NoLoc
    locOf (CExp ce)            = locOf ce
    locOf (CPtr ce)            = locOf ce
    locOf (CIdx _ _ cidx)      = locOf cidx
    locOf (CSlice _ _ cidx _)  = locOf cidx
    locOf (CComp _ _ _ _ comp) = locOf comp

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
    toExp (CComp {})                 = error "toExp: cannot convert CComp to a C expression"

instance Pretty CExp where
    ppr CVoid                      = text "<void>"
    ppr (CBool True)               = text "true"
    ppr (CBool False)              = text "false"
    ppr (CBit True)                = text "'1"
    ppr (CBit False)               = text "'0"
    ppr (CInt i)                   = ppr i
    ppr (CFloat f)                 = ppr f
    ppr (CExp e)                   = ppr e
    ppr (CPtr e)                   = ppr [cexp|*$e|]
    ppr (CIdx _ carr cidx)         = ppr carr <> brackets (ppr cidx)
    ppr (CSlice _ carr cidx len)   = ppr carr <> brackets (ppr cidx <> colon <> ppr len)
    ppr (CComp v []  []  tau comp) = ppr (LetCompD v tau comp noLoc)
    ppr (CComp f ibs vbs tau comp) = ppr (LetFunCompD f ibs vbs tau comp noLoc)

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

-- | Read an element from a bit array.
cgBitArrayRead :: CExp -> CExp -> C.Exp
cgBitArrayRead carr ci =
    [cexp|($carr[$cbitIdx] & $cbitMask) ? 1 : 0|]
  where
    cbitIdx, cbitOff :: CExp
    (cbitIdx, cbitOff) = ci `quotRem` bIT_ARRAY_ELEM_BITS

    cbitMask :: CExp
    cbitMask = 1 `shiftL'` cbitOff
