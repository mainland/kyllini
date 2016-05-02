{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Lut
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.Lut (
    LUTInfo(..),
    lutInfo,

    shouldLUT,

    returnedVar
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative, (<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            execStateT,
                            gets,
                            modify)
import Control.Monad.Trans (MonadTrans(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Text.PrettyPrint.Mainland hiding (width)

import KZC.Analysis.Abs (absEval)
import KZC.Analysis.Dataflow (DState(..),
                              runD)
import KZC.Analysis.NeedDefault (defaultsUsedExp)
import KZC.Analysis.Range ()
import KZC.Auto.Lint
import KZC.Auto.Syntax
import KZC.Error
import KZC.Flags
import KZC.Summary
import KZC.Trace
import KZC.Uniq

shouldLUT :: forall m . MonadTc m => LUTInfo -> Exp -> m Bool
shouldLUT info e = do
    dflags <- askFlags
    ((Right <$> lutStats e) `catch`
        \(err :: SomeException) -> return (Left err)) >>= go dflags
  where
    go :: Flags -> Either SomeException LUTStats -> m Bool
    go _ Left{} =
        return False

    go dflags (Right stats) = do
        traceAutoLUT $ ppr stats
        return $ lutBytesLog2 info <= fromIntegral (maxLUTLog2 dflags) &&
                 lutBytes info <= fromIntegral (maxLUT dflags) &&
                 lutInBits info <= 64 &&
                 lutOutBits info + lutResultBits info > 0 &&
                 lutOutBits info + lutResultBits info <= 64 &&
                 (lutOpCount stats >= minLUTOps dflags || lutHasLoop stats) &&
                 not (lutHasSideEffect stats)

-- | Compute the variable that is returned by an expression. This is a partial
-- operation. Note that the variable may have type ref, in which case its
-- dereferenced value is what is returned.
returnedVar :: Monad m => Exp -> m Var
returnedVar (VarE v _) = do
    return v

returnedVar (LetE _ e _) =
    returnedVar e

returnedVar (ReturnE _ e _) =
    returnedVar e

returnedVar (IfE _ e1 e2 _) = do
    v1 <- returnedVar e1
    v2 <- returnedVar e2
    if v1 == v2
      then return v1
      else fail "Different variables returned"

returnedVar (DerefE (VarE v   _) _) =
    return v

returnedVar (BindE (TameV v') _
                   (DerefE    (VarE v   _) _)
                   (ReturnE _ (VarE v'' _) _) _)
    | v'' == bVar v' = return v

returnedVar (BindE _ _ _ e _) =
    returnedVar e

returnedVar _ =
    fail "No variable returned"

data LUTInfo = LUTInfo
    { lutInVars      :: Set Var
    , lutOutVars     :: Set Var
    , lutReturnedVar :: Maybe Var

    , lutInBits     :: Int
    , lutOutBits    :: Int
    , lutResultBits :: Int

    , lutBytes     :: Integer
    , lutBytesLog2 :: Int
    }

instance Pretty LUTInfo where
    ppr info =
        nest 2 (text "In vars:" </> ppr (lutInVars info)) </>
        nest 2 (text "Out vars:" </> ppr (lutOutVars info)) </>
        nest 2 (text "Returned var:" <+> ppr (lutReturnedVar info)) </>
        nest 2 (text "In bits:    " <+> ppr (lutInBits info)) </>
        nest 2 (text "Out bits:   " <+> ppr (lutOutBits info)) </>
        nest 2 (text "Result bits:" <+> ppr (lutResultBits info)) </>
        nest 2 (text "LUT size in bytes (log 2):" <+> ppr (lutBytesLog2 info))

lutInfo :: forall m . MonadTc m => Exp -> m LUTInfo
lutInfo e = withFvContext e $ do
    (_, st)     <- runD (absEval e)
    tau_res     <- inferExp e
    inVars      <- defaultsUsedExp e
    let outVars =  (Map.keysSet . usedefs) st
    let retVar  =  returnedVar e
    inbits      <- sum <$> mapM varSize (Set.toList inVars)
    outbits     <- sum <$> mapM varSize (Set.toList outVars)
    resbits     <- case retVar of
                     Just v | v `Set.member` outVars -> return 0
                     _ -> typeSize tau_res
    let outbytes :: Int
        outbytes = (outbits + resbits + 7) `div` 8
    return $ LUTInfo { lutInVars      = inVars
                     , lutOutVars     = outVars
                     , lutReturnedVar = retVar

                     , lutInBits     = inbits
                     , lutOutBits    = outbits
                     , lutResultBits = resbits

                     , lutBytes      = 2^inbits * fromIntegral outbytes
                     , lutBytesLog2  = inbits + ceiling (log (fromIntegral outbytes) / log (2 :: Double))
                     }
  where
    varSize :: Var -> m Int
    varSize v = withSummaryContext v $ do
        tau <- lookupVar v
        typeSize tau

data LUTStats = LUTStats
    { lutOpCount       :: !Int
    , lutHasLoop       :: !Bool
    , lutHasSideEffect :: !Bool
    }

instance Pretty LUTStats where
    ppr info =
        nest 2 (text "Op count:" <+> ppr (lutOpCount info)) </>
        nest 2 (text "Has loop:" <+> ppr (lutHasLoop info)) </>
        nest 2 (text "Has side effect:" <+> ppr (lutHasSideEffect info))

defaultLUTStats :: LUTStats
defaultLUTStats = LUTStats
    { lutOpCount       = 0
    , lutHasLoop       = False
    , lutHasSideEffect = False
    }

newtype L m a = L { unL :: StateT LUTStats m a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadState LUTStats,
              MonadException,
              MonadUnique,
              MonadErr,
              MonadFlags,
              MonadTrace,
              MonadTc)

execL :: MonadTc m => L m () -> m LUTStats
execL m = execStateT (unL m) defaultLUTStats

instance MonadTrans L where
    lift = L . lift

addOpCount :: Monad m => Int -> L m ()
addOpCount x = modify $ \s -> s { lutOpCount = lutOpCount s + x }

incOpCount :: Monad m => L m ()
incOpCount = modify $ \s -> s { lutOpCount = lutOpCount s + 1 }

opCount :: Monad m => L m () -> L m Int
opCount act = do
    ops1 <- gets lutOpCount
    act
    ops2 <- gets lutOpCount
    modify $ \s -> s { lutOpCount = ops1 }
    return $ ops2 - ops1

hasLoop :: Monad m => L m ()
hasLoop = modify $ \s -> s { lutHasLoop = True }

hasSideEffect :: Monad m => L m ()
hasSideEffect = modify $ \s -> s { lutHasSideEffect = True }

lutStats :: forall m . MonadTc m => Exp -> m LUTStats
lutStats e =
   execL $ go e
  where
    go :: Exp -> L m ()
    go (ConstE {}) =
        return ()

    go (VarE {}) =
        return ()

    go (UnopE Bitcast{} _ _) =
        fail "Cannot LUT bitcast"

    go (UnopE Len{} e _) =
        go e

    go (UnopE _ e _) = do
        go e
        incOpCount

    go (BinopE Cat _ _ _) =
        fail "Cannot LUT array concatenation"

    go (BinopE _ e1 e2 _) = do
        go e1
        go e2
        incOpCount

    go (IfE e1 e2 e3 _) = do
        go e1
        ops1 <- opCount $ go e2
        ops2 <- opCount $ go e3
        addOpCount $ max ops1 ops2

    go (LetE (LetLD _ _ e1 _) e2 _) = do
        go e1
        go e2

    go (LetE (LetRefLD _ _ Nothing _) e _) =
        go e

    go (LetE (LetRefLD _ _ (Just e1) _) e2 _) = do
        go e1
        go e2

    go (CallE _ _ es _) =
        mapM_ go es

    go (DerefE e _) = do
        go e
        incOpCount

    go (AssignE e1 e2 _) = do
        go e1
        go e2

    go (WhileE e1 e2 _) = do
        hasLoop
        go e1
        go e2

    go (ForE _ _ _ e1 e2 e3 _) = do
        hasLoop
        go e1
        go e2
        go e3

    go (ArrayE es _) =
        mapM_ go es

    go (IdxE e1 e2 _ _) = do
        go e1
        go e2

    go (StructE _ flds _) =
        mapM_ go (map snd flds)

    go (ProjE e _ _) =
        go e

    go (PrintE {}) =
        hasSideEffect

    go (ErrorE {}) =
        hasSideEffect

    go (ReturnE _ e _) =
        go e

    go (BindE _ _ e1 e2 _) = do
        go e1
        go e2

    go (LutE e) =
        go e
