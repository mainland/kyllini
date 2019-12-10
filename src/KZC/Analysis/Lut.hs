{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Analysis.Lut
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Analysis.Lut (
    LUTInfo(..),
    lutInfo,

    LUTVar(..),
    unLUTVar,
    inferLUTVar,

    shouldLUT
  ) where

import Control.Monad.Exception (MonadException(..),
                                SomeException)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            execStateT,
                            gets,
                            modify)
import Control.Monad.Trans (MonadTrans(..))
import Data.Loc (Located(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes,
                   fromMaybe)
import Data.Monoid ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Mainland hiding (width)
import Text.PrettyPrint.Mainland.Class

import KZC.Analysis.Interval (IsInterval(..))
import KZC.Analysis.Lattice (bot)
import KZC.Analysis.ReadWriteSet
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Fuel
import KZC.Name
import KZC.Platform
import KZC.Util.Error
import KZC.Util.Summary
import KZC.Util.Trace
import KZC.Util.Uniq
import KZC.Vars

shouldLUT :: forall m . MonadTc m => LUTInfo -> Exp -> m Bool
shouldLUT info e = do
    dflags <- askConfig
    ((Right <$> lutStats e) `catch`
        \(err :: SomeException) -> return (Left err)) >>= go dflags
  where
    go :: Config -> Either SomeException LUTStats -> m Bool
    go _ Left{} =
        return False

    go dflags (Right stats) = do
        traceAutoLUT $ ppr stats
        return $ lutInBits info > 0 &&
                 lutInBits info <= 64 &&
                 lutOutBits info + lutResultBits info > 0 &&
                 (lutOpCount stats >= minLUTOps dflags || lutHasLoop stats) &&
                 not (lutHasSideEffect stats) &&
                 lutBytesLog2 info <= fromIntegral (maxLUTLog2 dflags) &&
                 lutBytes info <= fromIntegral (maxLUT dflags)

data LUTInfo = LUTInfo
    { -- Free variables
      lutInVars     :: Set LUTVar
      -- Variables written to
    , lutOutVars    :: Set LUTVar
      -- The result of the expression iff it is an out variable.
    , lutResultVar  :: Maybe Var
      -- Type of the expressions
    , lutResultType :: Type
      -- LUT refs
    , lutRWSets     :: Map Var RWSet

      -- Bit size of LUT input
    , lutInBits     :: Int
      -- Bit size of LUT output
    , lutOutBits    :: Int
      -- Bit size of LUT result
    , lutResultBits :: Int

      -- Size in bytes of the LUT
    , lutBytes     :: Integer
      -- log_2 of the size in bytes of the LUT
    , lutBytesLog2 :: Int
    }

instance Pretty LUTInfo where
    ppr info =
        nest 2 (text "In vars:" </> ppr (lutInVars info)) </>
        nest 2 (text "Out vars:" </> ppr (lutOutVars info)) </>
        nest 2 (text "Result var:" <+> ppr (lutResultVar info)) </>
        nest 2 (text "Result type:" <+> ppr (lutResultType info)) </>
        nest 2 (text "Read/write sets:" </> ppr (lutRWSets info)) </>
        nest 2 (text "In bits:    " <+> ppr (lutInBits info)) </>
        nest 2 (text "Out bits:   " <+> ppr (lutOutBits info)) </>
        nest 2 (text "Result bits:" <+> ppr (lutResultBits info)) </>
        nest 2 (text "LUT size in bytes (log 2):" <+> ppr (lutBytesLog2 info))

data LUTVar = VarL Var
            | IdxL Var Int (Maybe Int)
  deriving (Eq, Ord, Show)

instance Pretty LUTVar where
    ppr (VarL v) =
        ppr v

    ppr (IdxL v i Nothing) =
        ppr v <> brackets (ppr i)

    ppr (IdxL v i (Just len)) =
        ppr v <> brackets (commasep [ppr i, ppr len])

instance Located LUTVar where
    locOf (VarL v)     = locOf v
    locOf (IdxL v _ _) = locOf v

instance Named LUTVar where
    namedSymbol (VarL v)     = namedSymbol v
    namedSymbol (IdxL v _ _) = namedSymbol v

    mapName f (VarL v)           = VarL (mapName f v)
    mapName f (IdxL v start len) = IdxL (mapName f v) start len

instance Summary LUTVar where
    summary (VarL v)     = summary v
    summary (IdxL v _ _) = summary v

instance ToExp LUTVar where
    toExp (VarL v)                  = varE v
    toExp (IdxL v start Nothing)    = idxE (varE v) (fromIntegral start)
    toExp (IdxL v start (Just len)) = sliceE (varE v) (fromIntegral start) len

unLUTVar :: LUTVar -> Var
unLUTVar (VarL v)     = v
unLUTVar (IdxL v _ _) = v

idxL :: Integral a => Var -> a -> LUTVar
idxL v i = IdxL v (fromIntegral i) Nothing

sliceL :: Integral a => Var -> a -> a -> LUTVar
sliceL v i len = IdxL v (fromIntegral i) (Just (fromIntegral len))

inferLUTVar :: MonadTc m => LUTVar -> m Type
inferLUTVar (VarL v) =
    lookupVar v

inferLUTVar (IdxL v _ maybe_len) = do
    (_, tau) <- lookupVar v >>= checkArrOrRefArrT
    return $ arrKnownT n tau
  where
    n :: Int
    n = fromMaybe 1 maybe_len

lutInfo :: forall m . MonadTc m => Exp -> m LUTInfo
lutInfo e = withFvContext e $ do
    tau_res           <- inferExp e
    rw                <- readWriteSets e
    (inVars, outVars) <- lutVars rw
    let resVar        =  case resultVar e of
                           Just v | v `Set.member` Set.map unLUTVar outVars -> Just v
                           _ -> Nothing
    inbits            <- sum <$> mapM lutVarSize (Set.toList inVars)
    outbits           <- sum <$> mapM lutVarSize (Set.toList outVars)
    resbits           <- case resVar of
                           Just{}  -> return 0
                           Nothing -> typeSize tau_res
    let outbytes :: Int
        outbytes = (outbits + resbits + 7) `div` 8
    return LUTInfo { lutInVars     = inVars
                   , lutOutVars    = outVars
                   , lutResultVar  = resVar
                   , lutResultType = tau_res
                   , lutRWSets     = rw

                   , lutInBits     = inbits
                   , lutOutBits    = outbits
                   , lutResultBits = resbits

                   , lutBytes      = 2^inbits * fromIntegral outbytes
                   , lutBytesLog2  = inbits +
                                     ceiling (logBase (2 :: Double)
                                                      (fromIntegral outbytes))
                   }
  where
    lutVarSize :: LUTVar -> m Int
    lutVarSize v =
        withSummaryContext v $ do
        tau <- inferLUTVar v
        typeSize tau

lutVars :: forall m . MonadTc m
        => Map Var RWSet
        -> m (Set LUTVar, Set LUTVar)
lutVars refs = do
    inVars  <- catMaybes <$> mapM inLutVar (Map.assocs refs)
    outVars <- catMaybes <$> mapM outLutVar (Map.assocs refs)
    return (Set.fromList inVars, Set.fromList outVars)
  where
    -- | Convert a variable and its reads/write set to an in 'LUTVar'.
    inLutVar :: (Var, RWSet) -> m (Maybe LUTVar)
    inLutVar (v, VarRW rs _ws) | rs /= bot =
        return $ Just $ VarL v

    inLutVar (v, ArrayRW rs _ws) | Just (lo, hi) <- fromInterval rs = do
        (nat, _) <- lookupVar v >>= checkArrOrRefArrT
        return $ Just $ rangeLUTVar v lo hi nat

    inLutVar (v, rws@(ArrayRW rs _ws)) | rs /= bot || weaklyUpdated rws =
        return $ Just $ VarL v

    inLutVar (v, rws@(StructRW rs _ws)) | rs /= bot || weaklyUpdated rws =
        return $ Just $ VarL v

    inLutVar (v, TopRW) =
        return $ Just $ VarL v

    inLutVar _ =
        return Nothing

    -- | Convert a variable and its 'RWSet' to an out 'LUTVar'.
    outLutVar :: (Var, RWSet) -> m (Maybe LUTVar)
    outLutVar (v, VarRW _rs ws) | ws /= bot =
        return $ Just $ VarL v

    outLutVar (v, ArrayRW _rs ws) | Just (lo, hi) <- fromInterval ws = do
        (nat, _) <- lookupVar v >>= checkArrOrRefArrT
        return $ Just $ rangeLUTVar v lo hi nat

    outLutVar (v, ArrayRW _rs ws) | ws /= bot =
        return $ Just $ VarL v

    outLutVar (v, StructRW _rs ws) | ws /= bot =
        return $ Just $ VarL v

    outLutVar (v, TopRW) =
        return $ Just $ VarL v

    outLutVar _ =
        return Nothing

    -- | Convert a variable range into a 'LUTVar'
    rangeLUTVar:: Var -> Integer -> Integer -> Type -> LUTVar
    -- We need the whole array
    rangeLUTVar v lo hi (NatT n _)
      | lo == 0 && hi == fromIntegral n-1 = VarL v

    -- We need either one element or a slice
    rangeLUTVar v lo hi _
      | hi == lo  = idxL v lo
      | otherwise = sliceL v lo (hi-lo+1)

-- | Compute the variable that is the result expression. This is a partial
-- operation. Note that the variable may have type ref, in which case its
-- dereferenced value is the result of the expression.
resultVar :: Monad m => Exp -> m Var
resultVar (VarE v _) =
    return v

resultVar (LetE decl e _) = do
    v <- resultVar e
    if v `Set.member` binders decl
      then fail "Result is locally bound"
      else return v

resultVar (ReturnE _ e _) =
    resultVar e

resultVar (IfE _ e1 e2 _) = do
    v1 <- resultVar e1
    v2 <- resultVar e2
    if v1 == v2
      then return v1
      else fail "Different variables returned"

resultVar (DerefE (VarE v   _) _) =
    return v

resultVar (BindE (TameV v') _
                   (DerefE    (VarE v   _) _)
                   (ReturnE _ (VarE v'' _) _) _)
    | v'' == bVar v' = return v

resultVar (BindE _ _ _ e _) =
    resultVar e

resultVar _ =
    fail "No variable returned"

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
              MonadConfig,
              MonadFuel,
              MonadPlatform,
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
    go ConstE{} =
        return ()

    go VarE{} =
        return ()

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
        -- Conditionals are expensive!
        addOpCount 5

    go (LetE (LetLD _ _ e1 _) e2 _) = do
        go e1
        go e2

    go (LetE (LetRefLD _ _ Nothing _) e _) =
        go e

    go (LetE (LetRefLD _ _ (Just e1) _) e2 _) = do
        go e1
        go e2

    go (LetE LetTypeLD{} e2 _) =
        go e2

    go (LetE (LetViewLD _ _ (IdxVW _ e1 _ _) _) e2 _) = do
        go e1
        go e2

    go CallE{} =
        fail "Cannot LUT function call"

    go (DerefE e _) = do
        go e
        incOpCount

    go (AssignE e1 e2 _) = do
        go e1
        go e2

    go LowerE{} =
        return ()

    go (WhileE e1 e2 _) = do
        hasLoop
        go e1
        go e2

    go (ForE _ _ _ gint e3 _) = do
        hasLoop
        go e1
        go e2
        go e3
      where
        e1, e2 :: Exp
        (e1, e2) = toStartLenGenInt gint

    go (ArrayE es _) =
        mapM_ go es

    go (IdxE e1 e2 _ _) = do
        go e1
        go e2

    go (StructE _ _ flds _) =
        mapM_ (go . snd) flds

    go (ProjE e _ _) =
        go e

    go (CastE _ e _) = do
        go e
        incOpCount

    go BitcastE{} =
        fail "Cannot LUT bitcast"

    go PrintE{} =
        hasSideEffect

    go ErrorE{} =
        hasSideEffect

    go (ReturnE _ e _) =
        go e

    go (BindE _ _ e1 e2 _) = do
        go e1
        go e2

    go (LutE _ e) =
        go e

    go (GenE e _ _) =
        go e
