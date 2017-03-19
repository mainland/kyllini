{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.LutToGen
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Optimize.LutToGen (
    lutToGen,
    lutGenToExp
  ) where

import Control.Monad (unless)
import Control.Monad.Exception (MonadException(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..),
                             ReaderT(..),
                             asks)
import Control.Monad.State (MonadState(..),
                            StateT(..),
                            evalStateT,
                            gets,
                            modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Bits (shiftL)
import Data.Foldable (toList)
import Data.List ((\\))
import Data.Loc (noLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence ((|>),
                      Seq)
import Text.PrettyPrint.Mainland

import KZC.Analysis.Lut
import KZC.Config
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Label
import KZC.Name
import KZC.Optimize.LowerViews
import KZC.Util.Error
import KZC.Util.Staged
import KZC.Util.Trace
import KZC.Util.Uniq

data GState l = GState
    { topDecls :: !(Seq (Decl l))
    , luts     :: Map Exp (Var, StructDef)
    }

defaultGState :: GState l
defaultGState = GState mempty mempty

newtype G l m a = G { unG :: StateT (GState l) m a }
  deriving (Applicative, Functor, Monad, MonadIO,
            MonadState (GState l),
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadTrace,
            MonadTc)

instance MonadTrans (G l) where
    lift = G . lift

runG :: MonadTc m => G l m a -> m a
runG m = evalStateT (unG m) defaultGState

getTopDecls :: MonadTc m => G l m [Decl l]
getTopDecls = do
    decls <- gets topDecls
    modify $ \s -> s { topDecls = mempty }
    return $ toList decls

appendTopDecl :: MonadTc m => Decl l -> G l m ()
appendTopDecl decl = modify $ \s -> s { topDecls = topDecls s |> decl }

lookupLUT :: MonadTc m => Exp -> G l m (Maybe (Var, StructDef))
lookupLUT e = gets (Map.lookup e . luts)

insertLUT :: MonadTc m => Exp -> Var -> StructDef -> G l m ()
insertLUT e v structdef =
    modify $ \s -> s { luts = Map.insert e (v, structdef) (luts s) }

lutToGen :: forall l m . (IsLabel l, MonadTc m)
         => Program l
         -> m (Program l)
lutToGen = runG . lutProgram
  where
    lutProgram :: Program l -> G l m (Program l)
    lutProgram = programT

instance (IsLabel l, MonadTc m) => TransformExp (G l m) where
    expT (LutE _ e) = do
        info <- lutInfo e
        lutExp e info

    expT e =
        transExp e

instance (IsLabel l, MonadTc m) => TransformComp l (G l m) where
    declsT [] m = do
        x     <- m
        decls <- getTopDecls
        return (decls, x)

    declsT (d:ds) m = do
        (d', (ds1, ds2, x)) <-
            declT d $ do
            ds1      <- getTopDecls
            (ds2, x) <- declsT ds m
            return (ds1, ds2, x)
        return (ds1 ++ d':ds2, x)

lutExp :: forall l m . MonadTc m => Exp -> LUTInfo -> G l m Exp
lutExp e info = do
    traceLUT $ ppr e </> ppr info
    (v_lut, structdef) <- lookupLUT e >>= maybeMkLUT
    mkLUTLookup structdef v_lut
  where
    tau_res :: Type
    tau_res = unSTC (lutResultType info)

    resultVars :: [LUTVar]
    resultVars = lutResultVars info

    maybeMkLUT :: Maybe (Var, StructDef) -> G l m (Var, StructDef)
    maybeMkLUT Nothing = do
        structdef@(StructDef struct _taus flds _) <- mkStructDef
        appendTopDecl $ StructD struct [] flds noLoc
        extendStructs [structdef] $ do
          e'    <- lowerLUTVars (toList $ lutInVars info) e
          v_lut <- mkLUT structdef e'
          insertLUT e v_lut structdef
          return (v_lut, structdef)

    maybeMkLUT (Just (v_lut, structdef)) =
        return (v_lut, structdef)

    mkStructDef :: G l m StructDef
    mkStructDef = do
        struct <- gensym "lut_struct"
        fs     <- mapM (gensym . namedString) resultVars
        taus   <- map unRefT <$> mapM lookupLUTVar resultVars
        case lutResultVar info of
          Nothing | not (isUnitT tau_res) -> do
              f_res     <- gensym "result"
              let fs'   = fs ++ [f_res]
              let taus' = taus ++ [tau_res]
              return $ StructDef struct [] (fs' `zip` taus') noLoc
          _ ->
              return $ StructDef struct [] (fs `zip` taus) noLoc

    mkLUT :: StructDef -> Exp -> G l m Var
    mkLUT structdef@(StructDef struct _taus _flds _) e = do
        taus_in     <- mapM lookupLUTVar lvs_in
        bits        <- sum <$> mapM typeSize taus_in
        v_lut       <- gensym "lut"
        let tau_lut =  arrKnownT (2^bits) (structT struct)
        e'          <- packLUTElement info structdef e
        let gs      =  [mkGen lv tau | (lv, tau) <- lvs_in `zip` taus_in]
        -- We reverse the generators @gs@ here so that the first generator in
        -- @gs@ varies fastest because its values must make up the least
        -- significant bits of the LUT index.
        appendTopDecl $ LetD (letD v_lut tau_lut (genE e' (reverse gs))) noLoc
        return v_lut
      where
        lvs_in :: [LUTVar]
        lvs_in = toList $ lutInVars info

        mkGen :: LUTVar -> Type -> Gen
        mkGen lv tau
          | isRefT tau = genrefG (unLUTVar lv) (unRefT tau) (EnumC (unRefT tau))
          | otherwise  = genG (unLUTVar lv) tau (EnumC tau)

    mkLUTLookup :: StructDef -> Var -> G l m Exp
    mkLUTLookup (StructDef _struct _taus flds _) v_lut = do
        taus_in     <- mapM lookupLUTVar lvs_in
        w_in        <- sum <$> mapM typeSize taus_in
        v_idx       <- gensym "lutidx"
        let tau_idx =  FixT (U w_in) noLoc
        packLUTIdx (lvs_in `zip` taus_in) $ \e_bits -> do
          let e_idx   =  bitcastE tau_idx e_bits
          let e_lut   =  idxE (varE v_lut) (varE v_idx)
          let es_assn =  [assignE (toExp lv) (projE e_lut f) |
                           (lv, f) <- resultVars `zip` fs]
          e_result    <- mkResult e_lut (lutResultVar info) (lutResultType info)
          return $ letE v_idx tau_idx e_idx $ foldr seqE e_result es_assn
      where
        lvs_in :: [LUTVar]
        lvs_in = toList (lutInVars info)

        fs :: [Field]
        fs = map fst flds

        mkResult :: Exp -> Maybe Var -> Type -> G l m Exp
        mkResult _e_lut Nothing (ForallT _ (ST (C UnitT{}) _ _ _ _) _) =
            return $ returnE unitE

        mkResult _e_lut Nothing (ST (C UnitT{}) _ _ _ _) =
            return $ returnE unitE

        mkResult _e_lut Nothing UnitT{} =
            return unitE

        mkResult e_lut Nothing (ForallT _ ST{} _) =
            return $ returnE $ projE e_lut (last fs)

        mkResult e_lut Nothing ST{} =
            return $ returnE $ projE e_lut (last fs)

        mkResult e_lut Nothing _ =
            return $ projE e_lut (last fs)

        mkResult _ (Just v) tau = do
            tau_v <- lookupVar v
            case (isRefT tau_v, isPureT tau) of
              (True, _)     -> return $ derefE $ varE v
              (_,    True)  -> return $ returnE $ varE v
              (_,    False) -> return $ varE v

    lookupLUTVar :: LUTVar -> G l m Type
    lookupLUTVar (VarL v) =
        lookupVar v

    lookupLUTVar (IdxL v _ Nothing) = do
        tau           <- lookupVar v
        (_, tau_elem) <- checkArrOrRefArrT tau
        if isRefT tau
          then return $ refT tau_elem
          else return tau_elem

    lookupLUTVar (IdxL v _ (Just n)) = do
        tau           <- lookupVar v
        (_, tau_elem) <- checkArrOrRefArrT tau
        if isRefT tau
          then return $ refT $ arrKnownT n tau_elem
          else return $ arrKnownT n tau_elem

-- | Pack LUT variables into a LUT index. Note that the variables may have ref
-- type.
packLUTIdx :: forall m . MonadTc m
           => [(LUTVar, Type)]
           -> (Exp -> m Exp)
           -> m Exp
packLUTIdx = go []
  where
    go :: [Exp] -> [(LUTVar, Type)] -> (Exp -> m Exp) -> m Exp
    go es [] k =
      k $ foldr1 catE es

    go es ((lv,tau):lvtaus) k | isRefT tau = do
        v' <- gensym (namedString lv)
        w  <- typeSize tau
        bindE v' (unRefT tau) (derefE (toExp lv)) <$>
            go (bitcastE (arrKnownT w bitT) (varE v') : es) lvtaus k

    go es ((lv,tau):lvtaus) k = do
        w  <- typeSize tau
        go (bitcastE (arrKnownT w bitT) (toExp lv):es) lvtaus k

packLUTElement :: forall m . MonadTc m
               => LUTInfo
               -> StructDef
               -> Exp
               -> m Exp
packLUTElement info (StructDef struct _taus flds _) e =
    bindFreeOutVars $
      bindResult e $
      bindResultVars (reverse (resultVars `zip` taus))
  where
    fs :: [Field]
    taus :: [Type]
    (fs, taus) = unzip flds

    lvs_in, lvs_out :: [LUTVar]
    lvs_in  = toList $ lutInVars info
    lvs_out = toList $ lutOutVars info

    resultVars :: [LUTVar]
    resultVars = lutResultVars info

    tau_res :: Type
    tau_res = unSTC (lutResultType info)

    bindFreeOutVars :: m Exp -> m Exp
    bindFreeOutVars k = do
        taus <- mapM lookupVar vs
        go (vs `zip` taus)
      where
        go :: [(Var, Type)] -> m Exp
        go [] =
            k

        go ((v, tau):vtaus) | isRefT tau =
            letrefE v (unRefT tau) Nothing <$> go vtaus

        go ((v, tau):vtaus) = do
            c <- defaultValueC (unRefT tau)
            letE v tau (constE c) <$> go vtaus

        vs :: [Var]
        vs = map unLUTVar lvs_out \\ map unLUTVar lvs_in

    bindResult :: Exp -> ([Exp] -> m Exp) -> m Exp
    bindResult e k = do
        x        <- gensym "x"
        let vals =  case lutResultVar info of
                      Nothing -> [varE x]
                      Just _  -> []
        if isPureT (lutResultType info)
          then letE x tau_res e <$> k vals
          else bindE x tau_res e <$> k vals

    bindResultVars :: [(LUTVar, Type)] -> [Exp] -> m Exp
    bindResultVars [] vals | isPureT (lutResultType info) =
        return $ structE struct [] (fs `zip` vals)

    bindResultVars [] vals =
        return $ returnE $ structE struct [] (fs `zip` vals)

    bindResultVars ((lv,tau):vtaus) vals = do
        x <- gensym (namedString (unLUTVar lv))
        bindE x tau (derefE (toExp lv)) <$>
            bindResultVars vtaus (varE x:vals)

-- | Given a 'LUTInfo', calculate the set of result variables, of type 'LUTVar',
-- of the corresponding LUT. This widens the out 'LUTVar' that corresponds to
-- the result variable, if there is one.
lutResultVars :: LUTInfo -> [LUTVar]
lutResultVars info =
    case lutResultVar info of
      Nothing -> toList (lutOutVars info)
      Just v  -> go v (toList (lutOutVars info))
  where
    go :: Var -> [LUTVar] -> [LUTVar]
    go v []                          = [VarL v]
    go v lvs@(VarL v':_)   | v' == v = lvs
    go v (IdxL v' _ _:lvs) | v' == v = VarL v : lvs
    go v (lv:lvs)                    = lv : go v lvs

lutGenToExp :: forall m . MonadTc m
            => Var
            -> Exp
            -> [Gen]
            -> m Exp
lutGenToExp v_lut e gs =
    localConfig (unsetWarnFlag WarnBitArrayCopy) $ do
    unless (isLUTGen e gs) $
      faildoc $ text "Cannot convert non-LUT generator expression to expression"
    tau  <- checkGenerators gs $ \_ ->
            inferExp e
    bits <- sum <$> mapM typeSize taus
    mkFor 0 (2^bits) $ \i ->
        unpackLUTIdx i (reverse (vs `zip` taus)) $
        mkAssign (idxE (varE v_lut) i) e tau
  where
    vs :: [Var]
    taus :: [Type]
    (vs, taus) = unzip $ map unGen gs

    unGen :: Gen -> (Var, Type)
    unGen (GenG    v tau _ _) = (v, tau)
    unGen (GenRefG v tau _ _) = (v, refT tau)

    mkFor :: Int -> Int -> (Exp -> m Exp) -> m Exp
    mkFor from to k = do
        i <- gensym "i"
        forE AutoUnroll i uintT (uintE from) (uintE to) <$> k (varE i)

    mkAssign :: Exp -> Exp -> Type -> m Exp
    mkAssign e_lhs e_rhs tau | isPureT tau =
        return $ assignE e_lhs e_rhs

    mkAssign e_lhs e_rhs tau = do
        x <- gensym "x"
        return $ bindE x (unSTC tau) e_rhs $
                 assignE e_lhs (varE x)

isLUTGen :: Exp -> [Gen] -> Bool
isLUTGen _ = all isEnumGen
  where
    isEnumGen :: Gen -> Bool
    isEnumGen (GenG    _ _ EnumC{} _) = True
    isEnumGen (GenRefG _ _ EnumC{} _) = True
    isEnumGen _                       = False

-- | Unpack LUT variables from a LUT index.
unpackLUTIdx :: forall m . MonadTc m
             => Exp           -- ^ The LUT index
             -> [(Var, Type)] -- ^ The variables to unpack, from least
                              -- significant bits to most significant bits.
             -> m Exp         -- ^ The body over which unpacked variables scope.
             -> m Exp
unpackLUTIdx = go 0
  where
    go :: Int -> Exp -> [(Var, Type)] -> m Exp -> m Exp
    go _ _ [] k =
        k

    go shift e_bits ((v, tau):vtaus) k = do
        n     <- typeSize tau
        let e =  bitcastE (unRefT tau) (extractBits e_bits shift n)
        mkLet v tau e <$> go (shift+n) e_bits vtaus k
      where
        extractBits :: Exp -> Int -> Int -> Exp
        extractBits bits shift n =
            (bits `shiftR'` uintE shift) ..&.. uintE mask
          where
            mask :: Int
            mask = (1 `shiftL` n) - 1

        mkLet :: Var -> Type -> Exp -> Exp -> Exp
        mkLet v tau e1 e2
          | isRefT tau = letrefE v (unRefT tau) (Just e1) e2
          | otherwise  = letE v tau e1 e2

type LEnv = Map Var LUTVar

newtype L m a = L { unL :: ReaderT LEnv m a }
  deriving (Applicative, Functor, Monad, MonadIO,
            MonadReader LEnv,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadConfig,
            MonadTrace,
            MonadTc)

instance MonadTrans L where
    lift = L . lift

runL :: LEnv -> L m a -> m a
runL env m = runReaderT (unL m) env

lookupLUTVar :: MonadTc m => Var -> L m (Maybe LUTVar)
lookupLUTVar v = asks (Map.lookup v)

lowerLUTVars :: MonadTc m
             => [LUTVar]
             -> Exp
             -> m Exp
lowerLUTVars lvs e = do
    -- We lower views here so we don't have to deal with them ocurring *inside*
    -- a LUTted expression. In fact, this re-indexing transformation can't deal
    -- with views at all!
    --
    -- Why not ditch views entirely before we even reach this pass? Because
    -- LutToGen needs the views that are *free* in a LUTted expression so that
    -- it can accurately determine the width of the LUT's input/output
    -- variables!
    e' <- lowerExpViews e
    runL env $ expT e'
  where
    env :: LEnv
    env = Map.fromList [(unLUTVar lv, lv) | lv <- lvs]

instance MonadTc m => TransformExp (L m) where
    expT e@(IdxE (VarE v _) e_i maybe_len _) =
        lookupLUTVar v >>= go
      where
        go :: Maybe LUTVar -> L m Exp
        go (Just (IdxL _ _ Nothing)) =
            return $ varE v

        go (Just (IdxL _ off _)) | Just e_len <- maybe_len =
            return $ sliceE (varE v) (e_i - uintE off) e_len

        go (Just (IdxL _ off _)) =
            return $ idxE (varE v) (e_i - uintE off)

        go _ =
            return e

    expT e =
        transExp e
