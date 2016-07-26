{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Optimize.LutToGen
-- Copyright   :  (c) 2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Optimize.LutToGen (
    lutToGen
  ) where

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
import Data.Foldable (toList)
import Data.List ((\\))
import Data.Loc (noLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence ((|>),
                      Seq)
import Text.PrettyPrint.Mainland

import KZC.Analysis.Lut
import KZC.Core.Lint
import KZC.Core.Smart
import KZC.Core.Syntax
import KZC.Core.Transform
import KZC.Error
import KZC.Flags
import KZC.Label
import KZC.Name
import KZC.Trace
import KZC.Uniq

data GState l = GState { topDecls :: !(Seq (Decl l)) }

defaultGState :: GState l
defaultGState = GState mempty

newtype G l m a = G { unG :: StateT (GState l) m a }
  deriving (Applicative, Functor, Monad, MonadIO,
            MonadState (GState l),
            MonadException,
            MonadUnique,
            MonadErr,
            MonadFlags,
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
    structdef@(StructDef struct flds _) <- mkStructDef
    appendTopDecl $ LetStructD struct flds noLoc
    extendStructs [structdef] $ do
    e'  <- lowerLUTVars (toList $ lutInVars info) e
    lut <- mkLUT structdef e'
    mkLUTLookup structdef lut
  where
    tau_res :: Type
    tau_res = unSTC (lutResultType info)

    resultVars :: [LUTVar]
    resultVars = lutResultVars info

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
              return $ StructDef struct (fs' `zip` taus') noLoc
          _ ->
              return $ StructDef struct (fs `zip` taus) noLoc

    mkLUT :: StructDef -> Exp -> G l m Var
    mkLUT structdef@(StructDef struct _ _) e = do
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
    mkLUTLookup (StructDef _struct flds _) v_lut = do
        taus_in     <- mapM lookupLUTVar lvs_in
        w_in        <- sum <$> mapM typeSize taus_in
        v_idx       <- gensym "lutidx"
        let tau_idx =  FixT I U (W w_in) (BP 0) noLoc
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
        mkResult _e_lut Nothing (ST _ (C UnitT{}) _ _ _ _) =
            return $ returnE unitE

        mkResult _e_lut Nothing UnitT{} =
            return unitE

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
        (_, tau) <- lookupVar v >>= checkArrOrRefArrT
        return tau

    lookupLUTVar (IdxL v _ (Just n)) = do
        (_, tau) <- lookupVar v >>= checkArrOrRefArrT
        return $ arrKnownT n tau

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
packLUTElement info (StructDef struct flds _) e =
    bindFreeOutVars $
      bindResult e $
      bindResultVars (reverse (map unLUTVar resultVars `zip` taus))
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

    bindResultVars :: [(Var, Type)] -> [Exp] -> m Exp
    bindResultVars [] vals | isPureT (lutResultType info) =
        return $ structE struct (fs `zip` vals)

    bindResultVars [] vals =
        return $ returnE $ structE struct (fs `zip` vals)

    bindResultVars ((v,tau):vtaus) vals = do
        x <- gensym (namedString v)
        bindE x tau (derefE (varE v)) <$>
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

type LEnv = Map Var LUTVar

newtype L m a = L { unL :: ReaderT LEnv m a }
  deriving (Applicative, Functor, Monad, MonadIO,
            MonadReader LEnv,
            MonadException,
            MonadUnique,
            MonadErr,
            MonadFlags,
            MonadTrace,
            MonadTc)

instance MonadTrans L where
    lift = L . lift

runL :: MonadTc m => LEnv -> L m a -> m a
runL env m = runReaderT (unL m) env

lookupLUTVar :: MonadTc m => Var -> L m (Maybe LUTVar)
lookupLUTVar v = asks (Map.lookup v)

lowerLUTVars :: MonadTc m
             => [LUTVar]
             -> Exp
             -> m Exp
lowerLUTVars lvs e =
    runL env $ expT e
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
            return $ sliceE (varE v) (e_i - fromIntegral off) e_len

        go (Just (IdxL _ off _)) =
            return $ idxE (varE v) (e_i - fromIntegral off)

        go _ =
            return e

    expT e =
        transExp e
