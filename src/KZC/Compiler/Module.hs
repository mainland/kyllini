{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Compiler.Module
-- Copyright   :  (c) 2016-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Compiler.Module (
    locateModuleSource,
    lookupModuleInfo,
    loadModuleInfo,
    updateModuleInfo,

    summarizeSourceFile,
    moduleDepSCCs,
    modulesDepSCCs
  ) where

import Control.Monad.IO.Class (MonadIO(..),
                               liftIO)
import Control.Monad.Reader (asks)
import Control.Monad.Ref (modifyRef,
                          readRef)
import Data.List (foldl')
import Data.Loc (locOf)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Symbol
import System.Directory (doesFileExist)
import System.FilePath (FilePath,
                        addExtension,
                        joinPath)
import Text.PrettyPrint.Mainland

import Data.Digraph
import KZC.Compiler.Types
import KZC.Config
import KZC.Name
import KZC.Monad
import KZC.Util.Error
import KZC.Util.Pretty

import qualified Language.Ziria.Parser as P
import qualified Language.Ziria.Syntax as Z

locateModuleSource :: forall m . (MonadConfig m, MonadErr m, MonadIO m)
                   => ModuleName
                   -> m FilePath
locateModuleSource mod =
    withLocContext (locOf mod) (text "Import of" <+> enquote (ppr mod)) $ do
    paths        <- asksConfig importPaths
    maybe_module <- searchPaths paths
    case maybe_module of
      Nothing  -> faildoc $ text "Cannot find module" <+> enquote (ppr mod)
      Just mod -> return mod
  where
    searchPaths :: [FilePath] -> m (Maybe FilePath)
    searchPaths [] =
        return Nothing

    searchPaths (path:paths) = do
        maybe_file <- searchExts path P.dialectExts
        case maybe_file of
          Nothing   -> searchPaths paths
          Just file -> return $ Just file

    searchExts :: FilePath -> [(String, Z.Dialect)] -> m (Maybe FilePath)
    searchExts _path [] =
        return Nothing

    searchExts path ((ext, _dialect):exts) = do
        exists <- liftIO $ doesFileExist filepath
        if exists
          then return $ Just filepath
          else searchExts path exts
      where
        filepath :: FilePath
        filepath = joinPath [path, addExtension (moduleToFilePath mod) ext]

moduleToFilePath :: ModuleName -> FilePath
moduleToFilePath m = joinPath (map unintern (modSyms m))

lookupModuleInfo :: ModuleName -> KZC ModuleInfo
lookupModuleInfo modname = do
    ref         <- asks modref
    maybe_info  <- Map.lookup modname <$> readRef ref
    case maybe_info of
      Just info  ->  return info
      Nothing    ->  loadModuleInfo modname

loadModuleInfo :: ModuleName -> KZC ModuleInfo
loadModuleInfo modname = do
    path    <- locateModuleSource modname
    modinfo <- summarizeSourceFile path
    updateModuleInfo modname modinfo
    return modinfo

summarizeSourceFile :: FilePath -> KZC ModuleInfo
summarizeSourceFile sourcePath = do
    imports <- P.parseImportsFromFile sourcePath
    return ModuleInfo { modSourcePath = sourcePath
                      , modImports    = [modname | Z.Import modname <- imports]
                      }

updateModuleInfo :: ModuleName -> ModuleInfo -> KZC ()
updateModuleInfo modname modinfo = do
    ref <- asks modref
    modifyRef ref $ Map.insert modname modinfo

moduleDepSCCs :: ModuleName -> KZC [Set ModuleInfo]
moduleDepSCCs modname = do
    modinfo <- lookupModuleInfo modname
    modulesDepSCCs [modinfo]

modulesDepSCCs :: [ModuleInfo] -> KZC [Set ModuleInfo]
modulesDepSCCs modinfos =
    go Set.empty (Set.fromList modinfos) Map.empty Map.empty
  where
    go  ::  Set ModuleInfo
        ->  Set ModuleInfo
        ->  Map ModuleInfo [ModuleInfo]
        ->  Map ModuleInfo [ModuleInfo]
        ->  KZC [Set ModuleInfo]
    go visited unvisited ins outs | Set.null unvisited =
        return $ scc  (\mod -> Map.findWithDefault [] mod ins)
                      (\mod -> Map.findWithDefault [] mod outs)
                      (Set.elems visited)

    go visited unvisited ins outs = do
        deps             <-  mapM lookupModuleInfo (modImports modinfo)
        let ins'         =   foldl' addEdge ins   [(dep, modinfo) | dep <- deps]
        let outs'        =   foldl' addEdge outs  [(modinfo, dep) | dep <- deps]
        let visited'     =   Set.insert modinfo visited
        let unvisited''  =   foldl' (flip Set.insert) unvisited'
                             [dep |  dep <- deps,
                                     dep `Set.notMember` visited]
        go visited' unvisited'' ins' outs'
      where
        (modinfo, unvisited') = Set.deleteFindMin unvisited

    addEdge :: Ord a => Map a [a] -> (a, a) -> Map a [a]
    addEdge m (e1, e2) = Map.insert e1 (e2 : Map.findWithDefault [] e1 m) m
