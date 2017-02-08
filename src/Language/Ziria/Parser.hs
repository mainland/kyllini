--------------------------------------------------------------------------------
-- |
-- Module      : Language.Ziria.Parser
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

module Language.Ziria.Parser (
    Dialect(..),
    dialectExts,

    parseProgram,
    parseImports,
    parseProgramFromFile,
    parseImportsFromFile
  ) where

import Control.Monad.Exception
import Control.Monad.Trans
import qualified Data.ByteString.Lazy as B
import Data.Loc
import Data.Set (Set)
import Data.Symbol
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E

import KZC.Monad
import KZC.Util.SysTools

import qualified Language.Ziria.Parser.Classic as Classic
import Language.Ziria.Parser.Monad
import Language.Ziria.Syntax

data Dialect = Classic
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

dialectExts :: [(String, Dialect)]
dialectExts = [ (".wpl", Classic)
              , (".blk", Classic)
              ]

parse :: P a
      -> T.Text
      -> Pos
      -> Either SomeException a
parse p buf pos =
    evalP p (emptyPState buf pos)

parseFromFile :: P a
              -> FilePath
              -> KZC a
parseFromFile p filepath = do
    text  <- liftIO $ E.decodeUtf8 <$> B.readFile filepath
    text' <- runCpp filepath text
    liftException (parse p text' start)
  where
    start :: Pos
    start = startPos filepath

parseProgram :: T.Text
             -> Pos
             -> IO Program
parseProgram buf pos = liftException $ parse Classic.parseProgram buf pos

parseImports :: T.Text
             -> Pos
             -> IO [Import]
parseImports buf pos = liftException $ parse Classic.parseImports buf pos

parseProgramFromFile :: Set Symbol -> FilePath -> KZC Program
parseProgramFromFile structIds =
    parseFromFile $ do
        addStructIdentifiers structIds
        Classic.parseProgram

parseImportsFromFile :: FilePath -> KZC [Import]
parseImportsFromFile = parseFromFile Classic.parseImports
