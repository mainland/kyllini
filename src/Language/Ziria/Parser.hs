{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      : Language.Ziria.Parser
-- Copyright   : (c) 2015-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>
--
--------------------------------------------------------------------------------

module Language.Ziria.Parser (
    dialectExts,
    moduleDialect,

    parseProgram,
    parseImports,
    parseProgramFromFile,
    parseImportsFromFile
  ) where

import Control.Monad.Exception
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Control.Monad.Trans
import qualified Data.ByteString.Lazy as B
import Data.Loc
import Data.Set (Set)
import Data.Symbol
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E
import System.FilePath
import Text.PrettyPrint.Mainland

import KZC.Globals
import KZC.Monad
import KZC.Util.Pretty
import KZC.Util.SysTools

import qualified Language.Ziria.Parser.Classic as Classic
import qualified Language.Ziria.Parser.Kyllini as Kyllini
import qualified Language.Ziria.Parser.LenientClassic as LenientClassic
import Language.Ziria.Parser.Monad
import Language.Ziria.Syntax

dialectExts :: [(String, Dialect)]
dialectExts = [ (".wpl", Classic)
              , (".blk", Classic)
              , (".kz",  Kyllini)
              ]

moduleDialect :: forall m . MonadFail m => FilePath -> m Dialect
moduleDialect filepath =
    go dialectExts
  where
    ext :: String
    ext = takeExtension filepath

    go :: [(String, Dialect)] -> m Dialect
    go [] = faildoc $ text "Unknown dialect" <+> enquote (text ext)

    go ((ext', dialect):dialects)
      | ext' == ext = return dialect
      | otherwise   = go dialects

parse :: Dialect
      -> P a
      -> T.Text
      -> Pos
      -> Either SomeException a
parse d p buf pos =
    evalP p (emptyPState d buf pos)

parseFromFile :: Dialect
              -> P a
              -> FilePath
              -> KZC a
parseFromFile d p filepath = do
    text  <- liftIO $ E.decodeUtf8 <$> B.readFile filepath
    text' <- runCpp filepath text
    liftException (parse d p text' start)
  where
    start :: Pos
    start = startPos filepath

parseProgram :: Dialect
             -> T.Text
             -> Pos
             -> IO Program
parseProgram dialect buf pos =
    liftException $ parse dialect (chooseParser dialect) buf pos
  where
    chooseParser :: Dialect -> P Program
    chooseParser Classic | strictClassic = Classic.parseProgram
                         | otherwise     = LenientClassic.parseProgram
    chooseParser Kyllini                 = Kyllini.parseProgram

parseImports :: Dialect
             -> T.Text
             -> Pos
             -> IO [Import]
parseImports dialect buf pos =
    liftException $ parse dialect (chooseParser dialect) buf pos
  where
    chooseParser :: Dialect -> P [Import]
    chooseParser Classic | strictClassic = Classic.parseImports
                         | otherwise     = LenientClassic.parseImports
    chooseParser Kyllini                 = Kyllini.parseImports

parseProgramFromFile :: Set Symbol -> FilePath -> KZC Program
parseProgramFromFile structIds filepath = do
    dialect <- moduleDialect filepath
    parseFromFile dialect (addStructIdentifiers structIds >> chooseParser dialect) filepath
  where
    chooseParser :: Dialect -> P Program
    chooseParser Classic | strictClassic = Classic.parseProgram
                         | otherwise     = LenientClassic.parseProgram
    chooseParser Kyllini                 = Kyllini.parseProgram

parseImportsFromFile :: FilePath -> KZC [Import]
parseImportsFromFile filepath = do
    dialect <- moduleDialect filepath
    parseFromFile dialect (chooseParser dialect) filepath
  where
    chooseParser :: Dialect -> P [Import]
    chooseParser Classic | strictClassic = Classic.parseImports
                         | otherwise     = LenientClassic.parseImports
    chooseParser Kyllini                 = Kyllini.parseImports
