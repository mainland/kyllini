--------------------------------------------------------------------------------
-- |
-- Module      : Language.Ziria.Parser
-- Copyright   : (c) 2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>
--
--------------------------------------------------------------------------------

module Language.Ziria.Parser (
    parseProgram,
    parseProgramFromFile
  ) where

import Control.Monad.Exception
import Control.Monad.Trans
import qualified Data.ByteString.Lazy as B
import Data.Loc
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E

import qualified Language.Ziria.Parser.Parser as P
import Language.Ziria.Parser.Monad
import Language.Ziria.Syntax

parse :: P a
      -> T.Text
      -> Pos
      -> Either SomeException a
parse p buf pos =
    evalP p (emptyPState buf pos)

parseFromFile :: P a
              -> FilePath
              -> IO a
parseFromFile p path = do
    text <- liftIO $ B.readFile path
    liftException (parse p (E.decodeUtf8 text) start)
  where
    start :: Pos
    start = startPos path

parseProgram :: T.Text
             -> Pos
             -> IO [CompLet]
parseProgram buf pos = liftException $ parse P.parseProgram buf pos

parseProgramFromFile :: FilePath -> IO [CompLet]
parseProgramFromFile = parseFromFile P.parseProgram
