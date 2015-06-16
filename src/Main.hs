module Main where

import Control.Monad
import System.Environment

import Language.Core.Syntax ()
import Language.Ziria.Syntax ()
import Language.Ziria.Parser

main :: IO ()
main = do
  args <- getArgs
  forM_ args $ \path -> parseProgramFromFile path
