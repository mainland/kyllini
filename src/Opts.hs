module Opts where

import System.Console.GetOpt
import System.Environment (getProgName)
import Data.Monoid

import KZC.Flags

options :: [OptDescr Flags]
options =
    [ Option ['p'] ["pprint"]         (NoArg pprintArg)        "pretty-print file"
    , Option []    ["check"]          (NoArg checkArg)        "type-check file"
    , Option []    ["lint-core"]      (NoArg lintArg)         "lint core"
    , Option []    ["Werror"]         (NoArg warnErrorArg)    "make warnings errors"
    , Option []    ["trace-tc"]       (NoArg traceTcArg)      "trace the type checker"
    , Option []    ["trace-lint"]     (NoArg traceLintArg)    "trace the linter"
    , Option []    ["dump-tc"]        (NoArg dumpTcArg)       "dump output of the type checker"
    , Option ['o'] ["output"]         (OptArg outArg "FILE")  "output FILE"
    ]
  where
    pprintArg :: Flags
    pprintArg = mempty { pprintF = True }

    checkArg :: Flags
    checkArg = mempty { checkF = True }

    lintArg :: Flags
    lintArg = mempty { lintF = True }

    warnErrorArg :: Flags
    warnErrorArg = mempty { warnErrorF = True }

    traceTcArg :: Flags
    traceTcArg = mempty { traceTcF = True }

    traceLintArg :: Flags
    traceLintArg = mempty { traceLintF = True }

    dumpTcArg :: Flags
    dumpTcArg = mempty { dumpTcF = True }

    outArg :: Maybe String -> Flags
    outArg f = mempty { outputF = f }

compilerOpts :: [String] -> IO (Flags, [String])
compilerOpts argv = do
    progname <- getProgName
    let header = "Usage: " ++ progname ++ " [OPTION...] files..."
    case getOpt Permute options argv of
      (fs,n,[] ) -> return (mconcat fs, n)
      (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
