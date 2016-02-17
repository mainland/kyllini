-- |
-- Module      :  Opts
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cdrexel.edu

module Opts (
    compilerOpts,
    usage
  ) where

import Control.Monad (when)
import System.Console.GetOpt
import System.Environment (getProgName)
import Data.Monoid

import KZC.Flags
import KZC.Globals

options :: [OptDescr (Flags -> Flags)]
options =
    map mkModeFlag modeFlagOpts ++
    otherOpts ++
    map (mkOptFlag "W" "" setWarnFlag) wWarnFlagOpts ++
    concatMap (mkSetOptFlag "f" "" setDynFlag unsetDynFlag) fDynFlagOpts ++
    map (mkOptFlag "d" "" setDynFlag) dDynFlagOpts ++
    map (mkOptFlag "d" "dump-" setDumpFlag) dDumpFlagOpts ++
    map (mkOptFlag "d" "trace-" setTraceFlag) dTraceFlagOpts
  where
    otherOpts :: [OptDescr (Flags -> Flags)]
    otherOpts =
        [ Option ['q'] ["quiet"]      (NoArg (setDynFlag Quiet))          "be quiet"
        , Option ['v'] ["verbose"]    (OptArg maybeSetVerbLevel "LEVEL")  "be verbose"
        , Option ['P'] []             (NoArg (setDynFlag StopAfterParse)) "stop after parsing"
        , Option ['C'] []             (NoArg (setDynFlag StopAfterCheck)) "stop after type checking"
        , Option ['I'] []             (ReqArg includePathOpt "DIR")       "include DIR"
        , Option ['D'] []             (ReqArg defineOpt "macro[=defn]")   "define macro"
        , Option ['o'] ["output"]     (ReqArg outOpt "FILE")              "output FILE"
        , Option []    ["ferrctx"]    (ReqArg maxErrCtxOpt "INT")         "set maximum error context"
        , Option [] ["fmax-simplifier-iterations"]
            (ReqArg maxSimplIterationsOpt "INT")
            "set maximum simplification iterations"
        ]

    maybeSetVerbLevel :: Maybe String -> Flags -> Flags
    maybeSetVerbLevel Nothing fs =
        fs { verbLevel = verbLevel fs + 1 }

    maybeSetVerbLevel (Just s) fs =
        case reads s of
          [(n, "")]  -> fs { verbLevel = n }
          _          -> error "argument to --verbose must be an integer"

    maxErrCtxOpt :: String -> Flags -> Flags
    maxErrCtxOpt s fs =
        case reads s of
          [(n, "")]  -> fs { maxErrCtx = n }
          _          -> error "argument to --ferrctx must be an integer"

    maxSimplIterationsOpt :: String -> Flags -> Flags
    maxSimplIterationsOpt s fs =
        case reads s of
          [(n, "")]  -> fs { maxSimpl = n }
          _          -> error "argument to --fmax-simplifier-iterations must be an integer"

    outOpt :: String -> Flags -> Flags
    outOpt path fs = fs { output = Just path }

    includePathOpt :: String -> Flags -> Flags
    includePathOpt path fs = fs { includePaths = includePaths fs ++ [path] }

    defineOpt :: String -> Flags -> Flags
    defineOpt def fs = fs { defines = defines fs ++ [split (/= '=') def] }

    split :: (a -> Bool) -> [a] -> ([a], [a])
    split p s = case split p s of
                  (xs, []) -> (xs, [])
                  (xs, ys) -> (xs, drop 1 ys)

mkModeFlag :: (ModeFlag, [Char], [String], String)
           -> OptDescr (Flags -> Flags)
mkModeFlag (f, so, lo, desc) =
    Option so lo (NoArg set) desc
  where
    set fs = fs { mode = f }

mkOptFlag :: String
          -> String
          -> (f -> Flags -> Flags)
          -> (f, String, String)
          -> OptDescr (Flags -> Flags)
mkOptFlag pfx mfx set (f, str, desc) =
    Option  [] [pfx ++ mfx ++ str] (NoArg (set f)) desc

mkSetOptFlag :: String
             -> String
             -> (f -> Flags -> Flags)
             -> (f -> Flags -> Flags)
             -> (f, String, String)
             -> [OptDescr (Flags -> Flags)]
mkSetOptFlag pfx mfx set unset (f, str, desc) =
    [  Option  [] [pfx ++          mfx ++ str] (NoArg (set f)) desc
    ,  Option  [] [pfx ++ "no"  ++ mfx ++ str] (NoArg (unset f)) ("don't " ++ desc)
    ,  Option  [] [pfx ++ "no-" ++ mfx ++ str] (NoArg (unset f)) ("don't " ++ desc)
    ]

modeFlagOpts :: [(ModeFlag, [Char], [String], String)]
modeFlagOpts =
  [ (Help,    ['h', '?'], ["--help"], "show help")
  , (Compile, ['c'],      [],         "compile")
  ]

fDynFlagOpts :: [(DynFlag, String, String)]
fDynFlagOpts =
  [ (PrettyPrint, "pprint",       "pretty-print file")
  , (LinePragmas, "line-pragmas", "print line pragmas in generated C")
  , (Fuse,        "fuse",         "run the par fuser")
  , (Simplify,    "simpl",        "run the simplifier")
  , (MayInline,   "inline",       "inline when simplifying")
  , (BoundsCheck, "bounds-check", "generate bounds checks")
  , (PartialEval, "peval",        "run the partial evaluator")
  ]

dDynFlagOpts :: [(DynFlag, String, String)]
dDynFlagOpts =
  [ (Lint,          "lint",
                    "lint core")
  , (AutoLint,      "auto-lint",
                    "lint auto")
  , (PrintUniques,  "print-uniques",
                    "show uniques when pretty-printing")
  , (ExpertTypes,   "expert-types",
                    "show \"expert\" types when pretty-printing")
  ]

dDumpFlagOpts :: [(DumpFlag, String, String)]
dDumpFlagOpts =
  [ (DumpCPP,     "cpp",     "dump CPP output")
  , (DumpRename,  "rn",      "dump renamer output")
  , (DumpLift,    "lift",    "dump lambda lifter output")
  , (DumpFusion,  "fusion",  "dump fusion output")
  , (DumpCore,    "core",    "dump core")
  , (DumpAuto,    "auto",    "dump automata")
  , (DumpOcc,     "occ",     "dump occurrence info")
  , (DumpSimpl,   "simpl",   "dump simplifier output")
  , (DumpEval,    "peval",   "dump partial evaluator output")
  ]

dTraceFlagOpts :: [(TraceFlag, String, String)]
dTraceFlagOpts =
  [ (TraceLexer,    "lex",       "trace lexer")
  , (TraceParser,   "parse",     "trace parser")
  , (TraceRn,       "rn",        "trace renamer")
  , (TraceLift,     "lift",      "trace lambda lifter")
  , (TraceTc,       "tc",        "trace type checker")
  , (TraceCg,       "cg",        "trace code generation")
  , (TraceLint,     "lint",      "trace linter")
  , (TraceAuto,     "auto",      "trace auto")
  , (TraceAutoLint, "auto-lint", "trace auto linter")
  , (TraceFusion,   "fusion",    "trace fusion")
  , (TraceSimplify, "simpl",     "trace simplifier")
  , (TraceEval,     "eval",      "trace evaluator")
  ]

wWarnFlagOpts :: [(WarnFlag, String, String)]
wWarnFlagOpts =
  [ (WarnError, "error", "make warnings errors")
  ]

compilerOpts :: [String] -> IO (Flags, [String])
compilerOpts argv = do
    case getOpt Permute options argv of
      (fs,n,[] ) -> do let fs' = foldr ($) mempty fs
                       setMaxErrContext (maxErrCtx fs')
                       when (testDynFlag PrintUniques fs') $
                           setPrintUniques True
                       when (testDynFlag ExpertTypes fs') $
                           setExpertTypes True
                       return (fs', n)
      (_,_,errs) -> do usageDesc <- usage
                       ioError (userError (concat errs ++ usageDesc))

usage :: IO String
usage = do
    progname   <- getProgName
    let header =  "Usage: " ++ progname ++ " [OPTION...] files..."
    return $ usageInfo header options
