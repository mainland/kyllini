{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  Opts
-- Copyright   :  (c) 2015-2016 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cdrexel.edu

module Opts (
    compilerOpts,
    usage
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif /* !MIN_VERSION_base(4,8,0) */
import Control.Monad ((>=>),
                      when)
import Data.List (foldl')
import System.Console.GetOpt
import System.Environment (getProgName)

import KZC.Flags
import KZC.Globals

options :: forall m . Monad m => [OptDescr (Flags -> m Flags)]
options =
    map mkModeFlag modeFlagOpts ++
    otherOpts ++
    map (mkOptFlag "W" "" setWarnFlag) wWarnFlagOpts ++
    concatMap (mkSetOptFlag "f" "" setWarnFlag unsetWarnFlag) fWarnFlagOpts ++
    concatMap (mkSetOptFlag "f" "" setDynFlag  unsetDynFlag)  fDynFlagOpts ++
    map (mkOptFlag "d" "" setDynFlag) dDynFlagOpts ++
    map (mkOptFlag "d" "dump-" setDumpFlag) dDumpFlagOpts ++
    map (mkOptFlag "d" "trace-" setTraceFlag) dTraceFlagOpts
  where
    otherOpts :: [OptDescr (Flags -> m Flags)]
    otherOpts =
        [ Option ['q'] ["quiet"]      (NoArg (setDynFlagM Quiet))          "be quiet"
        , Option ['v'] ["verbose"]    (OptArg maybeSetVerbLevel "LEVEL")   "be verbose"
        , Option ['P'] []             (NoArg (setDynFlagM StopAfterParse)) "stop after parsing"
        , Option ['C'] []             (NoArg (setDynFlagM StopAfterCheck)) "stop after type checking"
        , Option ['I'] []             (ReqArg includePathOpt "DIR")        "include DIR"
        , Option ['D'] []             (ReqArg defineOpt "macro[=defn]")    "define macro"
        , Option ['o'] ["output"]     (ReqArg outOpt "FILE")               "output FILE"
        , Option []    ["ddump-all"]  (NoArg dumpAll)                      "dump all output"
        , Option []    ["ferrctx"]    (ReqArg maxErrCtxOpt "INT")          "set maximum error context"
        , Option [] ["fmax-simplifier-iterations"]
            (ReqArg maxSimplIterationsOpt "INT")
            "set maximum simplification iterations"
        , Option [] ["fmax-lut"]
            (ReqArg maxLUTOpt "SIZE")
            "set maximum LUT size in bytes"
        , Option [] ["fmin-lut-ops"]
            (ReqArg minLUTOpsOpt "N")
            "set minimum operation count to consider a LUT"
        ]

    setDynFlagM :: DynFlag -> Flags -> m Flags
    setDynFlagM f fs = return $ setDynFlag f fs

    maybeSetVerbLevel :: Maybe String -> Flags -> m Flags
    maybeSetVerbLevel Nothing fs =
        return fs { verbLevel = verbLevel fs + 1 }

    maybeSetVerbLevel (Just s) fs =
        case reads s of
          [(n, "")]  -> return fs { verbLevel = n }
          _          -> fail "argument to --verbose must be an integer"

    maxErrCtxOpt :: String -> Flags -> m Flags
    maxErrCtxOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxErrCtx = n }
          _          -> fail "argument to --ferrctx must be an integer"

    maxSimplIterationsOpt :: String -> Flags -> m Flags
    maxSimplIterationsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxSimpl = n }
          _          -> fail "argument to --fmax-simplifier-iterations must be an integer"

    dumpAll :: Flags -> m Flags
    dumpAll fs =
        return $ foldl' (flip setDumpFlag) fs [minBound..maxBound]

    maxLUTOpt :: String -> Flags -> m Flags
    maxLUTOpt s fs =
        case reads s of
          (n, "")  : _ -> return fs { maxLUT = n }
          (n, "k") : _ -> return fs { maxLUT = (n*1024) }
          (n, "K") : _ -> return fs { maxLUT = (n*1024) }
          (n, "m") : _ -> return fs { maxLUT = (n*1024*1024) }
          (n, "M") : _ -> return fs { maxLUT = (n*1024*1024) }
          _            -> fail $ "bad argument to --fmax-lut option: " ++ s

    minLUTOpsOpt :: String -> Flags -> m Flags
    minLUTOpsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { minLUTOps = n }
          _          -> fail "argument to --fmin-lut-ops must be an integer"

    outOpt :: String -> Flags -> m Flags
    outOpt path fs = return fs { output = Just path }

    includePathOpt :: String -> Flags -> m Flags
    includePathOpt path fs = return fs { includePaths = includePaths fs ++ [path] }

    defineOpt :: String -> Flags -> m Flags
    defineOpt def fs = return fs { defines = defines fs ++ [splitOn '=' def] }

splitOn :: Eq a => a -> [a] -> ([a], [a])
splitOn x s = case span (not . (== x)) s of
              (xs, []) -> (xs, [])
              (xs, ys) -> (xs, drop 1 ys)

mkModeFlag :: Monad m
           => (ModeFlag, [Char], [String], String)
           -> OptDescr (Flags -> m Flags)
mkModeFlag (f, so, lo, desc) =
    Option so lo (NoArg set) desc
  where
    set fs = return fs { mode = f }

mkOptFlag :: Monad m
          => String
          -> String
          -> (f -> Flags -> Flags)
          -> (f, String, String)
          -> OptDescr (Flags -> m Flags)
mkOptFlag pfx mfx set (f, str, desc) =
    Option  [] [pfx ++ mfx ++ str] (NoArg (return . set f)) desc

mkSetOptFlag :: Monad m
             => String
             -> String
             -> (f -> Flags -> Flags)
             -> (f -> Flags -> Flags)
             -> (f, String, String)
             -> [OptDescr (Flags -> m Flags)]
mkSetOptFlag pfx mfx set unset (f, str, desc) =
    [  Option  [] [pfx ++          mfx ++ str] (NoArg (return . set f)) desc
    ,  Option  [] [pfx ++ "no"  ++ mfx ++ str] (NoArg (return . unset f)) ("don't " ++ desc)
    ,  Option  [] [pfx ++ "no-" ++ mfx ++ str] (NoArg (return . unset f)) ("don't " ++ desc)
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
  , (Timers,      "timers",       "insert code to track elapsed time")
  , (AutoLUT,     "autolut",      "run the auto-LUTter")
  , (LUT,         "lut",          "run the LUTter")
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
  , (DumpAutoLUT, "autolut", "dump auto-LUTter")
  , (DumpLUT,     "lut",     "dump LUTter")
  ]

dTraceFlagOpts :: [(TraceFlag, String, String)]
dTraceFlagOpts =
  [ (TracePhase,    "phase",     "trace compiler phase")
  , (TraceLexer,    "lex",       "trace lexer")
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
  , (TraceAutoLUT,  "autolut",   "trace auto-LUTter")
  , (TraceLUT,      "lut",       "trace LUTter")
  ]

wWarnFlagOpts :: [(WarnFlag, String, String)]
wWarnFlagOpts =
  [ (WarnError, "error", "make warnings errors")
  ]

fWarnFlagOpts :: [(WarnFlag, String, String)]
fWarnFlagOpts =
  [ (WarnUnusedCommandBind, "warn-unused-command-bind",  "warn when a non-unit command result is unused")
  , (WarnUnsafeAutoCast,    "warn-unsafe-auto-cast",     "warn on potentially unsafe automatic cast")
  , (WarnUnsafeParAutoCast, "warn-unsafe-par-auto-cast", "warn on potentially unsafe automatic cast in par")
  ]

compilerOpts :: [String] -> IO (Flags, [String])
compilerOpts argv = do
    case getOpt Permute options argv of
      (fs,n,[])  -> do fs' <- flagImplications <$> foldl (>=>) return fs defaultFlags
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
    return $ usageInfo header (options :: [OptDescr (Flags -> IO Flags)])
