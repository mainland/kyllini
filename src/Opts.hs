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
import Data.List (foldl',
                  isPrefixOf)
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
        , Option [] ["fmax-fusion-blowup"]
            (ReqArg maxFusionBlowupOpt "DOUBLE")
            "set maximum allowd fusion blowup"
        , Option [] ["fsimpl"]
            (NoArg simplOpt)
            "run the simplifier"
        , Option [] ["finline"]
            (NoArg inlineOpt)
            "inline when simplifying"
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

    maxFusionBlowupOpt :: String -> Flags -> m Flags
    maxFusionBlowupOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxFusionBlowup = n }
          _          -> fail "argument to --fmax-fusion-blowup must be a float"

    dumpAll :: Flags -> m Flags
    dumpAll fs =
        return $ foldl' (flip setDumpFlag) fs [minBound..maxBound]

    maxLUTOpt :: String -> Flags -> m Flags
    maxLUTOpt s fs = do
        n <- case humandReadable s of
               Just n  -> return n
               Nothing -> fail $ "bad argument to --fmax-lut option: " ++ s
        return fs { maxLUT     = n
                  , maxLUTLog2 = ceiling (logBase (2::Double) (fromIntegral n))
                  }

    minLUTOpsOpt :: String -> Flags -> m Flags
    minLUTOpsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { minLUTOps = n }
          _          -> fail "argument to --fmin-lut-ops must be an integer"

    simplOpt :: Flags -> m Flags
    simplOpt fs = return $
                  setDynFlag Simplify $
                  setDynFlag MayInlineVal
                  fs

    inlineOpt :: Flags -> m Flags
    inlineOpt fs = return $
                   setDynFlag MayInlineFun $
                   setDynFlag MayInlineComp
                   fs

    outOpt :: String -> Flags -> m Flags
    outOpt path fs = return fs { output = Just path }

    includePathOpt :: String -> Flags -> m Flags
    includePathOpt path fs = return fs { includePaths = includePaths fs ++ [path] }

    defineOpt :: String -> Flags -> m Flags
    defineOpt def fs = return fs { defines = defines fs ++ [splitOn '=' def] }

splitOn :: Eq a => a -> [a] -> ([a], [a])
splitOn x s = case break (== x) s of
              (xs, []) -> (xs, [])
              (xs, ys) -> (xs, drop 1 ys)

humandReadable :: (Integral a, Read a, Monad m) => String -> m a
humandReadable s =
    case reads s of
      (n, "")  : _ -> return n
      (n, "k") : _ -> return (n*1024)
      (n, "K") : _ -> return (n*1024)
      (n, "m") : _ -> return (n*1024*1024)
      (n, "M") : _ -> return (n*1024*1024)
      _            -> fail "bad argument"

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
mkSetOptFlag pfx mfx set _unset (f, str, desc) | "no" `isPrefixOf` str =
    [  Option  [] [pfx ++ mfx ++ str] (NoArg (return . set f)) desc
    ]

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
  [ (PrettyPrint,   "pprint",       "pretty-print file")
  , (LinePragmas,   "line-pragmas", "print line pragmas in generated C")
  , (Fuse,          "fuse",         "run the par fuser")
  , (MayInlineVal,  "inline-val",   "inline values when simplifying")
  , (MayInlineFun,  "inline-fun",   "inline functions when simplifying")
  , (MayInlineComp, "inline-comp",  "inline computation functions when simplifying")
  , (BoundsCheck,   "bounds-check", "generate bounds checks")
  , (PartialEval,   "peval",        "run the partial evaluator")
  , (Timers,        "timers",       "insert code to track elapsed time")
  , (AutoLUT,       "autolut",      "run the auto-LUTter")
  , (LUT,           "lut",          "run the LUTter")
  , (NoGensym,      "no-gensym",    "don't gensym (for debugging)")
  , (Pipeline,      "pipeline",     "pipeline computations")
  , (Coalesce,      "coalesce",     "coalesce computations")
  , (VectOnlyBytes, "vect-bytes",   "only vectorize to byte widths")
  , (VectFilterAnn, "vect-ann",     "use vectorization annotations")
  , (CoalesceTop,   "coalesce-top", "coalesce top-level computation")
  , (FuseUnroll,    "fuse-unroll",  "unroll loops during fusion")
  ]

dDynFlagOpts :: [(DynFlag, String, String)]
dDynFlagOpts =
  [ (Lint,          "lint",
                    "lint core")
  , (PrintUniques,  "print-uniques",
                    "show uniques when pretty-printing")
  , (ExpertTypes,   "expert-types",
                    "show \"expert\" types when pretty-printing")
  , (ShowCgStats,   "cg-stats",
                    "show code generator statistics")
  , (ShowFusionStats, "fusion-stats",
                      "show fusion statistics")
  ]

dDumpFlagOpts :: [(DumpFlag, String, String)]
dDumpFlagOpts =
  [ (DumpCPP,        "cpp",        "dump CPP output")
  , (DumpRename,     "rn",         "dump renamer output")
  , (DumpLift,       "lift",       "dump lambda lifter output")
  , (DumpFusion,     "fusion",     "dump fusion output")
  , (DumpCore,       "core",       "dump core")
  , (DumpOcc,        "occ",        "dump occurrence info")
  , (DumpSimpl,      "simpl",      "dump simplifier output")
  , (DumpEval,       "peval",      "dump partial evaluator output")
  , (DumpAutoLUT,    "autolut",    "dump auto-LUTter")
  , (DumpLUT,        "lut",        "dump LUTter")
  , (DumpHashCons,   "hashcons",   "dump hashcons of constants")
  , (DumpStaticRefs, "staticrefs", "dump result of static refs")
  , (DumpRate,       "rate",       "dump result of rate analysis")
  , (DumpCoalesce,   "coalesce",   "dump result of pipeline coalescing")
  ]

dTraceFlagOpts :: [(TraceFlag, String, String)]
dTraceFlagOpts =
  [ (TracePhase,       "phase",        "trace compiler phase")
  , (TraceLexer,       "lex",          "trace lexer")
  , (TraceParser,      "parse",        "trace parser")
  , (TraceRn,          "rn",           "trace renamer")
  , (TraceLift,        "lift",         "trace lambda lifter")
  , (TraceTc,          "tc",           "trace type checker")
  , (TraceCg,          "cg",           "trace code generation")
  , (TraceLint,        "lint",         "trace linter")
  , (TraceExprToCore,  "expr-to-core", "trace conversion from expr language to core")
  , (TraceFusion,      "fusion",       "trace fusion")
  , (TraceSimplify,    "simpl",        "trace simplifier")
  , (TraceEval,        "eval",         "trace evaluator")
  , (TraceAutoLUT,     "autolut",      "trace auto-LUTter")
  , (TraceLUT,         "lut",          "trace LUTter")
  , (TraceRefFlow,     "rflow",        "trace ref-flow")
  , (TraceNeedDefault, "need-default", "trace default need")
  , (TraceRate,        "rate",         "trace rate analysis")
  , (TraceCoalesce,    "coalesce",     "trace pipeline coalescing")
  ]

wWarnFlagOpts :: [(WarnFlag, String, String)]
wWarnFlagOpts =
  [ (WarnError, "error", "make warnings errors")
  ]

fWarnFlagOpts :: [(WarnFlag, String, String)]
fWarnFlagOpts =
  [ (WarnSimplifierBailout, "warn-simplifier-bailout",   "warn when the simplifier bails out")
  , (WarnUnusedCommandBind, "warn-unused-command-bind",  "warn when a non-unit command result is unused")
  , (WarnUnsafeAutoCast,    "warn-unsafe-auto-cast",     "warn on potentially unsafe automatic cast")
  , (WarnUnsafeParAutoCast, "warn-unsafe-par-auto-cast", "warn on potentially unsafe automatic cast in par")
  , (WarnRateMismatch,      "warn-rate-mismatch",        "warn on producer/consumer rate mismatch in par")
  ]

compilerOpts :: [String] -> IO (Flags, [String])
compilerOpts argv =
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
