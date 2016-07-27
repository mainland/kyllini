{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
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
import System.Console.GetOpt
import System.Environment (getProgName)

import KZC.Flags
import KZC.Globals

options :: forall m . Monad m => [OptDescr (Flags -> m Flags)]
options =
    [ Option ['h', '?'] ["--help"]  (NoArg (setModeM Help))              "Show help"
    , Option ['q']      ["quiet"]   (NoArg (setDynFlagM Quiet))          "Be quiet"
    , Option ['v']      ["verbose"] (OptArg maybeSetVerbLevel "LEVEL")   "Be verbose"
    , Option ['c']      []          (NoArg (setModeM Compile))           "Compile"
    , Option ['P']      []          (NoArg (setDynFlagM StopAfterParse)) "Stop after parsing"
    , Option ['C']      []          (NoArg (setDynFlagM StopAfterCheck)) "Stop after type checking"
    , Option ['o']      ["output"]  (ReqArg outOpt "FILE")               "Output to FILE"
    , Option ['I']      []          (ReqArg includePathOpt "DIR")        "Add preprocessor include directory"
    , Option ['D']      []          (ReqArg defineOpt "VAR[=DEF]")       "Define preprocessor symbol"
    , Option ['w']      []          (NoArg inhibitWarnings)              "Inhibit all warning messages."
    , Option ['f']      []          (ReqArg parseFFlags "")              "Specify compiler options"
    , Option ['d']      []          (ReqArg parseDFlags "")              "Specify debug flags"
    , Option ['W']      []          (ReqArg parseWFlags "")              "Specify warnings"
    ]
  where
    setModeM :: ModeFlag -> Flags -> m Flags
    setModeM m fs = return fs { mode = m }

    setDynFlagM :: DynFlag -> Flags -> m Flags
    setDynFlagM f fs = return $ setDynFlag f fs

    maybeSetVerbLevel :: Maybe String -> Flags -> m Flags
    maybeSetVerbLevel Nothing fs =
        return fs { verbLevel = verbLevel fs + 1 }

    maybeSetVerbLevel (Just s) fs =
        case reads s of
          [(n, "")]  -> return fs { verbLevel = n }
          _          -> fail "argument to --verbose must be an integer"

    outOpt :: String -> Flags -> m Flags
    outOpt path fs = return fs { output = Just path }

    includePathOpt :: String -> Flags -> m Flags
    includePathOpt path fs = return fs { includePaths = includePaths fs ++ [path] }

    defineOpt :: String -> Flags -> m Flags
    defineOpt def fs = return fs { defines = defines fs ++ [splitOn '=' def] }

    inhibitWarnings :: Flags -> m Flags
    inhibitWarnings fs = return fs { warnFlags = mempty }

    parseFFlags :: Monad m => String -> Flags -> m Flags
    parseFFlags = parseFlagOpts opts fOpts
      where
        opts :: [FlagOpt]
        opts = mkFlagOpts "" fFlags setDynFlag (Just unsetDynFlag)

    parseDFlags :: Monad m => String -> Flags -> m Flags
    parseDFlags = parseFlagOpts opts dOpts
      where
        opts :: [FlagOpt]
        opts =
            mkFlagOpts ""       dFlags      setDynFlag   (Just unsetDynFlag) ++
            mkFlagOpts "dump-"  dDumpFlags  setDumpFlag  Nothing ++
            mkFlagOpts "trace-" dTraceFlags setTraceFlag Nothing

    parseWFlags :: Monad m => String -> Flags -> m Flags
    parseWFlags = parseFlagOpts opts wOpts
      where
        opts :: [FlagOpt]
        opts = mkFlagOpts "" wFlags setWarnFlag (Just unsetWarnFlag)

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

data FlagOpt = forall a . FlagOpt a String String (a -> Flags -> Flags) (Maybe (a -> Flags -> Flags))

data FlagOptDescr a = FlagOption String (ArgDescr a) String

parseFlagOpts :: forall m . Monad m
              => [FlagOpt]
              -> [FlagOptDescr (Flags -> m Flags)]
              -> String
              -> Flags
              -> m Flags
parseFlagOpts fopts foptdescrs arg fs =
    if null flagArg
      then do maybe_fs' <- parseFlag flag fopts fs
              case maybe_fs' of
                Nothing  -> parseOpts flag flagArg foptdescrs fs
                Just fs' -> return fs'
      else parseOpts flag flagArg foptdescrs fs
  where
    flag, flagArg :: String
    (flag, flagArg) = splitOn '=' arg

    parseOpts :: String
              -> String
              -> [FlagOptDescr (Flags -> m Flags)]
              -> Flags
              -> m Flags
    parseOpts _ _ [] = fail $ "unrecognized option `" ++ arg ++ "'"

    parseOpts flag flagArg (FlagOption flag' argOpt _:_) | flag' == flag =
        go argOpt
      where
        go :: ArgDescr (Flags -> m Flags) -> Flags -> m Flags
        go (NoArg g)    | null flagArg = g
                        | otherwise    = fail $ "Argument specified:" ++ arg
        go (OptArg g _) | null flagArg = g Nothing
                        | otherwise    = g (Just flagArg)
        go (ReqArg g _) | null flagArg = fail $ "Argument required:" ++ arg
                        | otherwise    = g flagArg

    parseOpts flag flagArg (_:opts) =
        parseOpts flag flagArg opts

parseFlag :: forall m . Monad m
          => String
          -> [FlagOpt]
          -> Flags
          -> m (Maybe Flags)
parseFlag flag = go
  where
    go :: [FlagOpt] -> Flags -> m (Maybe Flags)
    go [] =
        return . const Nothing

    go (FlagOpt f s _ set Nothing:fs')
      | flag == s = return . Just . set f
      | otherwise = go fs'

    go (FlagOpt f s _ set (Just unset):fs')
      | flag == s          = return . Just . set f
      | flag == "no" ++ s  = return . Just . unset f
      | flag == "no-" ++ s = return . Just . unset f
      | otherwise          = go fs'

mkFlagOpts :: String
           -> [(a, String, String)]
           -> (a -> Flags -> Flags)
           -> Maybe (a -> Flags -> Flags)
           -> [FlagOpt]
mkFlagOpts pfx opts set unset =
    [FlagOpt f (pfx ++ s) desc set unset | (f, s, desc) <- opts]

fFlags :: [(DynFlag, String, String)]
fFlags =
    [ (PrettyPrint,   "pprint",       "pretty-print file")
    , (LinePragmas,   "line-pragmas", "print line pragmas in generated C")
    , (NoGensym,      "no-gensym",    "don't gensym (for debugging)")
    , (MayInlineVal,  "inline-val",   "inline values when simplifying")
    , (MayInlineFun,  "inline-fun",   "inline functions when simplifying")
    , (MayInlineComp, "inline-comp",  "inline computation functions when simplifying")
    , (BoundsCheck,   "bounds-check", "generate bounds checks")
    , (PartialEval,   "peval",        "run the partial evaluator")
    , (Timers,        "timers",       "insert code to track elapsed time")
    , (AutoLUT,       "autolut",      "run the auto-LUTter")
    , (LUT,           "lut",          "run the LUTter")
    , (Pipeline,      "pipeline",     "pipeline computations")
    , (Fuse,          "fuse",         "run the par fuser")
    , (FuseUnroll,    "fuse-unroll",  "unroll loops during fusion")
    , (VectOnlyBytes, "vect-bytes",   "only vectorize to byte widths")
    , (VectFilterAnn, "vect-ann",     "use vectorization annotations")
    , (Coalesce,      "coalesce",     "coalesce computations")
    , (CoalesceTop,   "coalesce-top", "coalesce top-level computation")
    , (LowerGen,      "lower-gen",    "lower generators to constants")
    , (ComputeLUTs,   "compute-luts", "compute LUTs instead of compiling them to constants")
    ]

fOpts :: forall m . Monad m => [FlagOptDescr (Flags -> m Flags)]
fOpts =
    [ FlagOption "errctx"                    (ReqArg maxErrCtxOpt "INT")          "set maximum error context"
    , FlagOption "max-simplifier-iterations" (ReqArg maxSimplIterationsOpt "INT") "set maximum simplification iterations"
    , FlagOption "max-lut"                   (ReqArg maxLUTOpt "INT")             "set maximum LUT size in bytes"
    , FlagOption "min-lut-ops"               (ReqArg minLUTOpsOpt "N")            "set minimum operation count to consider a LUT"
    , FlagOption "max-fusion-blowup"         (ReqArg maxFusionBlowupOpt "FLOAT")  "set maximum allowed fusion blowup"
    , FlagOption "simpl"                     (NoArg simplOpt)                     "run the simplifier"
    , FlagOption "inline"                    (NoArg inlineOpt)                    "inline when simplifying"
    ]
  where
    simplOpt :: Flags -> m Flags
    simplOpt = return . setDynFlags [Simplify, MayInlineVal]

    inlineOpt :: Flags -> m Flags
    inlineOpt = return . setDynFlags [MayInlineFun, MayInlineComp]

    maxErrCtxOpt :: String -> Flags -> m Flags
    maxErrCtxOpt s fs =
      case reads s of
        [(n, "")]  -> return fs { maxErrCtx = n }
        _          -> fail "argument to -ferrctx must be an integer"

    maxSimplIterationsOpt :: String -> Flags -> m Flags
    maxSimplIterationsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxSimpl = n }
          _          -> fail "argument to -fmax-simplifier-iterations must be an integer"

    maxLUTOpt :: String -> Flags -> m Flags
    maxLUTOpt s fs = do
        n <- case humandReadable s of
               Just n  -> return n
               Nothing -> fail $ "bad argument to -fmax-lut option: " ++ s
        return fs { maxLUT     = n
                  , maxLUTLog2 = ceiling (logBase (2::Double) (fromIntegral n))
                  }

    minLUTOpsOpt :: String -> Flags -> m Flags
    minLUTOpsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { minLUTOps = n }
          _          -> fail "argument to -fmin-lut-ops must be an integer"

    maxFusionBlowupOpt :: String -> Flags -> m Flags
    maxFusionBlowupOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxFusionBlowup = n }
          _          -> fail "argument to -fmax-fusion-blowup must be a float"

dFlags :: [(DynFlag, String, String)]
dFlags =
    [ (Lint,            "lint",          "lint core")
    , (PrintUniques,    "print-uniques", "show uniques when pretty-printing")
    , (ExpertTypes,     "expert-types",  "show \"expert\" types when pretty-printing")
    , (ShowCgStats,     "cg-stats",      "show code generator statistics")
    , (ShowFusionStats, "fusion-stats",  "show fusion statistics")
    ]

dDumpFlags :: [(DumpFlag, String, String)]
dDumpFlags =
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

dTraceFlags :: [(TraceFlag, String, String)]
dTraceFlags =
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

dOpts :: forall m . Monad m => [FlagOptDescr (Flags -> m Flags)]
dOpts = [FlagOption "dump-all" (NoArg dumpAll) "dump all output"]
  where
    dumpAll :: Flags -> m Flags
    dumpAll = return . setDumpFlags [minBound..maxBound]

wFlags :: [(WarnFlag, String, String)]
wFlags =
    [ (WarnSimplifierBailout, "simplifier-bailout",   "warn when the simplifier bails out")
    , (WarnUnusedCommandBind, "unused-command-bind",  "warn when a non-unit command result is unused")
    , (WarnUnsafeAutoCast,    "unsafe-auto-cast",     "warn on potentially unsafe automatic cast")
    , (WarnUnsafeParAutoCast, "unsafe-par-auto-cast", "warn on potentially unsafe automatic cast in par")
    , (WarnRateMismatch,      "rate-mismatch",        "warn on producer/consumer rate mismatch in par")
    , (WarnFusionFailure,     "fusion-failure",       "warn on fusion failure")
    ]

wOpts :: forall m . Monad m => [FlagOptDescr (Flags -> m Flags)]
wOpts =
    [ FlagOption "all"   (NoArg wAll)            "enable all warnings about questionable constructs"
    , FlagOption "error" (OptArg werror "WFLAG") "make warnings errors"
    ]
  where
    wAll :: Flags -> m Flags
    wAll = return . setWarnFlags [WarnUnusedCommandBind, WarnUnsafeAutoCast]

    werror :: Maybe String -> Flags -> m Flags
    werror Nothing  fs =
        return $ fs { werrorFlags = warnFlags fs }
    werror (Just f) fs = do
        maybe_fs' <- parseFlag f werrorOpts fs
        case maybe_fs' of
          Nothing  -> fail $ "Unrecognized flag `" ++ f ++ "`"
          Just fs' -> return fs'
      where
        werrorOpts :: [FlagOpt]
        werrorOpts = mkFlagOpts "" wFlags setWerrorFlag (Just unsetWerrorFlag)

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
