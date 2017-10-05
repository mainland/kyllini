{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  KZC.Driver.Opts
-- Copyright   :  (c) 2015-2017 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Driver.Opts (
    parseKzcOpts,
    kzcUsage
  ) where

import Control.Monad ((>=>),
                      when)
import Data.Maybe (fromMaybe)
import System.Console.GetOpt
import System.Environment (getProgName)

import KZC.Config
import KZC.Globals

options :: forall m . Monad m => [OptDescr (Config -> m Config)]
options =
    [ Option ['h', '?'] ["--help"]  (NoArg (setModeM Help))              "Show help"
    , Option ['q']      ["quiet"]   (NoArg (setDynFlagM Quiet))          "Be quiet"
    , Option ['v']      ["verbose"] (OptArg setVerbLevel "LEVEL")        "Be verbose"
    , Option ['c']      []          (NoArg (setModeM Compile))           "Compile"
    , Option ['P']      []          (NoArg (setDynFlagM StopAfterParse)) "Stop after parsing"
    , Option ['C']      []          (NoArg (setDynFlagM StopAfterCheck)) "Stop after type checking"
    , Option ['o']      ["output"]  (ReqArg outOpt "FILE")               "Output to FILE"
    , Option ['O']      []          (OptArg setOptLevel "LEVEL")         "Set optimization level"
    , Option ['i']      []          (ReqArg importPathOpt "DIR")        "Add import directory"
    , Option ['I']      []          (ReqArg includePathOpt "DIR")        "Add preprocessor include directory"
    , Option ['D']      []          (ReqArg defineOpt "VAR[=DEF]")       "Define preprocessor symbol"
    , Option ['w']      []          (NoArg inhibitWarnings)              "Inhibit all warning messages."
    , Option ['f']      []          (ReqArg parseFFlags "")              "Specify compiler options"
    , Option ['d']      []          (ReqArg parseDFlags "")              "Specify debug flags"
    , Option ['W']      []          (ReqArg parseWFlags "")              "Specify warnings"
    , Option ['s']      []          (NoArg setStats)                     "Display statistics"
    ]
  where
    setModeM :: ModeFlag -> Config -> m Config
    setModeM m fs = return fs { mode = m }

    setDynFlagM :: DynFlag -> Config -> m Config
    setDynFlagM f fs = return $ setDynFlag f fs

    setVerbLevel :: Maybe String -> Config -> m Config
    setVerbLevel Nothing fs =
        return fs { verbLevel = verbLevel fs + 1 }

    setVerbLevel (Just s) fs =
        case reads s of
          [(n, "")]  -> return fs { verbLevel = n }
          _          -> fail "argument to --verbose must be an integer"

    setOptLevel :: Maybe String -> Config -> m Config
    setOptLevel maybe_opt =
        go (fromMaybe "1" maybe_opt)
      where
        go :: String -> Config -> m Config
        go s conf = do
            n <- parseOptLevel s
            setOptIntLevel n conf

        parseOptLevel :: String -> m Int
        parseOptLevel s =
            case reads s of
              [(n, "")] | n >= 0 && n <= 3 -> return n
              _ -> fail "argument to -O must be an integer between 0 and 3"

        setOptIntLevel :: Int -> Config -> m Config
        setOptIntLevel 0 conf =
            return $ unsetDynFlags
              [ Fuse
              , Simplify
              , MayInlineVal
              , MayInlineFun
              , MayInlineComp
              , AlwaysInlineComp
              , PartialEval
              , AutoLUT
              , LUT
              , Pipeline
              , PipelineAll
              , Coalesce
              , CoalesceTop
              , FloatViews
              ]
              conf

        setOptIntLevel 1 conf =
            return $ setDynFlags
              [ Simplify
              , MayInlineVal
              , MayInlineFun
              , MayInlineComp
              ]
              conf

        setOptIntLevel 2 conf = do
            conf' <- setOptIntLevel 1 conf
            return $ setDynFlags
              [ Fuse
              , AutoLUT
              , LUT
              , FloatViews
              , ComputeLUTs
              ]
              conf'

        setOptIntLevel 3 conf = do
            conf' <- setOptIntLevel 2 conf
            return $ setDynFlags
              [ PartialEval
              , Coalesce
              , CoalesceTop
              ]
              conf'

        setOptIntLevel _ conf =
            return conf

    setStats :: Config -> m Config
    setStats = return . setDynFlags [ShowCgStats, ShowFusionStats]

    outOpt :: String -> Config -> m Config
    outOpt path fs = return fs { output = Just path }

    importPathOpt :: String -> Config -> m Config
    importPathOpt path fs = return fs { importPaths = importPaths fs ++ [path] }

    includePathOpt :: String -> Config -> m Config
    includePathOpt path fs = return fs { includePaths = includePaths fs ++ [path] }

    defineOpt :: String -> Config -> m Config
    defineOpt def fs = return fs { defines = defines fs ++ [splitOn '=' def] }

    inhibitWarnings :: Config -> m Config
    inhibitWarnings fs = return fs { warnFlags = mempty }

    parseFFlags :: String -> Config -> m Config
    parseFFlags = parseFlagOpts "-f" opts fOpts
      where
        opts :: [FlagOpt]
        opts = mkFlagOpts "" fFlags setDynFlag (Just unsetDynFlag)

    parseDFlags :: String -> Config -> m Config
    parseDFlags = parseFlagOpts "-d" opts dOpts
      where
        opts :: [FlagOpt]
        opts =
            mkFlagOpts ""       dFlags      setDynFlag   (Just unsetDynFlag) ++
            mkFlagOpts "dump-"  dDumpFlags  setDumpFlag  Nothing ++
            mkFlagOpts "trace-" dTraceFlags setTraceFlag Nothing

    parseWFlags :: String -> Config -> m Config
    parseWFlags = parseFlagOpts "-W" opts wOpts
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

data FlagOpt = forall a . FlagOpt a String String (a -> Config -> Config) (Maybe (a -> Config -> Config))

data FlagOptDescr a = FlagOption String (ArgDescr a) String

parseFlagOpts :: forall m . Monad m
              => String
              -> [FlagOpt]
              -> [FlagOptDescr (Config -> m Config)]
              -> String
              -> Config
              -> m Config
parseFlagOpts flagpfx fopts foptdescrs arg fs =
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
              -> [FlagOptDescr (Config -> m Config)]
              -> Config
              -> m Config
    parseOpts _ _ [] = fail $ "unrecognized option `" ++ flagpfx ++ arg ++ "'"

    parseOpts flag flagArg (FlagOption flag' argOpt _:_) | flag' == flag =
        go argOpt
      where
        go :: ArgDescr (Config -> m Config) -> Config -> m Config
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
          -> Config
          -> m (Maybe Config)
parseFlag flag = go
  where
    go :: [FlagOpt] -> Config -> m (Maybe Config)
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
           -> (a -> Config -> Config)
           -> Maybe (a -> Config -> Config)
           -> [FlagOpt]
mkFlagOpts pfx opts set unset =
    [FlagOpt f (pfx ++ s) desc set unset | (f, s, desc) <- opts]

fFlags :: [(DynFlag, String, String)]
fFlags =
    [ (StrictParser,  "strict-parse", "parse classic language strictly")
    , (PrettyPrint,   "pprint",       "pretty-print file")
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
    , (FloatViews,    "float-views",  "float view slices")
    ]

fOpts :: forall m . Monad m => [FlagOptDescr (Config -> m Config)]
fOpts =
    [ FlagOption "errctx"                    (ReqArg maxErrCtxOpt "INT")          "set maximum error context"
    , FlagOption "max-simplifier-iterations" (ReqArg maxSimplIterationsOpt "INT") "set maximum simplification iterations"
    , FlagOption "max-lut"                   (ReqArg maxLUTOpt "INT")             "set maximum LUT size in bytes"
    , FlagOption "min-lut-ops"               (ReqArg minLUTOpsOpt "N")            "set minimum operation count to consider a LUT"
    , FlagOption "max-fusion-blowup"         (ReqArg maxFusionBlowupOpt "FLOAT")  "set maximum allowed fusion blowup"
    , FlagOption "max-coalesce-buffer"       (ReqArg maxCoalesceBufferOpt "INT")  "set maximum coalescing buffer size (in bytes)"
    , FlagOption "max-coalesce-rate"         (ReqArg maxCoalesceRateOpt "INT")    "set maximum rate of widened computations during coalescing"
    , FlagOption "max-top-coalesce-rate"     (ReqArg maxTopCoalesceRateOpt "INT") "set maximum rate of widened top-level computations during coalescing"
    , FlagOption "min-memcpy-bytes"          (ReqArg minMemcpyBytesOpt "INT")     "set minimum number of bytes before using memcpy"
    , FlagOption "simpl"                     (NoArg simplOpt)                     "run the simplifier"
    , FlagOption "inline"                    (NoArg inlineOpt)                    "inline when simplifying"
    ]
  where
    simplOpt :: Config -> m Config
    simplOpt = return . setDynFlags [Simplify, MayInlineVal]

    inlineOpt :: Config -> m Config
    inlineOpt = return . setDynFlags [MayInlineFun, MayInlineComp]

    maxErrCtxOpt :: String -> Config -> m Config
    maxErrCtxOpt s fs =
      case reads s of
        [(n, "")]  -> return fs { maxErrCtx = n }
        _          -> fail "argument to -ferrctx must be an integer"

    maxSimplIterationsOpt :: String -> Config -> m Config
    maxSimplIterationsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxSimpl = n }
          _          -> fail "argument to -fmax-simplifier-iterations must be an integer"

    maxLUTOpt :: String -> Config -> m Config
    maxLUTOpt s fs = do
        n <- case humandReadable s of
               Just n  -> return n
               Nothing -> fail $ "bad argument to -fmax-lut option: " ++ s
        return fs { maxLUT     = n
                  , maxLUTLog2 = ceiling (logBase (2::Double) (fromIntegral n))
                  }

    minLUTOpsOpt :: String -> Config -> m Config
    minLUTOpsOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { minLUTOps = n }
          _          -> fail "argument to -fmin-lut-ops must be an integer"

    maxFusionBlowupOpt :: String -> Config -> m Config
    maxFusionBlowupOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxFusionBlowup = n }
          _          -> fail "argument to -fmax-fusion-blowup must be a float"

    maxCoalesceBufferOpt :: String -> Config -> m Config
    maxCoalesceBufferOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxCoalesceBuffer = n }
          _          -> fail "argument to -fmax-coalesce-buffer must be an integer"

    maxCoalesceRateOpt :: String -> Config -> m Config
    maxCoalesceRateOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxCoalesceRate = Just n }
          _          -> fail "argument to -fmax-coalesce-rate must be an integer"

    maxTopCoalesceRateOpt :: String -> Config -> m Config
    maxTopCoalesceRateOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { maxTopCoalesceRate = Just n }
          _          -> fail "argument to -fmax-top-coalesce-rate must be an integer"

    minMemcpyBytesOpt :: String -> Config -> m Config
    minMemcpyBytesOpt s fs =
        case reads s of
          [(n, "")]  -> return fs { minMemcpyBytes = n }
          _          -> fail "argument to -fmin-memcpy-bytes must be an integer"

dFlags :: [(DynFlag, String, String)]
dFlags =
    [ (Lint,            "lint",          "lint core")
    , (PipelineAll,     "pipeline-all",  "pipeline all computations")
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
    , (DumpViews,      "views",      "dump result of using views")
    , (DumpMono,       "mono",       "dump result of monomorphization")
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
    , (TraceViews,       "views",        "trace use of views")
    , (TraceMono,        "mono",         "trace monomorphization")
    ]

dOpts :: forall m . Monad m => [FlagOptDescr (Config -> m Config)]
dOpts =
  [ FlagOption "dump-all" (NoArg dumpAll)        "dump all output"
  , FlagOption "fuel"     (ReqArg addFuel "INT") "add debug fuel"
  ]
  where
    dumpAll :: Config -> m Config
    dumpAll = return . setDumpFlags [minBound..maxBound]

    addFuel :: String -> Config -> m Config
    addFuel s fs =
      case reads s of
        [(n, "")]  -> return fs { fuel = n }
        _          -> fail "argument to -dfuel must be an integer"

wFlags :: [(WarnFlag, String, String)]
wFlags =
    [ (WarnSimplifierBailout, "simplifier-bailout",   "warn when the simplifier bails out")
    , (WarnUnusedCommandBind, "unused-command-bind",  "warn when a non-unit command result is unused")
    , (WarnUnsafeAutoCast,    "unsafe-auto-cast",     "warn on potentially unsafe automatic cast")
    , (WarnUnsafeParAutoCast, "unsafe-par-auto-cast", "warn on potentially unsafe automatic cast in par")
    , (WarnRateMismatch,      "rate-mismatch",        "warn on producer/consumer rate mismatch in par")
    , (WarnFusionFailure,     "fusion-failure",       "warn on fusion failure")
    , (WarnBitArrayCopy,      "bitarray-copy",        "warn on a bit array copy")
    ]

wOpts :: forall m . Monad m => [FlagOptDescr (Config -> m Config)]
wOpts =
    [ FlagOption "all"   (NoArg wAll)            "enable all warnings about questionable constructs"
    , FlagOption "error" (OptArg werror "WFLAG") "make warnings errors"
    ]
  where
    wAll :: Config -> m Config
    wAll = return . setWarnFlags [WarnUnusedCommandBind, WarnUnsafeAutoCast]

    werror :: Maybe String -> Config -> m Config
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

parseKzcOpts :: [String] -> IO (Config, [String])
parseKzcOpts argv =
    case getOpt Permute options argv of
      (fs,n,[])  -> do fs' <- flagImplications <$> foldl (>=>) return fs defaultConfig
                       setMaxErrContext (maxErrCtx fs')
                       when (testDynFlag StrictParser fs') $
                           setStrictClassic True
                       when (testDynFlag PrintUniques fs') $
                           setPrintUniques True
                       when (testDynFlag ExpertTypes fs') $
                           setExpertTypes True
                       return (fs', n)
      (_,_,errs) -> do usageDesc <- kzcUsage
                       ioError (userError (concat errs ++ usageDesc))

kzcUsage :: IO String
kzcUsage = do
    progname   <- getProgName
    let header =  "Usage: " ++ progname ++ " [OPTION...] files..."
    return $ usageInfo header (options :: [OptDescr (Config -> IO Config)])
