# `kzc` User Guide

## General flags

| Flag                 | Description |
| ---                  | --- |
| `-h`, `-?`, `--help` | Display help |
| `-q`, `--quiet`      | Be quiet |
| `-v`, `--verbose`    | Increase verbosity level |
| `-o FILE`            | Specify output files |
| `-I DIR`             | Specify a preprocessor include directory |
| `-DVAR[=DEF]`        | Define a preprocessor symbol |

## Warning flags

Individual errors have a negated form, either `-Wno` or `-Wno-`, e.g.,
`-Wno-unused-command-bind`.

The only default warning flag is `-Wunused-command-bind`.

Individual warnings can be turned into errors with `-Werror=`, e.g.,
`-Werror=unused-command-bind`.

`-Wall` turns on `-Wunused-command-bind` and `-Wunsafe-auto-cast`.

The combined effect of multiple warning flag specifications is that they are
applied in order. For example, `-Wunsafe-auto-cast -Werror
-Wunused-command-bind` will fail with an error on an unsafe auto cast, but only
warn on an unused command bind.

| Flag                     | Description |
| ---                      | --- |
| `-w`                     | Inhibit all warnings |
| `-Wall`                  | Enable all warnings about questionable constructs |
| `-Werror`                | Make all warnings errors |
| `-Wsimplifier-bailout`   | Warn when the simplifier bails out|
| `-Wunused-command-bind`  | Warn when a non-unit command result is unused|
| `-Wunsafe-auto-cast`     | Warn on potentially unsafe automatic cast|
| `-Wunsafe-par-auto-cast` | Warn on potentially unsafe automatic cast in par|
| `-Wrate-mismatch`        | Warn on producer/consumer rate mismatch in par|
| `-Wfusion-failure`       | Warn on fusion failure|

## Feature flags

| Flag             | Description |
| ---              | --- |
| `-fpprint`       | Pretty-print file (for debugging) |
| `-fno-gensym`    | Don't gensym (for debugging) |
| `-fline-pragmas` | Print line pragmas in generated C |
| `-finline-val`   | Inline values when simplifying |
| `-finline-fun`   | Inline functions when simplifying |
| `-finline-comp`  | Inline computation functions when simplifying |
| `-fbounds-check` | Generate bounds checks |
| `-fpeval`        | Run the partial evaluator |
| `-ftimers`       | Insert code to track elapsed time |
| `-fautolut`      | Run the auto-LUTter |
| `-flut`          | Run the LUTter |
| `-fpipeline`     | Pipeline computations |
| `-fvect-bytes`   | Only vectorize to byte widths |
| `-fvect-ann`     | Use vectorization annotations |
| `-ffuse`         | Perform par fusion |
| `-ffuse-unroll`  | Unroll loops during fusion |
| `-fcoalesce`     | Coalesce computations |
| `-fcoalesce-top` | Coalesce top-level computation |
| `-fsimpl`        | Run the simplifier|
| `-finline`       | Inline when simplifying|
| `-flower-gen`     | Lower generators to explicit constant arrays |
| `-fcompute-luts` | Compute LUTs instead of compiling them to constants |
| `-ferrctx=INT`                    | set maximum error context"
| `-fmax-simplifier-iterations=INT` | Set maximum simplification iterations|
| `-fmax-lut=INT`                   | Set maximum LUT size in bytes|
| `-fmin-lut-ops=N`                 | Set minimum operation count to consider a LUT|
| `-fmax-fusion-blowup=FLOAT`       | Set maximum allowed fusion blowup|

## Debugging flags

| Flag              | Description |
| ---               | --- |
| `-dlint`          | Lint core |
| `-dprint-uniques` | Show uniques when pretty-printing |
| `-dexpert-types`  | Show "expert" types when pretty-printing |
| `-dcg-stats`      | Show code generator statistics |
| `-dfusion-stats`  | Show fusion statistics |

### Dump flags

| Flag                | Description |
| ---                 | --- |
| `-ddump-cpp`        | Dump preprocessor output |
| `-ddump-rn`         | Dump renamer output |
| `-ddump-lift`       | Dump lambda lifter output |
| `-ddump-fusion`     | Dump fusion output |
| `-ddump-core`       | Dump core |
| `-ddump-occ`        | Dump occurrence info |
| `-ddump-simpl`      | Dump simplifier output |
| `-ddump-peval`      | Dump partial evaluator output |
| `-ddump-autolut`    | Dump auto-LUTter |
| `-ddump-lut`        | Dump LUTter |
| `-ddump-hashcons`   | Dump hashcons of constants |
| `-ddump-staticrefs` | Dump result of static refs |
| `-ddump-rate`       | Dump result of rate analysis |
| `-ddump-coalesce`   | Dump result of pipeline coalescing |

### Tracing flags

| Flag                   | Description |
| ---                    | --- |
| `-dtrace-phase`        | Trace compiler phase |
| `-dtrace-lex`          | Trace lexer |
| `-dtrace-parse`        | Trace parser |
| `-dtrace-rn`           | Trace renamer |
| `-dtrace-lift`         | Trace lambda lifter |
| `-dtrace-tc`           | Trace type checker |
| `-dtrace-cg`           | Trace code generation |
| `-dtrace-lint`         | Trace linter |
| `-dtrace-expr-to-core` | Trace conversion from expr language to core |
| `-dtrace-fusion`       | Trace fusion |
| `-dtrace-simpl`        | Trace simplifier |
| `-dtrace-eval`         | Trace evaluator |
| `-dtrace-autolut`      | Trace auto-LUTter |
| `-dtrace-lut`          | Trace LUTter |
| `-dtrace-rflow`        | Trace ref-flow |
| `-dtrace-need-default` | Trace default need |
| `-dtrace-rate`         | Trace rate analysis |
| `-dtrace-coalesce`     | Trace pipeline coalescing |
