# ICFP '17 Artifact for *Better Living Through Operational Semantics: An Optimizing Compiler for Radio Protocols*

We provide an Ubuntu 16.04 LTS VMWare appliance containing all necessary tools to build the `kyllini` compiler and run the benchmarks from the paper *Better Living Through Operational Semantics: An Optimizing
Compiler for Radio Protocols*. You can log in to the appliance as user `icfp17` with password `icfp17`.

All code included in the appliance is available [on GitHub](https://github.com/mainland/kyllini/tree/icfp17).

This document is available [on GitHub](https://github.com/mainland/kyllini/blob/icfp17/ArtifactOverview.md) as well, as is the script used to prepare the artifact appliance.

## Getting Started

### Building `kyllini`

To save time, the virtual machine contains a full build of the `kyllini` compiler in the `kyllini` subdirectory of the `icfp17` user's home directory. This was accomplished by executing the following commands as the `icfp17` user:

```
git clone https://github.com/mainland/kyllini.git
cd kyllini
git checkout icfp17
./build-icfp17.sh
```

Note that the WiFi implementation benchmarked in the paper is contained in a git submodule, as is the version of the original Ziria compiler that was used for purposes of comparison.

### Running the `kzc` compiler

The [User Guide](doc/userguide.md) provides a detailed description of the available `kzc` flags. Important flags include:

 * `-IDIR`: Add `DIR` to the list of `#include` paths
 * `-o`: Specify output file for generated C.
 * `-ON`: Enable optimization level `N`. `N` may take values between 0 and 3, inclusive.

There is an extensive test suite in the `testsuite` directory, and the WiFi stack used in the benchmarks is in the `examples/wifi` directory. Each test `TEST` comes with an input file and expected ("ground truth") output file, named `TEST.infile` and `TEST.outfile.ground`, respectively. Tests can be run individually by `make`-ing the `TEST.test` target. By default, when running a test, extraneous output is hidden. To see all steps performed when running a test, invoke `make` with the additional virtual target `noquiet`, as shown in the following transcript:

```
> cd examples/wifi/tests
> make test_encdec_12mbps.test noquiet
../../../kzc -I../../../testsuite/lib -dlint -dprint-uniques -fno-line-pragmas  test_encdec.blk -o test_encdec.c
gcc -I../../../include -I../../../libkz/include -std=gnu99 -msse4 -c test_encdec.c -o test_encdec.o
gcc  test_encdec.o ../../../libkz/src/bits.o ../../../libkz/src/driver.o ../../../libkz/src/ext.o ../../../libkz/src/ext_zira.o ../../../libkz/src/io.o ../../../libkz/src/threads.o ../../../libkz/src/sora/kz_sora.o -lm -lpthread -lstdc++ -o test_encdec.exe
./test_encdec.exe \
             --input=test_encdec_12mbps.infile \
             --input-mode=text \
             --output=test_encdec_12mbps.outfile \
             --output-mode=text
Header - modulation: M_QPSK, coding: 1/2, length: 100 B
Header bits: 010100010011000001000000
Header - modulation: M_QPSK, coding: 1/2, length: 100 B
Header bits: 010100010011000001000000

CRC passed: 67 33 21 FFFFFFB6
Comparing output for test_encdec_12mbps
../../../dist/build/BlinkDiff/BlinkDiff -f test_encdec_12mbps.outfile -g test_encdec_12mbps.outfile.ground -d -v -n 0.81 -t 105
Matching! (EOF) (Accuracy 100.0%)
rm test_encdec.exe test_encdec_12mbps.outfile test_encdec.o test_encdec.c
```

There are also makefile targets for generating only the C source produces by `kzc`, for example:

```
> make test_encdec.c noquiet
../../../kzc -I../../../testsuite/lib -dlint -dprint-uniques -fno-line-pragmas  test_encdec.blk -o test_encdec.c
```

The test validation suite can be run as follows:

```
./validate
```

This can take a very long time to complete.

## Evaluation

### Reproducing the benchmarks and plots

Once the `kzc` and `wplc` compilers have been built according to the instructions from the previous section, the full benchmark suite can be run by executing the following commands in the `kyllini` source directory:

```
cd perf
./perf-icfp17.sh
```

This will run the benchmarks in the ICFP '17 paper and produce a file named `icfp17.csv`. **The benchmarks can take upwards of 15min to run.**

Once benchmark data has been collected, the four plots from the evaluation section of the paper can be reproduced by executing the following command (also in the `perf` subdirectory):

```
./plot-icfp17.R
```

The file `icfp17-submission.csv` contains the data used to generate the plots in the paper. To replicate the plots in the paper, copy `icfp17-submission.csv` to `icfp17.csv`.

Note that there are two small differences with respect to the plots in the paper:

 1. Each benchmarks was run 100 times for the paper, where as the `perf-icfp17.sh` script runs each benchmark only 10 times. Change the line `N=10` in the script to modify the number of runs.
 2. The plots in the paper are grayscale, whereas the script produces color plots. See the comments in `plot-icfp17.R` regarding the paper/artifact plots to change this.
