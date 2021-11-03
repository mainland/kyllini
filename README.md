# Building `kzc`

`kzc` is developed on Linux using GHC 8.10.7 and is compatible with GHC versions 8.0.2 through 9.0.1. There are three ways to build the project.

#### Building with `stack`

The default `stack` build currently uses [LTS 18.15](https://www.stackage.org/lts-18.15).

```
stack install
```

#### Building with `make`

When `make` is used, packages installed by stack LTS (or in the current cabal sandbox) will be used, if available. If the stack packages are present, they are preferred. Note that using the stack package database requires that the version of GHC in your path is the same as the version of GHC included in the stack LTS. It also requires that stack has already built the packages this project needs, which can be accomplished by building once with `stack build`. If you want to build a profiled version of `kzc`, use `stack build --profile`.

```
./configure
make
```

#### Building with `cabal`

```
cabal configure
cabal build
```

Building with `cabal` *will not* generate binaries in the `bin` directory, so you will need to specify the path to `kzc` explicitly when invoking  `bin/runtests.py`.

## Building under Windows

 1. Install [MSYS2](https://msys2.github.io/).
 1. Installing the [Haskell Platform](https://www.haskell.org/platform/windows.html).
 1. Install the toolchains you need. You can run the kyllini tests in the MinGW environment (recommended, because this is what GHC uses under Windows) or in the MSYS2 environment. Read the [description of the different MSYS2 subsystems](https://github.com/msys2/msys2/wiki/MSYS2-introduction#msys2-susbsystems) to see which packages you need to install.
 1. Install the `autoconf` MSYS2 package, e.g., execute `pacman -S autoconf` in the MSYS2 shell.
 1. Set the Windows environment variable `MSYS2_PATH_TYPE` to `inherit` so that MSYS2 will pick up your `PATH` and can find GHC.

After installing MSYS2, follow the instructions above.

# Testing

The `bin/runtests.py` script implements a flexible testing framework that can test not only input/output correctness, but also various code metrics like input/output rate and number of for loops. This helps verify that compiler changes don't introduce performance regressions.

Running `./bin/runtests.py --help` will display the available options. There are two main sets of test once should run.

The first tests correctness over a wide range of compiler flags. It is run as follows:

```
./bin/runtests.py testsuite examples/wifi --all-ways
```

The second tests metrics that correlate to performance. It is run as follows:

```
./bin/runtests.py examples/wifi/transmitter/perf examples/wifi/receiver/perf examples/wifi/perf --way perf
```

## Validate script

The `validate` scripts runs the test suite with a large number of optimization flag combinations. Running it is as simple as executing

```
./validate
```

Extra flags can be passed to the compiler during validation by setting the `KZCFLAGS` environment variable.

All compiler changes should be validated before being pushed! It is also a good idea to validate after changes to *any* component of the system.

# Performance testing

Instructions for running performance tests are in the [README in the `perf` directory](perf/README.md).

# Acknowledgments

This material is based upon work supported by the National Science Foundation under [Grant No. 1717088](https://www.nsf.gov/awardsearch/showAward?AWD_ID=1717088). Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.
