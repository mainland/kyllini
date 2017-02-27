# Building `kzc`

`kzc` is developed using GHC 8.0, although it should compile with at most minor
changes under 7.8 and 7.10. It does require `autoconf`; when building under
Windows, [msys2](https://msys2.github.io/) should be used.

The compiler can be built as follows:

```
cabal sandbox init
cabal install --only-dependencies --enable-tests
autoconf && ./configure && make
```

# Validating changes

The `validate` scripts runs the test suite with a large number of optimization
flag combinations. Running it is as simple as executing

    ./validate

Extra flags can be passed to the compiler during validation by setting the
`KZCFLAGS` environment variable.

All compiler changes should be validated before being pushed! It is also a good
idea to validate after changes to *any* component of the system.

# Performance testing

There are a number of scripts that will automatically run the WiFi performance
tests, generating a CSV file performance data. The performance tests can be run
for Ziria by invoking the `perf-ziria.sh` script with the path to the Ziria WiFi
implementation, e.g.,

    ./perf-ziria.sh ~/projects/ziria/Ziria/code/WiFi/

The other perf scripts, e.g., `perf-wifi.sh` and `perf-wifi-sid.sh` should be
run with no additional arguments.
