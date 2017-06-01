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

```
./validate
```

Extra flags can be passed to the compiler during validation by setting the
`KZCFLAGS` environment variable.

All compiler changes should be validated before being pushed! It is also a good
idea to validate after changes to *any* component of the system.

# Performance testing

Instructions for running performance tests are in the [README in the `perf` directory](perf/README.md).
