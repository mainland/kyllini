# Building `kzc`

`kzc` is developed using GHC 7.10, although it should compile with minor changes
under 7.8 and 8.0. It does require `autoconf`; when building under Windows,
[msys2](https://msys2.github.io/) should be used.

The compiler can be built as follows:

    autoconf && ./configure && make

# Validating changes

The `validate` scripts runs the test suite with a large number of optimization
flag combinations. Running it is as simple as executing

    ./validate

Extra flags can be passed to the compiler during validation by setting the
`KZCFLAGS` environment variable.
