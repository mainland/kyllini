#!/bin/sh
git submodule init
git submodule update
(cd ziria && cabal sandbox init && cabal install --only-dependencies --force-reinstalls && make)
autoreconf -i
cabal sandbox init
cabal install --only-dependencies
cabal build
make
