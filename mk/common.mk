MAKEFLAGS:=--no-print-directory

_QUIET=@

CC=gcc
CXX=g++
LD=gcc

CPPFLAGS+=-I$(TOP)/libkz/include
CFLAGS+=-msse4

CCFLAGS=-std=gnu99
CXXFLAGS=-std=c++11

LDFLAGS=

LIBS=-lm -lpthread

GHC=ghc
GHCFLAGS=-O -Wall -fno-warn-name-shadowing -Werror

RUNGHC=runghc
RUNGHCFLAGS=-W -fno-warn-unused-imports

HAPPY=happy 
HAPPY_ARGS=-agci

ALEX=alex 
ALEX_ARGS=-gi

#
# No built-in rules
#
MAKEFLAGS += --no-builtin-rules

#
# quiet and noquiet make commands
#
ifeq ($(filter quiet, $(MAKECMDGOALS)), quiet)
VIRTUAL_GOALS += quiet
QUIET := 1
endif

MAKECMDGOALS := $(filter-out quiet, $(MAKECMDGOALS))

ifeq ($(filter noquiet, $(MAKECMDGOALS)), noquiet)
VIRTUAL_GOALS += noquiet
NOQUIET := 1
endif

MAKECMDGOALS := $(filter-out noquiet, $(MAKECMDGOALS))

ifeq ($(QUIET), 1)
_QUIET = @
endif

ifeq ($(NOQUIET), 1)
_QUIET = 
endif

#
# opt and noopt make commands
#
ifeq ($(filter opt, $(MAKECMDGOALS)), opt)
VIRTUAL_GOALS += opt
OPT := 1
endif

MAKECMDGOALS := $(filter-out opt, $(MAKECMDGOALS))

ifeq ($(filter noopt, $(MAKECMDGOALS)), noopt)
VIRTUAL_GOALS += noopt
NOOPT := 1
endif

MAKECMDGOALS := $(filter-out noopt, $(MAKECMDGOALS))

#
# GHC optimization flags
#
GHCFLAGS_OPT = -O2 -funbox-strict-fields

ifeq ($(OPT), 1)
GHCFLAGS += $(GHCFLAGS_OPT)
endif

#
# Support cabal sandbox
#
ifneq ($(wildcard $(TOP)/.cabal-sandbox/*-packages.conf.d),)
GHCFLAGS += \
	-no-user-package-db \
	-package-db $(wildcard $(TOP)/.cabal-sandbox/*-packages.conf.d)

RUNGHCFLAGS += \
	-no-user-package-db \
	-package-db --ghc-arg=$(wildcard $(TOP)/.cabal-sandbox/*-packages.conf.d)
endif

#
# Support Cabal's MIN_VERSION
#
RUNGHCFLAGS += -optP-include -optP$(TOP)/dist/build/autogen/cabal_macros.h
GHCFLAGS += -optP-include -optP$(TOP)/dist/build/autogen/cabal_macros.h

#
# BlinkDiff
#

BLINKDIFF=$(TOP)/dist/build/BlinkDiff/BlinkDiff

$(BLINKDIFF) : $(TOP)/tools/BlinkDiff.hs
	$(_QUIET)cd $(TOP) && cabal build BlinkDiff

#
# Ziria Executables
#
TESTDIR = $(TOP)/testsuite

KZC=$(TOP)/kzc
KZCFLAGS+=-I$(TESTDIR)/lib --dlint --dauto-lint --ddump-core --ddump-lift --ddump-auto --ddump-fusion  --ddump-simpl --dprint-uniques --fno-line-pragmas

RUNTIME_SRC=\
	$(TOP)/libkz/src/bits.c \
	$(TOP)/libkz/src/driver.c \
	$(TOP)/libkz/src/ext.c \
	$(TOP)/libkz/src/io.cpp \
	$(TOP)/libkz/src/threads.c \
	$(TOP)/libkz/src/sora/kz_sora.cpp

RUNTIME_OBJ=$(patsubst %.cpp,%.o,$(patsubst %.c,%.o,$(RUNTIME_SRC)))

.PRECIOUS : $(RUNTIME_OBJ)

%.c : %.blk $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) $< -o $@

%.c : %.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) $< -o $@

%.c : %.zr $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) $< -o $@

%.o : %.c
	$(_QUIET)$(CC) $(CPPFLAGS) $(CCFLAGS) $(CFLAGS) -c $< -o $@

%.o : %.cpp
	$(_QUIET)$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(CFLAGS) -c $< -o $@

%.exe : %.o $(RUNTIME_OBJ)
	$(_QUIET)$(LD) $(LDFLAGS) $< $(RUNTIME_OBJ) $(LIBS) -o $@

bin_%.outfile: bin_%.exe bin_%.infile
	$(_QUIET)./$< \
	     --input=$(shell dirname $*.infile)/bin_$(shell basename $*.infile) \
             --output=$@ \
             --input-mode=bin \
             --output-mode=bin

bin_%.outfile: bin_%.exe
	$(_QUIET)./$< \
             --output=$@ \
             --output-mode=bin

%.outfile : %.exe %.infile
	$(_QUIET)./$< \
	     --input=$*.infile \
	     --output=$@

%.outfile : %.exe
	$(_QUIET)./$< \
	     --output=$@

#
# Print Makefile variables
#
print-%: ; @echo $*=$($*)

#
# Rules for virtual goals
#
ifeq ($(MAKECMDGOALS),)
$(VIRTUAL_GOALS) : all
	@true
else
$(VIRTUAL_GOALS) :
	@true
endif
