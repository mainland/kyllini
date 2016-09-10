MAKEFLAGS:=--no-print-directory

_QUIET=@

include $(TOP)/mk/virtual.mk

#
# No built-in rules
#
MAKEFLAGS += --no-builtin-rules

#
# Pick compiler
#
ifeq ($(GCC), 1)
CC=gcc
CXX=g++
LD=gcc
endif

ifeq ($(CLANG), 1)
CC=clang
CXX=clang++
LD=clang
endif

ifeq ($(ICC), 1)
CC=icc
CXX=icpc
LD=icc
endif

ifeq ($(SANITIZE), 1)
ifeq ($(CLANG), 1)
SANITIZEFLAGS+=-fsanitize=address -fsanitize=leak -fsanitize=undefined -fno-sanitize-recover=undefined,integer
CFLAGS+=$(SANITIZEFLAGS)
LDFLAGS+=$(SANITIZEFLAGS)
LIBS+=-lstdc++
endif

ifeq ($(GCC), 1)
SANITIZEFLAGS+=-fsanitize=address
CFLAGS+=$(SANITIZEFLAGS)
LDFLAGS+=$(SANITIZEFLAGS)
endif
endif

#
# Whole program
#
ifeq ($(WHOLEPROGRAM), 1)
CPPFLAGS+=-DWHOLEPROGRAM -I$(TOP)/libkz/src

ifeq ($(GCC), 1)
CFLAGS+=-fwhole-program
endif
endif

#
# Misc flags
#
CPPFLAGS+=-I$(TOP)/include -I$(TOP)/libkz/include
CFLAGS+=-msse4

CCFLAGS+=-std=gnu99
CXXFLAGS+=-std=c++11

LDFLAGS+=

LIBS+=-lm -lpthread -lstdc++

GHC=ghc
GHCFLAGS+=-XHaskell2010 -rtsopts -O -Wall -fno-warn-name-shadowing -Werror

RUNGHC=runghc
RUNGHCFLAGS+=-W -fno-warn-unused-imports

HAPPY=happy
HAPPYFLAGS+=-agci

ALEX=alex
ALEXFLAGS+=-gi

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
# Profiling
#

%.ps : %.hp
	hp2ps -c $^ >$@

%.pdf : %.ps
	ps2pdf $^ $@

%.folded : %.prof
	cat $^ | ghc-prof-flamegraph >$@

%.svg : %.folded
	cat $^ | flamegraph.pl >$@

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

KZC?=$(TOP)/kzc
KZCFLAGS := -I$(TESTDIR)/lib -dlint -dprint-uniques -fno-line-pragmas $(KZCFLAGS)

RUNTIME_SRC=\
	$(TOP)/libkz/src/bits.c \
	$(TOP)/libkz/src/driver.c \
	$(TOP)/libkz/src/ext.c \
	$(TOP)/libkz/src/ext_zira.c \
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

%.s : %.exe
	$(_QUIET)objdump -S -C -d $< > $@

%.o : %.c
	$(_QUIET)$(CC) $(CPPFLAGS) $(CCFLAGS) $(CFLAGS) -c $< -o $@

%.o : %.cpp
	$(_QUIET)$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(CFLAGS) -c $< -o $@

ifeq ($(WHOLEPROGRAM), 1)
%.exe : %.c $(RUNTIME_SRC)
	$(_QUIET)$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(CFLAGS) $< $(LIBS) -o $@
else
%.exe : %.o $(RUNTIME_OBJ)
	$(_QUIET)$(LD) $(LDFLAGS) $< $(RUNTIME_OBJ) $(LIBS) -o $@
endif

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
