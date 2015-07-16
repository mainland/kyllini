GHC=ghc
GHCFLAGS=-W -Werror

RUNGHC=runghc
RUNGHCFLAGS=-W -Werror

HAPPY=happy 
HAPPY_ARGS=-agci

ALEX=alex 
ALEX_ARGS=-gi

#
# opt and noopt make commands
#
OPT_MAKECMD := $(filter opt, $(MAKECMDGOALS))
MAKECMDGOALS := $(filter-out opt, $(MAKECMDGOALS))

NOOPT_MAKECMD := $(filter noopt, $(MAKECMDGOALS))
MAKECMDGOALS := $(filter-out noopt, $(MAKECMDGOALS))

ifeq ($(OPT_MAKECMD), opt)
VIRTUAL_GOALS += opt

OPT_MAKECMD := 1
OPT := 1
else
OPT_MAKECMD := 0
OPT := 0
endif

ifeq ($(NOOPT_MAKECMD), noopt)
VIRTUAL_GOALS += noopt

NOOPT_MAKECMD := 1
NOOPT := 1
else
NOOPT_MAKECMD := 0
endif

#
# Support cabal sandbox
#
ifneq ($(wildcard .cabal-sandbox/*-packages.conf.d),)
GHCFLAGS += \
	-no-user-package-db \
	-package-db $(wildcard .cabal-sandbox/*-packages.conf.d)

RUNGHCFLAGS += \
	-no-user-package-db \
	-package-db --ghc-arg=$(wildcard .cabal-sandbox/*-packages.conf.d)
endif

GHCFLAGS_OPT = -O2 -funbox-strict-fields

ifeq ($(OPT), 1)
GHCFLAGS += $(GHCFLAGS_OPT)
endif

GHCFLAGS += \
	-hide-all-packages \
	-package array \
	-package base \
	-package binary \
	-package bytestring \
	-package containers \
	-package directory \
	-package exception-mtl \
	-package exception-transformers \
	-package filepath \
	-package mainland-pretty \
	-package mtl \
	-package ref-fd \
	-package srcloc \
	-package syb \
	-package symbol \
	-package text \
	-package transformers

SRCDIR = src/

GHCFLAGS+=-i$(SRCDIR) -I$(SRCDIR)
RUNGHCFLAGS+=-i$(SRCDIR) -I$(SRCDIR)

SOURCE = \
	KZC/Check/Monad.hs \
	KZC/Check/State.hs \
	KZC/Check/Types.hs \
	KZC/Derive.hs \
	KZC/Error.hs \
	KZC/Flags.hs \
	KZC/Monad.hs \
	KZC/Name.hs \
	KZC/Pretty.hs \
	KZC/Summary.hs \
	KZC/Uniq.hs \
	KZC/Util/SetLike.hs \
	KZC/Vars.hs \
	Language/Core/Syntax.hs \
	Language/Ziria/Parser/Alex.hs \
	Language/Ziria/Parser/Exceptions.hs \
	Language/Ziria/Parser/Lexer.hs \
	Language/Ziria/Parser/Monad.hs \
	Language/Ziria/Parser/Tokens.hs \
	Language/Ziria/Parser.hs \
	Language/Ziria/Smart.hs \
	Language/Ziria/Syntax.hs \
	Main.hs \
	Opts.hs

GENERATED = \
	KZC/Check/Types-instances.hs \
	Language/Core/Syntax-instances.hs \
	Language/Ziria/Parser/Lexer.hs \
	Language/Ziria/Parser/Parser.hs \
	Language/Ziria/Syntax-instances.hs

SRC = $(patsubst %,$(SRCDIR)%,$(SOURCE)) $(patsubst %,$(SRCDIR)%,$(GENERATED))

.PHONY : all
all : kzc

.PHONY : clean
clean :
	rm -rf kzc obj $(patsubst %,$(SRCDIR)%,$(GENERATED))

$(SRCDIR)KZC/Check/Types-instances.hs : bin/gen-tc-instances.hs $(SRCDIR)KZC/Derive.hs $(SRCDIR)KZC/Check/Types.hs
	runhaskell $(RUNGHCFLAGS) $< > $@

$(SRCDIR)Language/Core/Syntax-instances.hs : bin/gen-core-instances.hs $(SRCDIR)KZC/Derive.hs $(SRCDIR)Language/Core/Syntax.hs
	runhaskell $(RUNGHCFLAGS) $< > $@

$(SRCDIR)Language/Ziria/Parser/Parser.hs : $(SRCDIR)Language/Ziria/Parser/Parser.y
	$(HAPPY) $(HAPPY_ARGS) -o $@ $<

$(SRCDIR)Language/Ziria/Parser/Lexer.hs : $(SRCDIR)Language/Ziria/Parser/Lexer.x
	$(ALEX) $(ALEX_ARGS) -o $@ $<

$(SRCDIR)Language/Ziria/Syntax-instances.hs : bin/gen-ziria-instances.hs $(SRCDIR)KZC/Derive.hs $(SRCDIR)Language/Ziria/Syntax.hs
	runhaskell $(RUNGHCFLAGS) $< > $@

kzc : $(SRC)
	@mkdir -p obj
	$(GHC) $(GHCFLAGS) --make $(SRCDIR)Main.hs -odir obj -hidir obj \
		-o $@

TESTS = \
	$(shell find tests -name '*.wpl') \
	$(wildcard code/WiFi/tests/*.blk) \
	$(wildcard code/WiFi/transmitter/tests/*.blk) \
	$(wildcard code/WiFi/receiver/tests/*.blk)

TESTSEXPANDED = $(patsubst %,%.expanded,$(TESTS))

%.expanded : %
	gcc -I lib -I tests/WiFi -I tests/WiFi/perf/blocks -w -x c -E $< >$@

.PHONY : test-parser
test-parser : kzc $(TESTSEXPANDED)
	set -e; \
	for TEST in $(TESTSEXPANDED); do \
		./kzc $$TEST; \
	done

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
