#
# Virtual goals
#

# quiet and noquiet virtual targets
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

# opt and noopt virtual targets
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

# compiler virtual targets
ifeq ($(filter gcc, $(MAKECMDGOALS)), gcc)
VIRTUAL_GOALS += gcc
GCC := 1
endif

MAKECMDGOALS := $(filter-out gcc, $(MAKECMDGOALS))

ifeq ($(filter clang, $(MAKECMDGOALS)), clang)
VIRTUAL_GOALS += clang
CLANG := 1
endif

MAKECMDGOALS := $(filter-out clang, $(MAKECMDGOALS))

ifneq ($(CLANG), 1)
GCC := 1
endif
