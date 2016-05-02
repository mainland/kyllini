TOP=../../../..

TESTS=$(shell ls *.blk | sort)

.PHONY : all
all : $(patsubst %.blk, %.perf, $(TESTS))

WHOLEPROGRAM=1
include $(TOP)/mk/common.mk

KZCFLAGS+=--ftimer --fautolut --flut --ffuse

ifeq ($(GCC), 1)
CFLAGS+=-pipe -march=native -Ofast -g
endif

ifeq ($(CLANG), 1)
CFLAGS+=-march=native -Ofast -g
endif

ifeq ($(ICC), 1)
CFLAGS+=-march=native -Ofast -g
endif

.PHONY : clean
clean :
	$(_QUIET)rm -f \
	      $(patsubst %.blk, %.c, $(TESTS)) \
	      $(patsubst %.blk, %.exe, $(TESTS)) \
	      $(patsubst %.blk, %.outfile, $(TESTS)) \
	      $(patsubst %.blk, %.dump*, $(TESTS))

%.perf : %.exe 
	./$< --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=100000000

%.amplxe : %.exe
	amplxe-cl -collect hotspots -collect general-exploration -- ./$< \
	     --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=10000000000

%.advixe : %.exe
	advixe-cl --collect survey -- ./$< \
	     --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=10000000000
