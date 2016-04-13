TOP=../../../..

TESTS=$(shell ls *.blk | sort)

.PHONY : all
all : $(patsubst %.blk, %.perf, $(TESTS))

WHOLEPROGRAM=1
include $(TOP)/mk/common.mk

KZCFLAGS+=--ftimer --fautolut --flut
CFLAGS+=-march=native -mtune=native -Ofast -pipe
LDFLAGS+=-march=native -mtune=native -Ofast

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
