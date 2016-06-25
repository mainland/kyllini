TOP=../../../../..

TESTS=$(shell ls *.blk | sort)

.PHONY : all
all : $(patsubst %.blk, %.perf, $(TESTS))

include $(TOP)/mk/perf.mk
