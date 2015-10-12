TOP=../../..

TESTS=$(shell ls *.wpl | sort)

.PHONY : all
all : $(patsubst %.wpl, %.test, $(TESTS))

include $(TOP)/mk/common.mk

.PHONY : clean
clean :
	$(_QUIET)rm -f \
	      $(patsubst %.wpl, %.c, $(TESTS)) \
	      $(patsubst %.wpl, %.exe, $(TESTS)) \
	      $(patsubst %.wpl, %.outfile, $(TESTS)) \
	      $(patsubst %.wpl, %.dump*, $(TESTS))
