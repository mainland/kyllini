TOP=../../../../..

TESTS=$(shell ls *.outfile.ground | sort)

.PHONY : all
all : $(patsubst %.outfile.ground, %.test, $(TESTS))

include $(TOP)/mk/common.mk

.PHONY : clean
clean :
	$(_QUIET)rm -f \
	      $(patsubst %.outfile.ground, %.c, $(TESTS)) \
	      $(patsubst %.outfile.ground, %.exe, $(TESTS)) \
	      $(patsubst %.outfile.ground, %.outfile, $(TESTS)) \
	      $(patsubst %.outfile.ground, %.dump*, $(TESTS))

test_c_%.test: test_c_%.outfile
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9 -t 220

%.test: %.outfile
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9
