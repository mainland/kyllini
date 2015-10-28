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
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9 -o 1.0

test_x_%.test: test_x_%.outfile
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9 -o 1.0 -t 25.1

%.test: %.outfile
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9
