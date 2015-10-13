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


# Test with complex outputs - set precision and threshold (to ignore
# discrepancies in small values)
test_c_%.test: test_c_%.outfile
	@echo "Comparing output for" test_c_$*
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.8 -c -t 20

# We remove -p (ignore endings) from tests to detect subtle errors For example,
# if no packet is detected, there is no output, and -p treats that as correct
%.test : %.outfile %.outfile.ground
	@echo "Comparing output for" $*
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.9
