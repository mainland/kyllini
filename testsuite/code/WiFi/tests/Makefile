TOP=../../../..

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

# test multiple encdec tests with the same exe
test_encdec%.outfile: test_encdec.exe test_encdec%.infile
	./$< \
             --input=test_encdec$*.infile \
             --input-mode=text \
             --output=$@ \
             --output-mode=text

# We remove -p (ignore endings) from tests to detect subtle errors For example,
# if no packet is detected, there is no output, and -p treats that as correct
%.test : %.outfile %.outfile.ground
	@echo "Comparing output for" $*
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.81 -t 105
