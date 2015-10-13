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

test_real_%.outfile: test_real_%.out test_real_%.infile
	./$< --input=test_real_$*.infile \
             --input-mode=bin \
             --output=$@ \
             --output-mode=text

# test multiple encdec tests with the same exe
test_encdec%.outfile: test_encdec.out test_encdec%.infile
	./test_encdec.out \
             --input=test_encdec$*.infile \
             --input-mode=text \
             --output-name=$@ \
             --output-mode=text

%.outfile: %.out %.infile
	./$< --input=$*.infile \
             --input-mode=text \
             --output=$@ \
             --output-mode=text

# We remove -p (ignore endings) from tests to detect subtle errors For example,
# if no packet is detected, there is no output, and -p treats that as correct
%.test : %.outfile %.outfile.ground
	@echo "Comparing output for" $*
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -n 0.81 -t 105
