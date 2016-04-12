TOP=../../..

GROUNDFILES=$(shell ls *.outfile.ground | sort)

.PHONY : all
all : $(patsubst %.outfile.ground, %.test, $(GROUNDFILES))

include $(TOP)/mk/common.mk

.PHONY : clean
clean :
	$(_QUIET)rm -f \
	      $(patsubst %.outfile.ground, %.c, $(GROUNDFILES)) \
	      $(patsubst %.outfile.ground, %.exe, $(GROUNDFILES)) \
	      $(patsubst %.outfile.ground, %.outfile, $(GROUNDFILES)) \
	      $(patsubst %.outfile.ground, %.dump*, $(GROUNDFILES))

%.test : %.outfile %.outfile.ground
	@echo "Comparing output for" $*
	$(_QUIET)$(BLINKDIFF) -f $< -g $<.ground -d -v -p
