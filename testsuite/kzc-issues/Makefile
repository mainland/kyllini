TOP=../..

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

issue03.c : issue03.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -fpeval $< -o $@

issue04.c : issue04.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -finline -fsimpl $< -o $@

issue05.c : issue05.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -finline -fsimpl $< -o $@

issue07.c : issue07.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -finline -fsimpl -fpeval $< -o $@

issue07-simplified.c : issue07-simplified.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -finline -fsimpl -fpeval $< -o $@

issue09.c : issue09.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -finline -fsimpl -fpeval -fautolut -flut $< -o $@

issue16.c : issue16.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse $< -o $@

issue48.c : issue48.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -fpipeline $< -o $@

issue49.c : issue49.wpl $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -O3 $< -o $@

issue52.c : issue52.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -fsimpl $< -o $@

fuse01.c : fuse01.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse02.c : fuse02.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse03.c : fuse03.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse04.c : fuse04.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse05.c : fuse05.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse06.c : fuse06.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse07.c : fuse07.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse08.c : fuse08.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -i../lib -ffuse -fsimpl $< -o $@

fuse09.c : fuse09.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse10.c : fuse10.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse11.c : fuse11.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@

fuse12.c : fuse12.kz $(KZC)
	$(_QUIET)$(KZC) $(KZCFLAGS) -ffuse -fsimpl $< -o $@
