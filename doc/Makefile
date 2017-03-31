DOT ?= dot

TARGETS = figs/classes.svg

.PHONY : all
all : $(TARGETS)

.PHONY : clean
clean :
	@rm -f $(TARGETS)

%.svg : %.dot
	$(DOT) -Tsvg -o $@ $< || rm -f $@

%.svgz : %.dot
	$(DOT) -Tsvgz -o $@ $< || rm -f $@
