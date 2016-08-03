WHOLEPROGRAM=1
include $(TOP)/mk/common.mk

KZCFLAGS := -ftimers -finline -fsimpl -fautolut -flut -ffuse -fpeval -fcoalesce-top -fcoalesce -Wno-unsafe-auto-cast $(KZCFLAGS)

ifeq ($(GCC), 1)
CFLAGS+=-pipe -march=native -mtune=native -Ofast -ggdb
LDFLAGS+=-ggdb
endif

ifeq ($(CLANG), 1)
CFLAGS+=-march=native -Ofast -ggdb
LDFLAGS+=-ggdb
endif

ifeq ($(ICC), 1)
CFLAGS+=-march=native -Ofast -ggdb
LDFLAGS+=-ggdb
endif

.PHONY : clean
clean :
	$(_QUIET)rm -f \
	      $(patsubst %.blk, %.c, $(TESTS)) \
	      $(patsubst %.blk, %.exe, $(TESTS)) \
	      $(patsubst %.blk, %.outfile, $(TESTS)) \
	      $(patsubst %.blk, %.dump*, $(TESTS))

%.perf : %.exe
	./$< --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=100000000

.PHONY : perf.all
perf.all :
	$(MAKE) all | awk -f $(TOP)/testsuite/code/WiFi/perf/perf.awk | sort >$@

%.amplxe : %.exe
	amplxe-cl -collect hotspots -collect general-exploration -- ./$< \
	     --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=10000000000

%.advixe : %.exe
	advixe-cl --collect survey -- ./$< \
	     --input-dev=dummy \
             --output-dev=dummy \
	     --dummy-samples=10000000000
