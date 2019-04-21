default_target: all

.PHONY: clean force all

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src

VS:=$(shell find $(SRCDIR) -type f -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q src bedrock2\n-Q $(DEPS_DIR)/coqutil/src coqutil\n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	printf -- '$(DEPFLAGS_NL)' > _CoqProject

all: Makefile.coq.all $(VS)
	$(MAKE) -f Makefile.coq.all
	$(MAKE) special/BytedumpTest.out

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(VS) -o Makefile.coq.all

special/BytedumpTest.out: special/BytedumpTest.v special/BytedumpTest.golden.bin
	coqc -q $(shell cat _CoqProject | grep -v ^-arg) $< | head --bytes -1 > special/BytedumpTest.out.tmp
	hexdump < /dev/null && \
		hexdump -C special/BytedumpTest.golden.bin > special/BytedumpTest.golden.hex && \
		hexdump -C special/BytedumpTest.out.tmp > special/BytedumpTest.out.hex && \
		diff -u special/BytedumpTest.golden.hex special/BytedumpTest.out.hex && \
		rm special/BytedumpTest.golden.hex special/BytedumpTest.out.hex || true
	diff -u special/BytedumpTest.golden.bin special/BytedumpTest.out.tmp
	mv special/BytedumpTest.out.tmp special/BytedumpTest.out

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject
