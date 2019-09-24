default_target: all

.PHONY: clean force all all_coqmakefile

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/bedrock2

VS:=$(shell find $(SRCDIR) -type f -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q src/bedrock2 bedrock2\n-Q $(DEPS_DIR)/coqutil/src coqutil\n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	printf -- '$(DEPFLAGS_NL)' > _CoqProject

all_coqmakefile: Makefile.coq.all $(VS)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.all

all: all_coqmakefile special/BytedumpTest.out

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(VS) -o Makefile.coq.all

special/BytedumpTest.out: special/BytedumpTest.v special/BytedumpTest.golden.bin all_coqmakefile
	coqc -q $(DEPFLAGS) $< > special/BytedumpTest.out.tmp0
	head -c $$(($$(wc -c < special/BytedumpTest.out.tmp0 | xargs) - 1)) special/BytedumpTest.out.tmp0 > special/BytedumpTest.out.tmp
	rm special/BytedumpTest.out.tmp0
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
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject special/BytedumpTest.out
