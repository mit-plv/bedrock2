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
	$(MAKE) src/BytedumpTest.out

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(VS) -o Makefile.coq.all

src/BytedumpTest.out: src/BytedumpTest.v src/BytedumpTest.golden.bin
	coqc -q $(shell cat _CoqProject | grep -v ^-arg) $< | head --bytes -1 > src/BytedumpTest.out.tmp
	hexdump < /dev/null && \
		hexdump -C src/BytedumpTest.golden.bin > src/BytedumpTest.golden.hex && \
		hexdump -C src/BytedumpTest.out.tmp > src/BytedumpTest.out.hex && \
		diff -u src/BytedumpTest.golden.hex src/BytedumpTest.out.hex && \
		rm src/BytedumpTest.golden.hex src/BytedumpTest.out.hex || true
	diff -u src/BytedumpTest.golden.bin src/BytedumpTest.out.tmp
	mv src/BytedumpTest.out.tmp src/BytedumpTest.out

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject
