default_target: all

.PHONY: clean force all noex ex install

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/bedrock2
EXDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/bedrock2Examples

VS_NOEX:=$(shell find $(SRCDIR) -type f -name '*.v')
VS_EX:=$(shell find $(EXDIR) -type f -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
CURFLAGS_NL=-Q src/bedrock2 bedrock2\n-Q src/bedrock2Examples bedrock2Examples\n

EXTERNAL_DEPENDENCIES?=

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ALLDEPFLAGS=$(subst \n, ,$(ALLDEPFLAGS_NL))

_CoqProject:
	printf -- '$(ALLDEPFLAGS_NL)' > _CoqProject

noex: Makefile.coq.noex $(VS_NOEX)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.noex

ex: Makefile.coq.ex $(VS_EX) noex
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.ex

all: noex ex special/BytedumpTest.out

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.noex: force _CoqProject
	@echo "Generating Makefile.coq.noex"
	@$(COQ_MAKEFILE) $(VS_NOEX) -o Makefile.coq.noex

Makefile.coq.ex: force _CoqProject
	@echo "Generating Makefile.coq.ex"
	@$(COQ_MAKEFILE) $(VS_EX) -o Makefile.coq.ex

special/BytedumpTest.out: special/BytedumpTest.v special/BytedumpTest.golden.bin noex
	coqc -q $(ALLDEPFLAGS) $< > special/BytedumpTest.out.tmp0
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

clean:: Makefile.coq.noex Makefile.coq.ex
	$(MAKE) -f Makefile.coq.noex clean
	$(MAKE) -f Makefile.coq.ex clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.noex Makefile.coq.noex.conf Makefile.coq.ex Makefile.coq.ex.conf _CoqProject special/BytedumpTest.out

install::
	$(MAKE) -f Makefile.coq.noex install
