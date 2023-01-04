default_target: all

.PHONY: clean force all noex ex install_noex install_ex install test

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/LiveVerif
EXDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/LiveVerifExamples

VS_NOEX:=$(shell find $(SRCDIR) -type f -name '*.v' -and -not -name LiveVerif.v)
VS_EX:=$(shell find $(EXDIR) -type f -name '*.v')

CC ?= cc
DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_NL=
CURFLAGS_NL=-Q ../bedrock2/src/bedrock2 bedrock2\n-Q src/LiveVerif LiveVerif\n-Q src/LiveVerifExamples LiveVerifExamples\n

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

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

all: noex ex

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = LiveVerif $(COQMF_ARGS)

Makefile.coq.noex: force _CoqProject
	@echo "Generating Makefile.coq.noex"
	@$(COQ_MAKEFILE) $(VS_NOEX) -o Makefile.coq.noex

Makefile.coq.ex: force _CoqProject
	@echo "Generating Makefile.coq.ex"
	@$(COQ_MAKEFILE) $(VS_EX) -o Makefile.coq.ex

force:

clean:: Makefile.coq.noex Makefile.coq.ex
	$(MAKE) -f Makefile.coq.noex clean
	$(MAKE) -f Makefile.coq.ex clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.noex Makefile.coq.noex.conf Makefile.coq.ex Makefile.coq.ex.conf _CoqProject

install_noex::
	$(MAKE) -f Makefile.coq.noex install

install_ex::
	$(MAKE) -f Makefile.coq.ex install

install:: install_noex install_ex
