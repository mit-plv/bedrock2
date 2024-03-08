default_target: all

.PHONY: clean force all

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/LiveVerifCompile

VS:=$(shell find $(SRCDIR) -type f -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_NL=
CURFLAGS_NL=-Q ../bedrock2/src/bedrock2 bedrock2\n-Q ../compiler/src/compiler compiler\n-Q ../deps/riscv-coq/src/riscv riscv\n-Q ../LiveVerif/src/LiveVerif LiveVerif\n-Q ../LiveVerif/src/LiveVerifExamples LiveVerifExamples\n-Q src/LiveVerifCompile LiveVerifCompile\n

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

all: Makefile.coq $(VS)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject -docroot LiveVerifCompile $(COQMF_ARGS)

Makefile.coq: force _CoqProject
	@echo "Generating Makefile.coq"
	@$(COQ_MAKEFILE) $(VS) -o Makefile.coq

force:

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf _CoqProject
