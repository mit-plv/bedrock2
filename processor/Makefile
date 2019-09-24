default_target: all

.PHONY: clean force all

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q ./src/processor processor\n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	printf -- '$(DEPFLAGS_NL)' > _CoqProject

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

DEPS_DIR ?= $(ABS_ROOT_DIR)/../deps

EXTERNAL_DEPENDENCIES?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)
# N.B. We should be using ; instead of : iff we are on Windows AND the ocaml we are using was NOT compiled with cygwin...
# We will instead wait until someone complains that make is not working on Windows and then have them figure out a way to detect this case
# Note that Windows users can always manually set COQPATH, so always using : does not make it impossible to build on Windows, just a bit of a pain.
COQPATH?=$(DEPS_DIR)/coqutil/src:$(DEPS_DIR)/riscv-coq/src:$(DEPS_DIR)/kami
export COQPATH
endif

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/processor
ALL_VS := $(shell find $(SRCDIR) -type f -name '*.v')

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject
