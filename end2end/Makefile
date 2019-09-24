default_target: all

.PHONY: clean force all all0 admitsCount

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n-Q $(DEPS_DIR)/riscv-coq/src/riscv riscv\n-R $(DEPS_DIR)/kami/Kami/ Kami\n-Q ../processor/src/processor processor\n-Q ../bedrock2/src/bedrock2 bedrock2\n-Q ../compiler/src/compiler compiler\n
CURFLAGS_NL=-Q ./src/end2end end2end\n

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

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/end2end
ALL_VS := $(shell find $(SRCDIR) -type f -name '*.v')

all0: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = end2end $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject
	rm -f admits.txt PrintAdmits.vo admits1perLine.txt

admits.txt: all0 PrintAdmits.v
	$(COQBIN)coqc $(ALLDEPFLAGS) PrintAdmits.v > admits.txt

admits1perLine.txt: admits.txt
	grep admits.txt -e '^[^ ]* : ' -e 'used in' | grep -v '^[^ ]*TODO : False' | sed -e 's/:.*//g' > admits1perLine.txt

admitsCount: admits1perLine.txt
	@printf -- 'Number of admits: '
	@cat admits1perLine.txt | wc -l

all: all0 admitsCount
