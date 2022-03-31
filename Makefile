# Makefile originally based off of one from coq-club, also borrowing from fiat-crypto and bedrock2's Makefiles

# use cygpath -m because Coq on Windows cannot handle cygwin paths
LIBDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola/Lib
ALLDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola

# use git ls-files if we can to avoid building non-checked-in cruft;
# use find when building from a tarball
ifneq (,$(wildcard .git/))
find_vs = $(shell git ls-files "$(1)/*.v")
else
find_vs = $(shell find "$(1)" -type f -name '*.v')
endif
# absolute paths so that emacs compile mode knows where to find error
VS_LIB:=$(abspath $(call find_vs,$(LIBDIR)))
VS_ALL:=$(abspath $(call find_vs,$(ALLDIR)))

all: Makefile.coq $(VS_ALL)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq

lib: Makefile.coq.lib $(VS_LIB)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.lib

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = Rupicola $(COQMF_ARGS)

force:

Makefile.coq.lib: force _CoqProject
	@echo "Generating Makefile.coq.lib"
	@$(COQ_MAKEFILE) $(VS_LIB) -o Makefile.coq.lib

Makefile.coq: force _CoqProject
	@echo "Generating Makefile.coq"
	@$(COQ_MAKEFILE) $(VS_ALL) -o Makefile.coq

clean:: Makefile.coq.lib Makefile.coq
	$(MAKE) -f Makefile.coq.lib clean
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.lib Makefile.coq.lib.conf Makefile.coq Makefile.coq.conf _CoqProject

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=
EXTERNAL_BEDROCK2?=

COQUTIL_FOLDER := bedrock2/deps/coqutil
BEDROCK2_FOLDER := bedrock2/bedrock2

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(COQUTIL_FOLDER)/src/coqutil coqutil\n
DEPFLAGS_BEDROCK2_NL=-Q $(BEDROCK2_FOLDER)/src/bedrock2 bedrock2\n
CURFLAGS_NL=-R src/Rupicola Rupicola\n-arg -w\n-arg -unexpected-implicit-declaration,-deprecated-ident-entry\n
DEPFLAGS_NL=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

ifneq ($(EXTERNAL_BEDROCK2),1)
DEPFLAGS_NL+=$(DEPFLAGS_BEDROCK2_NL)
endif

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ifneq ($(EXTERNAL_DEPENDENCIES),1)

ifneq ($(EXTERNAL_COQUTIL),1)
bedrock2: coqutil
install install_lib: install_coqutil
endif

ifneq ($(EXTERNAL_BEDROCK2),1)
install install_lib: install_bedrock2
all: bedrock2
deps: bedrock2
%.vo: bedrock2
endif

endif

coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER)

clean_coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) clean

install_coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) install

bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) noex

clean_bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) clean

install_bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) install

cleanall: clean clean_coqutil clean_bedrock2

%.vo: deps Makefile.coq
	+$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

install_lib: Makefile.coq.lib
	+$(MAKE) -f Makefile.coq.lib install

_CoqProject:
	@printf -- '$(ALLDEPFLAGS_NL)' > _CoqProject

Makefile: ;

phony: ;

.PHONY: all lib clean phony base coqutil clean_coqutil install_coqutil bedrock2 clean_bedrock2 install_bedrock2 install install_lib deps cleanall _CoqProject
