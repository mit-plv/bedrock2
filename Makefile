# Makefile originally based off of one from coq-club, also borrowing from fiat-crypto and bedrock2's Makefiles

COQPATH?=$(COQUTIL_FOLDER)/src:$(BEDROCK2_FOLDER)/src
export COQPATH

# use cygpath -m because Coq on Windows cannot handle cygwin paths
LIBDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola/Lib
ALLDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola

# absolute paths so that emacs compile mode knows where to find error
VS_LIB:=$(shell git ls-files $(LIBDIR) | xargs readlink -f | grep "\.v")
VS_ALL:=$(shell git ls-files $(ALLDIR) | xargs readlink -f | grep "\.v")

all: deps Makefile.coq $(VS_ALL)
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

COQUTIL_FOLDER := bedrock2/deps/coqutil
BEDROCK2_FOLDER := bedrock2/bedrock2

coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) 

clean-coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) clean

bedrock2: coqutil
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) noex

clean-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) clean

deps: bedrock2

cleanall: clean clean-coqutil clean-bedrock2

%.vo: deps Makefile.coq
	+make -f Makefile.coq $@

_CoqProject:
	@echo "-R src/Rupicola Rupicola" > _CoqProject
	@echo "-Q bedrock2/bedrock2/src/bedrock2 bedrock2" >> _CoqProject
	@echo "-Q bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject

Makefile: ;

phony: ;

.PHONY: all lib clean phony base coqutil clean-coqutil bedrock2 clean-bedrock2 deps cleanall _CoqProject
