# Makefile originally based off of one from coq-club, also borrowing from fiat-crypto and bedrock2's Makefiles

COQPATH?=$(COQUTIL_FOLDER)/src:$(BEDROCK2_FOLDER)/src
export COQPATH

# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola/Lib
EXDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/Rupicola/Examples

# absolute paths so that emacs compile mode knows where to find error
VS_NOEX:=$(shell git ls-files $(SRCDIR) | xargs readlink -f | grep "\.v")
VS_EX:=$(shell git ls-files $(EXDIR) | xargs readlink -f | grep "\.v")

all: deps noex ex

noex: Makefile.coq.noex $(VS_NOEX)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.noex

ex: Makefile.coq.ex $(VS_EX) noex
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.ex

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = Rupicola $(COQMF_ARGS)

force:

Makefile.coq.noex: force _CoqProject
	@echo "Generating Makefile.coq.noex"
	@$(COQ_MAKEFILE) $(VS_NOEX) -o Makefile.coq.noex

Makefile.coq.ex: force _CoqProject
	@echo "Generating Makefile.coq.ex"
	@$(COQ_MAKEFILE) $(VS_EX) -o Makefile.coq.ex

clean:: Makefile.coq.noex Makefile.coq.ex
	$(MAKE) -f Makefile.coq.noex clean
	$(MAKE) -f Makefile.coq.ex clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.noex Makefile.coq.noex.conf Makefile.coq.ex Makefile.coq.ex.conf _CoqProject

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

.PHONY: all noex ex clean phony base coqutil clean-coqutil bedrock2 clean-bedrock2 deps cleanall _CoqProject
