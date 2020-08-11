# Makefile originally based off of one from coq-club, also borrowing from fiat-crypto's Makefile

COQPATH?=$(COQUTIL_FOLDER)/src:$(BEDROCK2_FOLDER)/src
export COQPATH

all: deps Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq INSTALLDEFAULTROOT = Rupicola

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
	git ls-files '*.v' >> _CoqProject

Makefile: ;

phony: ;

.PHONY: all clean phony base coqutil clean-coqutil bedrock2 clean-bedrock2 deps cleanall _CoqProject
