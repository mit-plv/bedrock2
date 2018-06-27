
default_target: all

COQC=$(COQBIN)coqc

DIRS = lib src

COQFLAGS= -Q ../bbv bbv  -Q ../riscv-coq/src riscv  -Q ./lib lib  -Q ./src compiler

DEPFLAGS:=$(COQFLAGS)

COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

all: $(patsubst %.v,%.vo,$(wildcard src/*.v src/examples/*.v))

ExprImp: src/ExprImp.vo src/ExprImpNotations.vo

.depend depend:
	$(COQDEP) >.depend `find $(DIRS) -name "*.v"`

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

