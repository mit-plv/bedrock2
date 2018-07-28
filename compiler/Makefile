
default_target: all

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

DIRS = lib src

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q $(DEPS_DIR)/bbv/theories bbv \n-Q $(DEPS_DIR)/riscv-coq/src riscv \n-Q ./lib lib \n-Q ./src compiler
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	echo -e '$(DEPFLAGS_NL)' > _CoqProject

COQFLAGS=$(DEPFLAGS)

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

all: $(patsubst %.v,%.vo,$(wildcard src/*.v src/examples/*.v)) _CoqProject

ExprImp: src/ExprImp.vo src/ExprImpNotations.vo

.depend depend:
	$(COQDEP) $(DEPFLAGS) >.depend `find $(DIRS) -name "*.v"`

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

