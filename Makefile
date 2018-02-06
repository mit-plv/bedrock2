
default_target: all

DEPS := $(patsubst dep/%,%,$(wildcard dep/*))

DEPS_CHECK_RESULT := $(shell ./check_deps.sh)

ifneq ($(DEPS_CHECK_RESULT), )
  $(error $(DEPS_CHECK_RESULT))
endif

DIRS = lib src

COQFLAGS= -Q ../bbv bbv  -Q ../riscv-coq/src riscv  -Q ./lib lib  -Q ./src compiler

DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

all: $(patsubst %.v,%.vo,$(wildcard src/*.v src/examples/*.v))

.depend depend:
	$(COQDEP) >.depend `find $(DIRS) -name "*.v"`

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

