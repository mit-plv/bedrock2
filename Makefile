
default_target: all

COQC=$(COQBIN)coqc

EXPECTED_COQC_VERSION ?= 8.7.2

ACTUAL_COQC_VERSION := $(shell $(COQC) --version | sed -n 's/The Coq Proof Assistant, version \([^ ]*\) .*/\1/p')

ifneq ($(EXPECTED_COQC_VERSION), $(ACTUAL_COQC_VERSION))
  $(error Coq version mismatch: Expected version $(EXPECTED_COQC_VERSION), but got $(ACTUAL_COQC_VERSION))
endif


DEPS := $(patsubst dep/%,%,$(wildcard dep/*))

DEPS_CHECK_RESULT := $(shell ./check_deps.sh)

ifneq ($(DEPS_CHECK_RESULT), )
  $(error $(DEPS_CHECK_RESULT))
endif

DIRS = lib src

COQFLAGS= -Q ../bbv bbv  -Q ../riscv-coq/src riscv  -Q ./lib lib  -Q ./src compiler

DEPFLAGS:=$(COQFLAGS)

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

