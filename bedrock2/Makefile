
default_target: all

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

DIRS = src
VS:=$(shell find . -type f -name '*.v')
VOS:=$(patsubst %.v,%.vo,$(VS))

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q src bedrock2 -Q \n $(DEPS_DIR)/bbv/theories bbv \n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	echo -e '$(DEPFLAGS_NL)' > _CoqProject

COQFLAGS=$(DEPFLAGS)

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

all: $(VOS) _CoqProject

.depend depend:
	$(COQDEP) $(DEPFLAGS) >.depend $(VS)

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

