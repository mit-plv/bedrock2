
default_target: all

.PHONY: clean force all

VS:=$(shell find . -type f -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q src bedrock2 \n-Q $(DEPS_DIR)/bbv/theories bbv
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	echo -e '$(DEPFLAGS_NL)' > _CoqProject

all: Makefile.coq.all $(VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject
