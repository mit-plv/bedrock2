.DEFAULT_GOAL := all

.PHONY: clean force all coq install test

# Absolute paths so that emacs compile mode knows where to find the errors
# even under parallel make, where the 'Entering/Leaving directory ...'
# messages get mixed up.
# Using cygpath -m because Coq on Windows cannot handle cygwin paths.
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src

ALL_VS := $(shell find $(SRCDIR) -name '*.v')

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_NL=
CURFLAGS_NL=-Q ../bedrock2/src/bedrock2 bedrock2\n-Q ../LiveVerif/src/LiveVerif LiveVerif\n-Q src/LiveVerifExamples LiveVerifExamples\n

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ALLDEPFLAGS=$(subst \n, ,$(ALLDEPFLAGS_NL))

# We auto-update _CoqProject,
# but only change the timestamp if the set of files that it lists changed

PRINT_DEPFLAGS_NL := printf -- '$(ALLDEPFLAGS_NL)'
PRINT_ALL_VS := printf -- '%s\n' $(sort $(ALL_VS))
PRINT_COQPROJECT := { $(PRINT_DEPFLAGS_NL); $(PRINT_ALL_VS); }
OLD_COQPROJECT_CONTENTS := $(strip $(shell cat _CoqProject 2>/dev/null))
NEW_COQPROJECT_CONTENTS := $(strip $(shell $(PRINT_COQPROJECT)))

ifneq ($(OLD_COQPROJECT_CONTENTS),$(NEW_COQPROJECT_CONTENTS))
_CoqProject: force
	@echo updating $@
	@$(PRINT_COQPROJECT) > $@
endif

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -docroot LiveVerif $(COQMF_ARGS) -f _CoqProject -o Makefile.coq

coq: Makefile.coq $(ALL_VS)
	$(MAKE) --no-print-directory -f Makefile.coq

all: coq

force:

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf _CoqProject

install::
	$(MAKE) -f Makefile.coq install
