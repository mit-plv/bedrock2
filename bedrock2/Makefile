default_target: all

.PHONY: clean force all noex ex install_noex install_ex install test

# Absolute paths so that emacs compile mode knows where to find the errors.
# The emacs compile mode considers the 'Entering/Leaving directory ...'
# message emitted by make, so relative paths should work, but -j mixes
# the output of several parallel sub-makes, so relative paths can't be
# used any more (and '--output-sync=recurse' would hold back the output
# for too long).
# Using cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/bedrock2
EXDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/bedrock2Examples

VS_NOEX:=$(shell find $(SRCDIR) -type f -name '*.v')
VS_EX:=$(shell find $(EXDIR) -type f -name '*.v')

CC ?= cc
DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_NL=
CURFLAGS_NL=-Q src/bedrock2 bedrock2\n-Q src/bedrock2Examples bedrock2Examples\n

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ALLDEPFLAGS=$(subst \n, ,$(ALLDEPFLAGS_NL))

# We auto-update _CoqProject and _CoqProject.noex,
# but only change their timestamp if the set of files that they list changed

PRINT_DEPFLAGS_NL := printf -- '$(ALLDEPFLAGS_NL)'
PRINT_VS_NOEX := printf -- '%s\n' $(sort $(VS_NOEX))
PRINT_VS_EX := printf -- '%s\n' $(sort $(VS_EX))
PRINT_COQPROJECT_NOEX := { $(PRINT_DEPFLAGS_NL); $(PRINT_VS_NOEX); }
PRINT_COQPROJECT := { $(PRINT_DEPFLAGS_NL); $(PRINT_VS_NOEX); $(PRINT_VS_EX); }
OLD_COQPROJECT_NOEX_CONTENTS := $(strip $(shell cat _CoqProject.noex 2>/dev/null))
NEW_COQPROJECT_NOEX_CONTENTS := $(strip $(shell $(PRINT_COQPROJECT_NOEX)))
OLD_COQPROJECT_CONTENTS := $(strip $(shell cat _CoqProject 2>/dev/null))
NEW_COQPROJECT_CONTENTS := $(strip $(shell $(PRINT_COQPROJECT)))

ifneq ($(OLD_COQPROJECT_NOEX_CONTENTS),$(NEW_COQPROJECT_NOEX_CONTENTS))
_CoqProject.noex: force
	@echo updating $@
	@$(PRINT_COQPROJECT_NOEX) > $@
endif

ifneq ($(OLD_COQPROJECT_CONTENTS),$(NEW_COQPROJECT_CONTENTS))
_CoqProject: force
	@echo updating $@
	@$(PRINT_COQPROJECT) > $@
endif

noex: Makefile.coq.noex $(VS_NOEX)
	$(MAKE) --no-print-directory -f Makefile.coq.noex

ex: Makefile.coq.ex $(VS_EX) noex
	$(MAKE) --no-print-directory -f Makefile.coq.ex

all: noex ex test
test: special/BytedumpTest.out special/stackloop.out special/stacknondet.out special/ToCStringTest.out special/TypecheckExprToCString.out # special/TypecheckExprToCString-32.out special/TypecheckExprToCString-64.out

COQ_MAKEFILE := $(COQBIN)coq_makefile -docroot bedrock2 $(COQMF_ARGS)

Makefile.coq.noex: _CoqProject.noex
	$(COQ_MAKEFILE) -f _CoqProject.noex -o Makefile.coq.noex

Makefile.coq.ex: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -arg -native-compiler -arg ondemand -o Makefile.coq.ex

BYTEDUMP_DEPS := $(SRCDIR)/PrintListByte.vo ../etc/bytedump.py
BYTEDUMP := COQFLAGS="$(ALLDEPFLAGS)" ../etc/bytedump.py

special/BytedumpTest.out: special/BytedumpTest.golden.bin $(BYTEDUMP_DEPS)
	$(BYTEDUMP) bedrock2.PrintListByte.allBytes > special/BytedumpTest.out.tmp
	hexdump < /dev/null && \
		hexdump -C special/BytedumpTest.golden.bin > special/BytedumpTest.golden.hex && \
		hexdump -C special/BytedumpTest.out.tmp > special/BytedumpTest.out.hex && \
		diff -u special/BytedumpTest.golden.hex special/BytedumpTest.out.hex && \
		rm special/BytedumpTest.golden.hex special/BytedumpTest.out.hex || true
	diff -u special/BytedumpTest.golden.bin special/BytedumpTest.out.tmp
	mv special/BytedumpTest.out.tmp special/BytedumpTest.out

$(SRCDIR)/ToCStringStackallocLoopTest.vo: | noex
special/stackloop.c: $(SRCDIR)/ToCStringStackallocLoopTest.vo $(BYTEDUMP_DEPS)
	$(BYTEDUMP) bedrock2.ToCStringStackallocLoopTest.main_cbytes > $@
special/stackloop: special/stackloop.c
	$(CC) -O0 $< -o $@
special/stackloop.out: special/stackloop
	special/stackloop > $@

$(EXDIR)/stackalloc.vo: | ex
special/stacknondet.c: $(EXDIR)/stackalloc.vo $(BYTEDUMP_DEPS)
	$(BYTEDUMP) bedrock2Examples.stackalloc.stacknondet_c > $@
special/stacknondet: special/stacknondet.c
	$(CC) $< -o $@
special/stacknondet.out: special/stacknondet
	$< > $@

$(EXDIR)/ToCStringTest.vo: | noex
special/ToCStringTest.c: $(SRCDIR)/ToCStringTest.vo $(BYTEDUMP_DEPS)
	$(BYTEDUMP) bedrock2.ToCStringTest.test > $@
special/ToCStringTest: special/ToCStringTest.c
	$(CC) $< -o $@
special/ToCStringTest.out: special/ToCStringTest
	$< > $@

$(SRCDIR)/ToCStringExprTypecheckingTest.vo : | noex
special/TypecheckExprToCString.c: $(SRCDIR)/ToCStringExprTypecheckingTest.vo $(BYTEDUMP_DEPS)
	$(BYTEDUMP) bedrock2.ToCStringExprTypecheckingTest.test > $@
special/TypecheckExprToCString.out: special/TypecheckExprToCString.c
	$(CC) -fsyntax-only $< > $@
special/TypecheckExprToCString-64.out: special/TypecheckExprToCString.c
	$(CC) -m64 -fsyntax-only $< > $@
special/TypecheckExprToCString-32.out: special/TypecheckExprToCString.c
	$(CC) -m32 -fsyntax-only $< > $@

force:

clean:: Makefile.coq.noex Makefile.coq.ex
	$(MAKE) -f Makefile.coq.noex clean
	$(MAKE) -f Makefile.coq.ex clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.noex Makefile.coq.noex.conf Makefile.coq.ex Makefile.coq.ex.conf _CoqProject special/BytedumpTest.out

install_noex::
	$(MAKE) -f Makefile.coq.noex install

install_ex::
	$(MAKE) -f Makefile.coq.ex install

install:: install_noex install_ex
