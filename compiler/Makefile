default_target: all

.PHONY: clean force all noex ex install

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_RISCV_COQ_NL=-Q $(DEPS_DIR)/riscv-coq/src/riscv riscv\n
DEPFLAGS_NL=-Q ../bedrock2/src/bedrock2 bedrock2\n-Q ../bedrock2/src/bedrock2Examples bedrock2Examples\n
CURFLAGS_NL=-Q ./src/compiler compiler\n-Q ./src/compilerExamples compilerExamples\n

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=
EXTERNAL_RISCV_COQ?=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

ifneq ($(EXTERNAL_RISCV_COQ),1)
DEPFLAGS_NL+=$(DEPFLAGS_RISCV_COQ_NL)
endif

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ALLDEPFLAGS=$(subst \n, ,$(ALLDEPFLAGS_NL))

_CoqProject:
	printf -- '$(ALLDEPFLAGS_NL)' > _CoqProject

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/compiler
EXDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/compilerExamples

VS_NOEX := $(shell find $(SRCDIR) -type f -name '*.v')
VS_EX := $(shell find $(EXDIR) -type f -name '*.v')

noex: Makefile.coq.noex $(VS_NOEX)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.noex

ex: Makefile.coq.ex $(VS_EX) noex
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.ex

all: noex ex

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.noex: force _CoqProject
	@echo "Generating Makefile.coq.noex"
	@$(COQ_MAKEFILE) $(VS_NOEX) -o Makefile.coq.noex

Makefile.coq.ex: force _CoqProject
	@echo "Generating Makefile.coq.ex"
	@$(COQ_MAKEFILE) $(VS_EX) -o Makefile.coq.ex

src/compiler/examples/swap_bytes_over_uart.hex: src/compiler/examples/swap_bytes_over_uart_hexdump.v _CoqProject src/compiler/examples/FE310Compiler.vo
	coqc -q $(shell cat _CoqProject) $< > $@
src/compiler/examples/swap_bytes_over_uart.bin: src/compiler/examples/swap_bytes_over_uart.hex
	xxd -r -p $< > $@
src/compiler/examples/swap_bytes_over_uart.elf: src/compiler/examples/swap_bytes_over_uart.bin
	riscv64-linux-gnu-ld --section-start=.data=0x20400000 --strip-all --format=binary --oformat=elf32-littleriscv $< -o $@

force:

clean:: Makefile.coq.noex Makefile.coq.ex
	$(MAKE) -f Makefile.coq.noex clean
	$(MAKE) -f Makefile.coq.ex clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.noex Makefile.coq.noex.conf Makefile.coq.ex Makefile.coq.ex.conf _CoqProject src/compiler/examples/swap_bytes_over_uart.elf src/compiler/examples/swap_bytes_over_uart.bin src/compiler/examples/swap_bytes_over_uart.hex

install::
	$(MAKE) -f Makefile.coq.noex install
