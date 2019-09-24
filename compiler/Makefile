default_target: all

.PHONY: clean force all

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q ../bedrock2/src/bedrock2 bedrock2\n-Q ./src/compiler compiler\n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	printf -- '$(DEPFLAGS_NL)' > _CoqProject


REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

DEPS_DIR ?= $(ABS_ROOT_DIR)/../deps

EXTERNAL_DEPENDENCIES?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)
# N.B. We should be using ; instead of : iff we are on Windows AND the ocaml we are using was NOT compiled with cygwin...
# We will instead wait until someone complains that make is not working on Windows and then have them figure out a way to detect this case
# Note that Windows users can always manually set COQPATH, so always using : does not make it impossible to build on Windows, just a bit of a pain.
COQPATH?=$(DEPS_DIR)/coqutil/src:$(DEPS_DIR)/riscv-coq/src
export COQPATH
endif

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/compiler

ALL_VS := $(shell find $(SRCDIR) -type f -name '*.v')

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

src/compiler/examples/swap_bytes_over_uart.hex: src/compiler/examples/swap_bytes_over_uart_hexdump.v _CoqProject src/compiler/examples/FE310Compiler.vo
	coqc -q $(shell cat _CoqProject) $< > $@
src/compiler/examples/swap_bytes_over_uart.bin: src/compiler/examples/swap_bytes_over_uart.hex
	xxd -r -p $< > $@
src/compiler/examples/swap_bytes_over_uart.elf: src/compiler/examples/swap_bytes_over_uart.bin
	riscv64-linux-gnu-ld --section-start=.data=0x20400000 --strip-all --format=binary --oformat=elf32-littleriscv $< -o $@

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject src/compiler/examples/swap_bytes_over_uart.elf src/compiler/examples/swap_bytes_over_uart.bin src/compiler/examples/swap_bytes_over_uart.hex
