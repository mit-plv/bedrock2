default_target: all

.PHONY: clean force all

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q ../bedrock2/src bedrock2\n-Q $(DEPS_DIR)/coqutil/src coqutil\n-Q $(DEPS_DIR)/riscv-coq/src riscv\n-Q ./lib lib\n-Q ./src compiler\n
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	printf -- '$(DEPFLAGS_NL)' > _CoqProject

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src
LIBDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/lib

ALL_VS := $(shell find $(SRCDIR) $(LIBDIR) -type f -name '*.v')

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = bedrock2 $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

src/examples/swap_bytes_over_uart.hex: src/examples/swap_bytes_over_uart_hexdump.v _CoqProject src/examples/FE310Compiler.v
	coqc -q $(shell cat _CoqProject) $< > $@
src/examples/swap_bytes_over_uart.bin: src/examples/swap_bytes_over_uart.hex
	xxd -r -p $< > $@
src/examples/swap_bytes_over_uart.elf: src/examples/swap_bytes_over_uart.bin
	riscv64-linux-gnu-ld --section-start=.data=0x20400000 --strip-all --format=binary --oformat=elf32-littleriscv $< -o $@

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject examples/swap_bytes_over_uart.elf examples/swap_bytes_over_uart.bin examples/swap_bytes_over_uart.hex
