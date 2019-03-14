default_target: all

.PHONY: update_all clone_all coqutil riscv-coq bedrock2 compiler kami processor clean_coqutil clean_riscv-coq clean_bedrock2 clean_compiler clean_kami clean_processor clean_manglenames

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

DEPS_DIR ?= $(ABS_ROOT_DIR)/deps
export DEPS_DIR

ifeq ($(TRY_MANGLE_NAMES),1)
COQC := $(ABS_ROOT_DIR)/coqc-try-mangle-names.sh
export COQC
endif

clean_manglenames:
	find . -type f -name '*.manglenames' -delete

coqutil:
	$(MAKE) -C $(DEPS_DIR)/coqutil

clean_coqutil:
	$(MAKE) -C $(DEPS_DIR)/coqutil clean

kami: riscv-coq
	$(MAKE) -C $(DEPS_DIR)/kami

clean_kami:
	$(MAKE) -C $(DEPS_DIR)/kami clean

riscv-coq: coqutil
	$(MAKE) -C $(DEPS_DIR)/riscv-coq all

clean_riscv-coq:
	$(MAKE) -C $(DEPS_DIR)/riscv-coq clean

bedrock2: coqutil riscv-coq
	$(MAKE) -C $(ABS_ROOT_DIR)/bedrock2

clean_bedrock2:
	$(MAKE) -C $(ABS_ROOT_DIR)/bedrock2 clean

compiler: riscv-coq bedrock2
	$(MAKE) -C $(ABS_ROOT_DIR)/compiler

clean_compiler:
	$(MAKE) -C $(ABS_ROOT_DIR)/compiler clean

processor: riscv-coq kami
	$(MAKE) -C $(ABS_ROOT_DIR)/processor

clean_processor:
	$(MAKE) -C $(ABS_ROOT_DIR)/processor clean

all: coqutil riscv-coq bedrock2 compiler processor

clean: clean_coqutil clean_riscv-coq clean_bedrock2 clean_compiler clean_kami clean_processor
