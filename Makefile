default_target: all

.PHONY: update_all clone_all coqutil riscv-coq bedrock2 compiler processor

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive --remote

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))

DEPS_DIR ?= $(ABS_ROOT_DIR)/deps
export DEPS_DIR

coqutil:
	$(MAKE) -C $(DEPS_DIR)/coqutil

riscv-coq: coqutil
	$(MAKE) -C $(DEPS_DIR)/riscv-coq all

bedrock2: coqutil
	$(MAKE) -C $(ABS_ROOT_DIR)/bedrock2

compiler: riscv-coq bedrock2
	$(MAKE) -C $(ABS_ROOT_DIR)/compiler

processor: riscv-coq
	$(MAKE) -C $(ABS_ROOT_DIR)/processor

all: compiler bedrock2 processor
