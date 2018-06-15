## Towards a low-level systems programming language with a verified compiler

This is work in progress towards a low-level systems programming language with current work focusing on a verified compiler targeting RISC-V.

This project has similar goals as [bedrock](https://github.com/mit-plv/bedrock), but uses a different design:
No code is shared between bedrock and bedrock2 (except a [bit vector library](https://github.mit.edu/plv/bbv/)), and compilation is implemented as a Gallina function rather than as an Ltac function.


### Build

You'll need [Coq](https://coq.inria.fr/), see variable `EXPECTED_COQC_VERSION` in the Makefile for which version to use.

Dependencies: The following projects should be sibling directories of the `bedrock2` directory:
*    The [Bedrock Bitvector Library (bbv)](https://github.mit.edu/plv/bbv/)
*    The [RISCV Specification in Coq (riscv-coq)](https://github.com/samuelgruetter/riscv-coq)

To build the whole project (including the compiler):
*    run `make` in the `bbv` directory
*    run `make proofs` in the `riscv-coq` directory
*    run `make` in the `bedrock2` directory

To build only the source language (ExprImp):
*    run `make` in the `bbv` directory
*    run `make util` in the `riscv-coq` directory
*    run `make ExprImp` in the `bedrock2` directory


### Current Features

The source language is a "C-like" language called ExprImp. It is an imperative language with expressions.
Currently, the only data type is word (32-bit or 64-bit), and the memory is an array of such words.


### Planned features

The following features will be added soon:
*    Functions
*    Register allocation (spilling if more local variables are needed than registers are available)


### Non-features

It is a design decision to *not* support the following features:
*    Records
*    Function pointers


### Compilation Overview (as of May 29, 2018)

The source language (ExprImp) is compiled to FlatImp, which has no expressions, ie. all expressions have to be flattened into one-operation-at-a-time style assignments.
FlatImp is compiled to RISC-V (the target language).

Main correctness theorems:

*   `flattenStmt_correct_aux` in `FlattenExpr.v`
*   `compile_stmt_correct_aux` in `FlatToRiscv.v`
*   `exprImp2Riscv_correct` in `Pipeline.v` combining the two


