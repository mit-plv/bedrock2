## A work-in-progress language and compiler for verified low-level programming

This repository containts ongoing work on a low-level systems programming language. One piece of the puzzle is a verified compiler targeting RISC-V. The source language itself is also equipped with a simple program logic for proving correctness of the source programs. It is not ready yet, at least for most uses.

This project has similar goals as [bedrock](https://github.com/mit-plv/bedrock), but uses a different design.
No code is shared between bedrock and bedrock2.

### Current Features

The source language is a "C-like" language called ExprImp. It is an imperative language with expressions.
Currently, the only data type is word (32-bit or 64-bit), and the memory is an array of bytes.
"Records" are supported as a notation for memory access with an offset.


### Work-in-progress features

The following features will be added soon:
*    Register allocation (spilling if more local variables are needed than registers are available)

### Non-features

It is a design decision to *not* support the following features:
*    Function pointers

### Build [![Build Status](https://travis-ci.com/mit-plv/bedrock2.svg?branch=master)](https://travis-ci.com/mit-plv/bedrock2)

You'll need [Coq](https://coq.inria.fr/), version 8.10 or master.

In case you didn't clone with `--recursive`, use `make clone_all` to clone the git submodules.

Then simply run `make` or `make -j` or `make -jN` where `N` is the number of cores to use. This will invoke the Makefiles of each subproject in the correct order, and also pass the `-j` switch to the recursive make.

### Compilation Overview (as of May 29, 2018)

The source language (ExprImp) is compiled to FlatImp, which has no expressions, ie. all expressions have to be flattened into one-operation-at-a-time style assignments.
FlatImp is compiled to RISC-V (the target language).

Main correctness theorems:

*   `flattenStmt_correct_aux` in `FlattenExpr.v`
*   `compile_stmt_correct_aux` in `FlatToRiscv.v`
*   `exprImp2Riscv_correct` in `Pipeline.v` combining the two
