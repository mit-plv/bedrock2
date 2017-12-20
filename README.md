# Towards a verified compiler from a C-like language to RISC-V

Tested with Coq 8.7.0

Dependency: The [Bedrock Bitvector Library (bbv)](https://github.mit.edu/plv/bbv/) should be a sibling directory of the `compiler` directory.

Building: First run `make` in the `bbv` directory, then run `make` in the `compiler` directory.



## Overview (as of Dec 20, 2017)

The source language is a "C-like" language called ExprImp. It is an imperative language with expressions.
ExprImp is compiled to FlatImp, which has no expressions, ie. all expressions have to be flattened into one-operation-at-a-time style assignments.
FlatImp is compiled to RISC-V (the target language).

Currently, no heap memory is supported, variables are the only storage, and the RISC-V language assumes an unbounded number of registers (even though there are only 32 in reality).

Main correctness theorems:

*   `flattenStmt_correct_aux` in `FlattenExpr.v`
*   `compile_stmt_correct_aux` in `FlatToRiscv.v`



