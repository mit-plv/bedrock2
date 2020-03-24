## A work-in-progress language and compiler for verified low-level programming

This repository containts ongoing work on a low-level systems programming language. One piece of the puzzle is a verified compiler targeting RISC-V. The source language itself is also equipped with a simple program logic for proving correctness of the source programs. It is not ready yet, at least for most uses.

This project has similar goals as [bedrock](https://github.com/mit-plv/bedrock), but uses a different design.
No code is shared between bedrock and bedrock2.


### Current Features

The source language is a "C-like" language called ExprImp. It is an imperative language with expressions.
Currently, the only data type is word (32-bit or 64-bit), and the memory is a partial map from words to bytes.
"Records" are supported as a notation for memory access with an offset.


### Work-in-progress features

The following features will be added soon:
*    Register allocation (spilling if more local variables are needed than registers are available)


### Non-features

It is a design decision to *not* support the following features:
*    Function pointers


### Build [![Build Status](https://travis-ci.com/mit-plv/bedrock2.svg?branch=master)](https://travis-ci.com/mit-plv/bedrock2)

You'll need [Coq](https://coq.inria.fr/), version 8.11 or master.

In case you didn't clone with `--recursive`, use `make clone_all` to clone the git submodules.

Then simply run `make` or `make -j` or `make -jN` where `N` is the number of cores to use. This will invoke the Makefiles of each subproject in the correct order, and also pass the `-j` switch to the recursive make.


### Project Overview

This repository is an umbrella repository integrating several sub-projects, allowing us to prove end-to-end theorems describing the I/O behavior of a pipelined processor executing a program written in the bedrock2 language, verified with our program logic, and compiled with our compiler.

There are the following sub-projects:

*    [coqutil](https://github.com/mit-plv/coqutil): Coq library for tactics, basic definitions, sets, maps
*    [riscv-coq](https://github.com/mit-plv/riscv-coq): RISC-V specification in Coq
*    [bedrock2/bedrock2](https://github.com/mit-plv/bedrock2/tree/master/bedrock2): The bedrock2 language, a simple C-like programming language with a program logic and a few verified sample programs
*    [bedrock2/compiler](https://github.com/mit-plv/bedrock2/tree/master/compiler): A very simple compiler from the bedrock2 language to bare metal, position independent RISC-V machine code
*    [kami](https://github.com/mit-plv/kami/tree/rv32i): Provides a 4-stage pipelined RISC-V processor
*    [processor](https://github.com/mit-plv/bedrock2/tree/master/processor): Proves that the hardware-centric RISC-V specification of Kami matches the software-centric specification of riscv-coq
*    [end2end](https://github.com/mit-plv/bedrock2/tree/master/end2end): Combines all the projects into an end-to-end theorem about a concrete program, the IoT lightbulb demo.

The Kami processor can be extracted to [bluespec](https://github.com/B-Lang-org/bsc), which can be compiled to Verilog, and run on an FPGA.


### The IoT lightbulb demo

<img alt="IoT lightbulb demo" src="img/lightbulb-on.jpg" width="700px"/>

In the above picture, the FPGA at the bottom left is running the Kami processor, which executes a program proven correct using the bedrock2 program logic and compiled to bytes using the bedrock2 compiler.
Through a set of blue wires (using SPI), the FPGA is connected to an ethernet card (which we do not verify), and through a red & black wire, it is connected to a power relay which can turn on and off a lightbulb.


### Compilation Overview (as of May 29, 2018)

The source language (ExprImp) is compiled to FlatImp, which has no expressions, ie. all expressions have to be flattened into one-operation-at-a-time style assignments.
FlatImp is compiled to RISC-V (the target language).
