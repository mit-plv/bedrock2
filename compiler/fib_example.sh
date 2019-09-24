#!/bin/bash

# src/compiler/PipelineTest.v should create Fib6.hs
make

# should print 13 (in (S (S ...O)) form)
cat hs_commands.txt | ghci
