#!/usr/bin/env bash

printf "sub-project          fail succ  tot frac\n"

for PROJ in ./deps/coqutil/src ./deps/riscv-coq/src ./bedrock2/src/bedrock2 ./compiler/src/compiler ./processor/src/processor ; do
    FAILED=`find $PROJ -name '*.v.FAIL.manglenames' | wc -l`
    SUCCEEDED=`find $PROJ -name '*.v.SUCCESS.manglenames' | wc -l`
    TOTAL=`find $PROJ -name '*.v' | wc -l`
    PERCENTAGE=`expr 100 '*' "$SUCCEEDED" '/' "$TOTAL"`
    printf "%-20s %4d %4d %4d %3d%%\n" $PROJ $FAILED $SUCCEEDED $TOTAL $PERCENTAGE
done
