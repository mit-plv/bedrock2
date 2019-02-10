#!/usr/bin/env bash

printf "sub-project          fail succ  tot frac\n"

for PROJ in ./deps/coqutil ./deps/riscv-coq ./bedrock2 ./compiler ./processor ; do
    FAILED=`find $PROJ/src -name '*.v.FAIL.manglenames' | wc -l`
    SUCCEEDED=`find $PROJ/src -name '*.v.SUCCESS.manglenames' | wc -l`
    TOTAL=`find $PROJ/src -name '*.v' | wc -l`
    PERCENTAGE=`expr 100 '*' "$SUCCEEDED" '/' "$TOTAL"`
    printf "%-20s %4d %4d %4d %3d%%\n" $PROJ $FAILED $SUCCEEDED $TOTAL $PERCENTAGE
done
