#!/bin/sh

# sample usage:
# ./refactor_sed.sh -f renamings.txt
#
# where renamings.txt contains eg.
#
# s/bedrock2.Macros/coqutil.Macros.unique/g
# s/bedrock2.Map.SortedList/coqutil.Map.SortedList/g
# s/compiler.Decidable/coqutil.Decidable/g
# s/compiler.Semantics/bedrock2.Semantics/g
# s/compiler.util.List_Map/coqutil.Map.SortedList/g
# s/compiler.util.Map/coqutil.Map.Solver/g
# s/compiler.util.MapSolverTest/coqutil.Map.TestLemmas/g

set -x

find . -type f -name '*.v' -print0 | xargs -0 sed -i "$@"
