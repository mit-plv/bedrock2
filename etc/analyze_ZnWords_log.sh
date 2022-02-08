#!/bin/sh

# In ZnWords.v, replace
#   Ltac ZnWords := ZnWords_pre; better_lia.
# by
#   Ltac ZnWords := time "ZnWords" (ZnWords_pre; better_lia).
# Then run
#   TIMED=1 time make | tee /path/to/logfile.log
# and then run this script with /path/to/logfile.log as its first argument.

echo -n "Number of ZnWords calls: "
sed $1 -E -n -e 's/Tactic call ZnWords ran for ([^ ]+) .*/\1/p' | wc -l

echo -n "Total time spent in ZnWords: "
sed $1 -E -n -e 's/Tactic call ZnWords ran for ([^ ]+) .*/\1/p' | paste -s -d+ - | bc
