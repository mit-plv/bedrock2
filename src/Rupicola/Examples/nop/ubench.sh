#/bin/sh
set -eu
cd "$(dirname "$0")"

CC="${CC:-cc}"
$CC -O3 -c nop.c -lm
$CC -O3 ubench.c nop.o -lm -o ubench

doas /usr/local/bin/turboboost-off.sh > /dev/null
doas /usr/local/bin/hyperthreading-off.sh > /dev/null

doas /usr/bin/cpupower -c 2 frequency-set --governor performance
sleep 1
printf "nop: "; taskset -c 2 ./ubench

doas /usr/local/bin/hyperthreading-on.sh > /dev/null
doas /usr/local/bin/turboboost-on.sh > /dev/null
