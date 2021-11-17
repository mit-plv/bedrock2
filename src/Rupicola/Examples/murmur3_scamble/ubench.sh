#/bin/sh
set -eu
cd "$(dirname "$0")"

( cd ../../../../
  COQFLAGS="${COQFLAGS:-"$(make -f Makefile.coqflags)"}" bedrock2/etc/bytedump.sh Rupicola.Examples.Arithmetic.murmur3_scramble_cbytes
  ) > murmur3_scramble_rupicola.c

CC="${CC:-cc}"

$CC -O3 -c murmur3_scramble_rupicola.c
$CC -O3 ubench.c murmur3_scramble_rupicola.o -lm -o ubench_rupicola

$CC -O3 -c murmur3_scramble_c.c
$CC -O3 ubench.c murmur3_scramble_c.o -lm -o ubench_c

doas /usr/local/bin/turboboost-off.sh > /dev/null
doas /usr/local/bin/hyperthreading-off.sh > /dev/null

doas /usr/bin/cpupower -c 2 frequency-set --governor performance
sleep 1
printf "murmur3_scramble_rupicola: "; taskset -c 2 ./ubench_rupicola
printf "murmur3_scramble_c: "; taskset -c 2 ./ubench_c

doas /usr/local/bin/hyperthreading-on.sh > /dev/null
doas /usr/local/bin/turboboost-on.sh > /dev/null
