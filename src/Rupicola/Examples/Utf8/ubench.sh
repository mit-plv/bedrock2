#/bin/sh
set -eu
scriptdir="$(realpath "$(dirname "$0")")"

cd "$scriptdir/../../../../"
coqc $(make -f Makefile.coqflags) "$(realpath src/Rupicola/Examples/Utf8/Print.v)" > src/Rupicola/Examples/Utf8/utf8_rupicola.h

cd "$scriptdir"

gcc -O3 -c utf8_skeeto.c
gcc -O3 -lm ubench.c utf8_skeeto.o -o ubench_skeeto

gcc -O3 -c utf8_client_rupicola.c
gcc -O3 -lm ubench.c utf8_client_rupicola.o -o ubench_rupicola

doas /usr/local/bin/turboboost-off.sh > /dev/null
doas /usr/local/bin/hyperthreading-off.sh > /dev/null

#doas /usr/bin/cpupower -c 2 frequency-set --freq "$(grep -o '[0-9\.]*GHz' /proc/cpuinfo | sort -h | head -1)"
doas /usr/bin/cpupower -c 2 frequency-set --governor performance
sleep 1
printf "utf8_rupicola: "; taskset -c 2 ./ubench_rupicola
printf "utf8_skeeto: "; taskset -c 2 ./ubench_skeeto
#doas /usr/bin/cpupower -c 2 frequency-set --governor schedutil

doas /usr/local/bin/hyperthreading-on.sh > /dev/null
doas /usr/local/bin/turboboost-on.sh > /dev/null
