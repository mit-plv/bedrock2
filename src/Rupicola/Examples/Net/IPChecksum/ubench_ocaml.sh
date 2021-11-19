#!/bin/sh
set -eu
cd "$(dirname "$0")"

( cd ../../../../../
  coqc ${COQFLAGS:-$(make -f Makefile.coqflags)} src/Rupicola/Examples/Net/IPChecksum/SpecExtraction.v
) > ip_checksum_ocaml.ml

CC="${CC:-cc}"
CFLAGS="${CFLAGS:--O3}"

benchmark=ip_checksum
language=ocaml
ocamlopt -O3 -output-obj ip_checksum_ocaml.ml -o ip_checksum_ocaml_tmp.o
$CC $CFLAGS -I /usr/lib/ocaml ubench_ocaml.c ip_checksum_ocaml_tmp.o -L "$(ocamlopt -where)" -lasmrun -ldl -lm -o ip_checksum_ocaml
printf '("%s", "%s", "%s", ' "$benchmark" "$language" "ocamlopt-$(ocamlopt --version)"
sh -c 'ulimit -s unlimited; taskset -c 2 ./ip_checksum_ocaml'
printf "),\n"
