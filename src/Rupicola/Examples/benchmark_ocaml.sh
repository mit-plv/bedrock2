#/bin/sh
set -eu
cd "$(dirname "$0")"

{
	printf "# %s\n" "$(grep 'processor\W*2' -A5 /proc/cpuinfo | tr '\n' ';' |  sed 's/;/; /g; s/\s\+/ /g; s/ \?: \?/=/g')"
	printf 'data=[\n'
	find Net/IPChecksum -name 'ubench_ocaml.sh' | xargs -n1 env CC="clang" CFLAGS="-O3 -march=native" sh
	for CC in clang gcc gcc-10; do
		find Net/IPChecksum -name 'ubench.sh' | xargs -n1 env CC="$CC" CFLAGS="-O3 -march=native" sh
	done
	printf ']\n'
} | tee latest_benchmark_ocaml_results.py
