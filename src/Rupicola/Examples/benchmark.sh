#/bin/sh
set -eu
cd "$(dirname "$0")"

COMPILERS="clang-11 clang-12 clang-13 gcc-9 gcc-10 gcc-11"
{
	printf "# %s\n" "$(grep 'processor\W*2' -A5 /proc/cpuinfo | tr '\n' ';' |  sed 's/;/; /g; s/\s\+/ /g; s/ \?: \?/=/g')"
	printf 'data=[\n'
	for CC in $COMPILERS; do
		find . -name ubench.sh | xargs -n1 env CC="$CC" CFLAGS="-O3 -march=native" sh
	done
	printf ']\n'
} | tee latest_benchmark_results.py
