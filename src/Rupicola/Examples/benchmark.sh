#/bin/sh
set -eu
cd "$(dirname "$0")"

{
	printf 'data=[\n'
	find . -name ubench.sh | xargs -n1 sh
	printf ']\n'
} | tee latest_benchmark_results.py
