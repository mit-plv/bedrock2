#!/bin/sh

printf '\033c'

set -e
set -o pipefail
set -x

cd deps/coq
git clean -dfx
git fetch
git reset origin/for_itauto --hard
git show -s --oneline HEAD
./configure -local
make
cd ../..

cd deps/itauto/
git clean -dfx
git pull
git show -s --oneline HEAD
make
make install
cd ../..

cd deps/coq-record-update/
git clean -dfx
cd ../..

cd deps/coqutil/
git clean -dfx
cd ../..

cd deps/kami/
git clean -dfx
cd ../..

cd deps/riscv-coq/
git clean -dfx
cd ../..

git clean -dfx

time TIMED=1 make 2>&1 | tee log.txt | grep -v -e ' ran for 0' -e '^Tactic call *$'
