#/bin/sh
set -eu
ulimit -s unlimited || true

{
coqtop -q -quiet $COQFLAGS 2>/dev/null << EOF
Require ${1%.*}.
Require Import bedrock2.Bytedump. Local Open Scope bytedump_scope.
Local Set Printing Width 2147483647.
Goal True.
  idtac "COQTOP_CRAP_ENDS_HERE".
  let bs := eval cbv in ${1} in idtac bs.
Abort.
EOF
} | python -c '
import os, sys
needle = b"\nCOQTOP_CRAP_ENDS_HERE\n"
waiting_on_coqbug_15373 = True
b = b""
while True:
	r = os.read(0, 1)
	if not r:
		sys.exit(waiting_on_coqbug_15373 + 2*(not b.endswith(b"\n")))
	b = b[-(len(needle)-len(r)):] + r
	if b == needle:
		waiting_on_coqbug_15373 = 0
		b = b""
	if not waiting_on_coqbug_15373:
		os.write(1, b[-2:-1])
'
