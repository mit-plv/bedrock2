#/bin/sh
set -eu

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
} | sed '0,/^COQTOP_CRAP_ENDS_HERE$/d' | sed -z '$ s/\n$//'
