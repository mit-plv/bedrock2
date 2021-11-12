#/bin/sh
set -eu

{
coqtop -quiet $COQFLAGS 2>/dev/null << EOF
Require ${1%.*}.
Require Import bedrock2.Bytedump. Local Open Scope bytedump_scope.
Goal forall COQTOP_CRAP_ENDS_HERE:Prop, COQTOP_CRAP_ENDS_HERE.
  let bs := eval cbv in ${1} in idtac bs.
Abort.
EOF
} | sed '1,/COQTOP_CRAP_ENDS_HERE/d'

# NOTE: there are extra newlines at the end: at least one from idtac and maybe more
