#!/usr/bin/env bash

# supposed to be usable as a replacement for coqc (to which some options followed by exactly one .v file were passed)

# that's not a curse, but how bash says "command line args array at index 'length of command line args'"
VFILE=${@:${#@}}

if [[ ! -f "$VFILE" ]]; then
    echo "Error: $VFILE does not exist"
    exit 1
fi

if [[ ${VFILE: -2} != ".v" ]]; then
    echo "Error: $VFILE is not a .v file"
    exit 1
fi

rm -f "$VFILE.*.manglenames"

if coqc -mangle-names HH "$@" &>/dev/null ; then
    echo "[manglenames] SUCCESS: $VFILE does not depend on auto-generated names"
    touch "$VFILE.SUCCESS.manglenames"
else
    echo "[manglenames] FAIL: $VFILE depends on auto-generated names"
    touch "$VFILE.FAIL.manglenames"
fi

# To make sure we don't confuse other files depending on $VFILE, we recompile in any case:
coqc "$@"
