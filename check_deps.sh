#!/bin/sh

echo "bedrock2: Skipping dependency check" 1>&2
exit 0

DEPS=`cd dep && ls`

for d in $DEPS; do
    EXPECTED=`cat dep/$d`
    ACTUAL=`cd ../$d && git rev-parse HEAD`
    if [ "$ACTUAL" != "$EXPECTED" ]; then
        echo "Commit hash of $d does not match: Expected $EXPECTED, but got $ACTUAL"
        exit 1
    fi
done

