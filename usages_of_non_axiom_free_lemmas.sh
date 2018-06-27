#!/bin/sh

GREP_FOR=`grep deps/bbv/Word.v -e 'not axiom free' | sed -e 's/Lemma //g' -e 's/[: ].*//g' | tr '\n' - | sed -e 's/-$/\n/g' -e 's/^/-/g' -e 's/-/ -e /g'`

set -x

grep -R . --include='*.v' $GREP_FOR -C3 --color=always
