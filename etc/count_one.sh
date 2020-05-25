#!/bin/sh

if ! grep "$1" -e '(\*tag:.*\*)' ; then
    printf "$1 is not annotated\n" 1>&2
fi

printf '(*tag:UNTAGGED*)\n'
cat "$1"
printf "\n"
