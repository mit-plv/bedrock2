#!/bin/sh

# set to first arg or else to working directory
root=${1:-.}

find "$root" -name '*.v' -exec sh -c './etc/count_one.sh "$0"' {} \;
