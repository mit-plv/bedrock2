#!/bin/sh

find . -name '*.v' -exec sh -c './etc/count_one.sh "$0"' {} \;
