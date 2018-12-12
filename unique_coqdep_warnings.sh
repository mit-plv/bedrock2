#!/bin/sh
sed -e 's/.*, library//g' -e 's/ is required and has not been found.*//g' | sort | uniq
