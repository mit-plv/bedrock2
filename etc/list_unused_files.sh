#!/bin/bash

grep -Fv -f <( grep -R . --include='*.v' --no-filename -e 'Require ' | sed -E -e 's/Import +//g' -e 's/Export +//g' -e 's/From +[^ ]+ +//g' -e 's/Require +//g' -e 's/Local +//g' -e 's/Open +Scope +[^ ]+//g' -e 's/Set Default Proof Mode "Classic".//g' -e 's/\(\*.*\*\)//g' -e 's/\. //g' -e 's/\.$//g' -e 's/[^ .]+\.//g' | tr ' ' '\n' | grep -v -e '^ *$' | sed -e 's/$/.v/g' | sort | uniq ) <( find . -name '*.v' )
