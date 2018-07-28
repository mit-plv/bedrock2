#!/bin/sh

if [ "$#" -ne 1 ] || ! [ -f "$1" ]; then
  echo "Usage: $0 COQ_FILE" >&2
  exit 1
fi

#set -x

f=$1
flast="$1Last"
target="$1o"

lineno=1

while true
do
    linecount=`cat "$f" | wc -l`
    if [ $lineno -gt $linecount ]; then
	break
    fi

    l=`sed -n "${lineno}p" < "$f"`

    case "$l" in
	*Require*|*Import*)
	    
	    echo "Trying to remove line $lineno: $l"
	    cp "$f" "$flast"
	    sed -i "${lineno}d" "$f"

	    if make "$target"; then
		lineno=`expr $lineno - 1`
		echo "line removal successful"
	    else
		cp "$flast" "$f"
		echo "line cannot be removed"
	    fi
	;;
	*) : ;;
    esac
    
    lineno=`expr $lineno + 1`

done

rm "$flast"
