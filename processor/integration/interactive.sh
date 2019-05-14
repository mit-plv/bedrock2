#!/bin/bash
set -e
gtkwave=""
trap 'kill $gtkwave' EXIT

while : ; do
	if make
	then
		kill "$gtkwave" || true
		gtkwave --chdir /tmp/ --rcvar 'enable_vcd_autosave yes' --rcvar 'do_initial_zoom_fit yes' "$(realpath system.vcd)" &
		gtkwave=$!
	else
		kill "$gtkwave" || true
	fi
	inotifywait -e modify system.v || true
done
