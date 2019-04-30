#!/bin/bash
set -e

while : ; do
	make || true
	kill "$oldgtkwave" || true
	gtkwave --chdir /tmp/ --rcvar 'enable_vcd_autosave yes' --rcvar 'do_initial_zoom_fit yes' "$(realpath system.vcd)" &
	oldgtkwave=$!
	inotifywait -e modify *.v -r . || true
done
