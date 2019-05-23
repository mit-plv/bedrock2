#!/bin/sh

# make system.svf
openocd -f /usr/share/trellis/misc/openocd/ecp5-evn.cfg -c "transport select jtag; init; svf system.svf; exit"
