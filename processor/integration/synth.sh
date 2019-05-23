#!/bin/sh
set -eux
yosys -p "synth_ecp5 -json system.json" system.v mkTop.v /home/fiat/plv/bedrock2/deps/kami/Kami/Ext/BluespecFrontEnd/verilog/FIFO2.v
nextpnr-ecp5 --json system.json --textcfg system.out.config --um5g-85k --package CABGA381 --lpf ecp5evn.lpf --freq 50
ecppack --svf system.svf system.out.config system.bit
