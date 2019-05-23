#!/bin/sh
set -eux
/usr/bin/time yosys -p "synth_ecp5 -json synth.json" system.v mkTop.v /home/fiat/plv/bedrock2/deps/kami/Kami/Ext/BluespecFrontEnd/verilog/FIFO2.v
nextpnr-ecp5 --json system.json --um5g-85k --package CABGA381
