system.vcd: system.vvp program0.hex program1.hex program2.hex program3.hex
	vvp system.vvp
system.vvp: system.v mkTop.v
	iverilog \
	-y ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/ \
	-y ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/build/ \
	-y. -o system.vvp system.v
clean:
	rm -f system.vvp system-kami.vvp system-kami.log system.vcd program.hex program0.hex program1.hex program2.hex program3.hex system.json system.out.config system.bit system.svf
	rm -f PrintProgram.glob PrintProgram.vo PrintProgram.vok PrintProgram.vos
program.hex: PrintProgram.v
	(cd ../../end2end; "$(COQBIN)rocq" compile -Q ./src/end2end end2end -Q ../deps/coqutil/src/coqutil coqutil -Q ../deps/riscv-coq/src/riscv riscv -Q ../deps/kami/Kami/ Kami -Q ../processor/src/processor processor -Q ../bedrock2/src/bedrock2 bedrock2 -Q ../bedrock2/src/bedrock2Examples bedrock2Examples -Q ../compiler/src/compiler compiler -Q ../compiler/src/compilerExamples compilerExamples ../processor/integration/PrintProgram.v) > program.hex
program0.hex: program.hex
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 1' > $@
program1.hex: program.hex
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 2' > $@
program2.hex: program.hex
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 3' > $@
program3.hex: program.hex
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 0' > $@

system.json: program0.hex program1.hex program2.hex program3.hex system.v mkTop.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/FIFO2.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/SizedFIFO.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/build/mkBramInst.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/RegFileLoad.v
	yosys -p "synth_ecp5 -json system.json" system.v mkTop.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/FIFO2.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/SizedFIFO.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/build/mkBramInst.v ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/RegFileLoad.v
system.out.config: system.json
	nextpnr-ecp5 --json system.json --textcfg system.out.config --um5g-85k --package CABGA381 --lpf ecp5evn.lpf --freq 35
system.bit system.svf: system.out.config
	ecppack --svf system.svf system.out.config system.bit

# The same simulation with the processor regenerated from Kami: the Bluespec
# program is extracted from Kami and compiled with bsc (instead of using the
# checked-in mkTop.v), then the lightbulb program is run on it.
KAMI_VERILOG := ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog
# bsc's own Verilog primitives (FIFO2, RegFile, ...), next to the bsc binary.
BSC_VERILOG_LIB := $(dir $(shell command -v bsc))../lib/Verilog
.PHONY: kami-verilog bluespec-test
kami-verilog:
	$(MAKE) -C ../../deps/kami verilog
system-kami.vvp: kami-verilog system.v
	iverilog -y $(KAMI_VERILOG)/gen -y $(BSC_VERILOG_LIB) -y. -o system-kami.vvp system.v $(KAMI_VERILOG)/gen/mkTop.v
system-kami.log: system-kami.vvp program0.hex program1.hex program2.hex program3.hex
	vvp system-kami.vvp | tee system-kami.log
# lightbulb_init configures the GPIO (IOF off, pin 23 as output) and then
# talks to the LAN9250 over SPI; the first SPI byte is its read command 0x0b.
bluespec-test: system-kami.log
	! grep -q FAIL system-kami.log
	grep -q '^MMIO write 10012038 <= 0000003c' system-kami.log
	grep -q '^MMIO write 10012008 <= 00800000' system-kami.log
	grep -q '^SPI TX 0b' system-kami.log
