system.vcd: system.vvp program0.hex program1.hex program2.hex program3.hex
	vvp system.vvp
system.vvp: system.v mkTop.v
	iverilog \
	-y ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/ \
	-y ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/build/ \
	-y. -o system.vvp system.v
clean:
	rm -f system.vvp system.vcd program.hex program0.hex program1.hex program2.hex program3.hex system.json system.out.config system.bit system.svf
	rm -f PrintProgram.glob PrintProgram.vo PrintProgram.vok PrintProgram.vos
program.hex: PrintProgram.v
	(cd ../../end2end; coqc -Q ./src/end2end end2end -Q ../deps/coqutil/src/coqutil coqutil -Q ../deps/riscv-coq/src/riscv riscv -Q ../deps/kami/Kami/ Kami -Q ../processor/src/processor processor -Q ../bedrock2/src/bedrock2 bedrock2 -Q ../bedrock2/src/bedrock2Examples bedrock2Examples -Q ../compiler/src/compiler compiler -Q ../compiler/src/compilerExamples compilerExamples ../processor/integration/PrintProgram.v) > program.hex
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
