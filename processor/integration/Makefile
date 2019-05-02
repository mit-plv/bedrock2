system.vcd: system.vvp program.hex
	vvp system.vvp
system.vvp: system.v mkTop.v
	iverilog -y ../../deps/kami/Kami/Ext/BluespecFrontEnd/verilog/ -y. system.v -o system.vvp
clean:
	rm -f system.vvp system.vcd
program.hex: ../../compiler/src/examples/integration.v
	( cd ../../compiler && coqc -q \
		-Q ../bedrock2/src bedrock2 \
		-Q ../deps/coqutil/src coqutil \
		-Q ../deps/riscv-coq/src riscv \
		-Q lib lib -Q src compiler  \
		../compiler/src/examples/integration.v ) > program.hex
