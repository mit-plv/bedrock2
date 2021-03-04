/* Note: this wrapper file and the gcc riscv toolchain, are not needed to build our
   system, but if you want to use objdump to inspect the binary, we need this wrapper
   to turn the binary into a .o file that objdump can read. */
.section .text
.incbin "lightbulb.bin"
