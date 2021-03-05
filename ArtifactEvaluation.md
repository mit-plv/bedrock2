## Getting Started Guide

First, please note that building the Coq development takes over three hours of CPU time and requires 8GB of RAM per CPU.
You may prefer to do that asynchronously, but you can also inspect the source code as outlined below while it is building.

We provide a disk image in .vdi format that boots into a Linux terminal environment accessible over SSH.
You can get VirtualBox from your operating system's repositories or virtualbox.org.
Here are instructions for using VirtualBox:

```sh
tar -xfa lightbulb.tar.gz
VBoxManage registervm "$(realpath lightbulb/lightbulb.vbox)"
VBoxManage startvm lightbulb
# hide the window that pops up
sleep 5
ssh artifact@localhost -p 8022
```

You can then kick off the build process in the VM:

```sh
make -C bedrock2 && make -C bedrock2/processor/integration system.bit
```

The directory `bedrock2-prebuilt` contains the results of our execution of that command, so feel free to open up another SSH connection and follow along.

The VM contains Emacs+ProofGeneral and vim+coqtail available for stepping through the Coq files.
In case you haven't used either, pick whichever one sounds better:
in ProofGeneral, ctrl+enter evaluates until the cursor, and in coqtail, the corresponding shortcut is \ c l.

Try stepping through the following file (it has no dependencies):

```sh
emacs bedrock2/deps/coqutil/src/coqutil/Word/Interface.v
vim bedrock2/deps/coqutil/src/coqutil/Word/Interface.v
```

## Step-by-Step Instructions

Overview of claims from the paper supported by the artifact (more details on each below):
- The top-level theorem is fully proven in Coq, only references a small number of definitions, and looks reasonable as a translation of our high-level intent.
- The code may be broken into lines in different categories (implementation/interface/interesting proof/low-insight proof), and our process of computing line counts per category is reasonable.
- Our Coq code base can really generate a reasonable RISC-V binary.
- Our Coq code base can really generate a reasonable Bluespec hardware design.

Overview of claims from the paper *not* supported by the artifact:
- It is too hard for us to help you recreate our physical setup, with a specific model of FPGA, a specific network card, and a GPIO-compatible power strip.  (You could probably find a compatible lightbulb to plug into the power strip, though. `:-P`)  See paper Figure 2 for what it would look like.


### The toplevel theorem and the trusted code base (TCB) of Coq definitions

The toplevel theorem of our development is `Theorem end2end_lightbulb` in `end2end/src/end2end/End2EndLightbulb.v`. If you process that file in your Coq IDE all the way to the end and then add and run the command

```
Print Assumptions end2end_lightbulb.
```

you should see some messages of the form `Fetching opaque proofs from disk for ...`, followed by a list of unproven axioms on which that theorem depends.
This list should only contain the following four axioms from the standard library, which are a sound extension to Coq's logic:

```
PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
```

We encourage you to check that `Theorem end2end_lightbulb` in that file matches what we show in section 5.9, "The end-to-end theorem" (up to renaming of `Semantics.Behavior` into `Trace` and reformulating it with an existential instead of an `Inductive`), and to locate the definitions referenced in this theorem statement by (if you're using Proof General) placing the cursor on top of a definition and running `C-c C-a C-l` (or running `Locate nameOfDefinition.` or grepping for it) to find the definitions referenced in the theorem. Of interest:

- `bytes_at`, just above in the same file, asserts that given bytes are at a given memory address.
- `instrencode lightbulb_insts` are the bytes that we print as a hexdump further up in the same file, on the line `let x := eval cbv in (instrencode lightbulb_insts) in idtac x.`. Note that our theorem is about this concrete list of bytes, which we can compute inside Coq, so the meaning of the theorem does not depend on any high-level language or on any compilation function or compilation specification.
- `Semantics.Behavior` in `deps/kami/Kami/Semantics.v` defines what it means for a Kami module (here we're looking at the 4-stage pipelined processor `p4mm` whose memory equals `mem0`) to have a behavior, expressed as an MMIO interaction trace.
- `KamiRiscv.KamiLabelSeqR t t'` converts trace formats
- `goodHlTrace`, defined in `bedrock2/src/bedrock2Examples/lightbulb_spec.v`, is the specification of the expected behavior, expressed as a regular expression over MMIO events. We recommend reading this file backwards, in order to get a top-down unfolding of each definition, until you see the individual MMIO events in the `spi_...` definitions. The definition `one` is a regular expression over traces that asserts that the trace consists of exactly one given MMIO event, and it is the primitive building block to specify the protocol.
- `bedrock2/src/bedrock2/TracePredicate.v` contains the definitions needed to express regular expressions over traces, which are used to define `goodHlTrace`.


### Checking the line number counts

The numbers of Table 4 in the paper (Lines of code) can be reproduced as follows.
First, note that `etc/all-files.txt` assigns a category to each file.
To check that we did not miss any file, run

```
etc/completenesscheck.sh
```

whose output should only contain paths to Verilog files (it lists all .v files that recursive `find` finds but are not listed in `etc/all-files.txt`, and note that unfortunately, Coq and Verilog both use the .v file extension).
Then, run

```
python etc/allcount.py < etc/all-files.txt
```

which parses the annotations like eg `(*tag:proof*)` or `(*tag:obvious*)`, and whenever it encounters such a tag, it changes the line counter to be incremented.
It outputs two `.tex` files, and you can run

```
cat loc.tex
cat loc_excluded.tex
```

to inspect them and compare them to the values reported in the paper.
(Note that the number of "unrelated" lines of code changed because previously, we were also counting Verilog files, which also end in .v, and now we don't count them any more).

### Inspecting the Coq-generated RISC-V binary

In your Coq IDE, open the file `end2end/src/end2end/End2EndLightbulb.v` and process up to the line

```
    let x := eval cbv in (instrencode lightbulb_insts) in idtac x.
```

This prints a hexdump of the binary into the response window.

In `end2end/Makefile`, there are commands to turn this hexdump into an object file that the standard RISC-V GNU `objdump` can read. You can run them by `cd`ing into `end2end` and running

```
make lightbulb.o
```

Then, you can use

```
riscv32-elf-objdump -D lightbulb.o | less
```

to inspect the generated binary. The Kami processor starts executing at address 0.
The first few commands should look like this:

```
   0:	00002137                lui	sp,0x2
   4:	00014113                xori	sp,sp,0
   8:	3d5000ef                jal	ra,0xbdc
   c:	358000ef                jal	ra,0x364
  10:	ffdff06f                j	0xc
  14:	fe810113                addi	sp,sp,-24 # 0x1fe8
  18:	00112423                sw	ra,8(sp)
  1c:	00412023                sw	tp,0(sp)
  20:	00312223                sw	gp,4(sp)
  24:	01412183                lw	gp,20(sp)
  28:	fe312e23                sw	gp,-4(sp)
  2c:	038000ef                jal	ra,0x64
  30:	ff812203                lw	tp,-8(sp)
  34:	00020463                beqz	tp,0x3c
  38:	0100006f                j	0x48
  3c:	0f0000ef                jal	ra,0x12c
  40:	ff812183                lw	gp,-8(sp)
  44:	ffc12203                lw	tp,-4(sp)
  48:	00312623                sw	gp,12(sp)
  4c:	00412823                sw	tp,16(sp)
  50:	00012203                lw	tp,0(sp)
  54:	00412183                lw	gp,4(sp)
  58:	00812083                lw	ra,8(sp)
  5c:	01810113                addi	sp,sp,24
  60:	00008067                ret
```

Some explanation of the code, using "line" numbers to refer to the addresses written at the starts of lines:
Lines 0-4 initialize the stackpointer.
Lines 8-10 correspond to the top-level program structure `init(); while(1) loop()`.
Note that all code is position-independent, but `objdump` pretty-prints it in a way that makes it look position-dependent: For instance, in `j 0xc`, the target address `0xc` is displayed as an absolute address, but the encoding uses the `jal` instruction with destination register 0 (thus printed as `j`), which stores a relative address. You can compare the `objdump` output to our own way of displaying assembly, in your Coq IDE at the line quoted above, and you should see the following:

```
           lui     x2, 8192
           xori    x2, x2, 0
           jal     x1, 3028
           jal     x1, 856
           jal     x0, -4
           addi    x2, x2, -24
           sw      x2, x1, 8
           sw      x2, x4, 0
           sw      x2, x3, 4
           lw      x3, x2, 20
           sw      x2, x3, -4
           jal     x1, 56
           lw      x4, x2, -8
           beq     x4, x0, 8
           jal     x0, 16
           jal     x1, 240
           lw      x3, x2, -8
           lw      x4, x2, -4
           sw      x2, x3, 12
           sw      x2, x4, 16
           lw      x4, x2, 0
           lw      x3, x2, 4
           lw      x1, x2, 8
           addi    x2, x2, 24
           jalr    x0, x1, 0
```

Above, you can also see the Coq-generated symbol table:

```
  symbols := [("init", 3016); ("lan9250_init", 2756); ("lan9250_mac_write", 2572);
             ("lan9250_readword", 2116); ("lan9250_wait_for_boot", 1956); ("lan9250_writeword", 1552);
             ("lightbulb_handle", 1140); ("lightbulb_init", 1036); ("lightbulb_loop", 904);
             ("loop", 848); ("recvEthernet", 448); ("spi_read", 280); ("spi_write", 80);
             ("spi_xchg", 0)] : list (string * Z)
```

These are decimal offsets of the function positions in the assembly, relative to the first function after the `init(); while(1) loop()` code (which ends at `0x14`=20), so if you add 20 to the numbers of that table and convert to hex, you can find the corresponding position in the `objdump` output.
For instance, for `spi_read`, 280+20=300=`0x12c`, and indeed, at `0x12c`, you'll find the start of a new function:

```
 128:	00008067                ret
 12c:	fd410113                addi	sp,sp,-44
 130:	02112023                sw	ra,32(sp)
 134:	00612023                sw	t1,0(sp)
 138:	00712223                sw	t2,4(sp)
 13c:	00812423                sw	s0,8(sp)
 140:	00912623                sw	s1,12(sp)
 144:	00a12823                sw	a0,16(sp)
 148:	00312a23                sw	gp,20(sp)
 14c:	00512c23                sw	t0,24(sp)
 150:	00412e23                sw	tp,28(sp)
 154:	fff00213                li	tp,-1
 158:	05a00193                li	gp,90
 15c:	000002b7                lui	t0,0x0
 160:	fff2c293                not	t0,t0
 164:	02028e63                beqz	t0,0x1a0
 168:	00100313                li	t1,1
 16c:	406282b3                sub	t0,t0,t1
 170:	100243b7                lui	t2,0x10024
 174:	04c3c393                xori	t2,t2,76
 178:	0003a203                lw	tp,0(t2) # 0x10024000
 17c:	01f00413                li	s0,31
 180:	008254b3                srl	s1,tp,s0
 184:	00048463                beqz	s1,0x18c
 188:	0140006f                j	0x19c
 18c:	0ff00513                li	a0,255
 190:	00a271b3                and	gp,tp,a0
 194:	0052c2b3                xor	t0,t0,t0
 198:	00424233                xor	tp,tp,tp
 19c:	fc9ff06f                j	0x164
 1a0:	02312223                sw	gp,36(sp)
 1a4:	02412423                sw	tp,40(sp)
 1a8:	00012303                lw	t1,0(sp)
 1ac:	00412383                lw	t2,4(sp)
 1b0:	00812403                lw	s0,8(sp)
 1b4:	00c12483                lw	s1,12(sp)
 1b8:	01012503                lw	a0,16(sp)
 1bc:	01412183                lw	gp,20(sp)
 1c0:	01812283                lw	t0,24(sp)
 1c4:	01c12203                lw	tp,28(sp)
 1c8:	02012083                lw	ra,32(sp)
 1cc:	02c10113                addi	sp,sp,44
 1d0:	00008067                ret
```

It starts by decrementing the stack pointer and saving the modified registers.
Note the load-word instruction on line 178: It loads from the hardcoded address `0x10024000 + 76_dec`, which is `Ox1002404c`, which you can find in the source code of `spi_read` in `bedrock2/src/bedrock2Examples/SPI.v`:

```
Definition spi_read : function :=
(*tag:workaround*)
  let b : String.string := "b" in
  let busy : String.string := "busy" in
  let i : String.string := "i" in
  let SPI_READ_ADDR := Ox"1002404c" in
  (*tag:code*)
  ("spi_read", (nil, (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (constr:(Ox"5a"));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_READ_ADDR);
      if !(busy >> constr:(31)) {
        b = (busy & constr:(Ox"ff"));
        i = (i^i);
        busy = (busy ^ busy)
      }
    }
  ))).
```

### How the processor and code end up in the FPGA

First, the CPU design needs to be extracted into a format that the FPGA synthesis tools accept. 
That happens in `~/bedrock2/deps/kami` .
Rule `proc_ext` in `Makefile` coordinates the extraction of the Kami processor, culminating in `Proc.bsv` in the directory `kami`.

The the extraction process sadly loses method names, but the file should still be recognizable as a Bluespec implementation of a simple processor.
Rule `verilog_comp` in Kami/Ext/BluespecFrontEnd/verilog/Makefile` calls the Bluespec compiler `bsc` to generate Verilog code `mkTop.v`.
We recommend against trying to read the generated Verilog code itself, but the module signature is instructive:
the processor takes a clock and a reset signal and allows its environment to obtain memory requests and send responses to them.
This is what the verification boundary of our system looks like after translation from Bluespec to Verilog.

```verilog
module mkTop(CLK,
	     RST_N,

	     EN_obtain_rq_get,
	     obtain_rq_get,
	     RDY_obtain_rq_get,

	     send_rs_put,
	     EN_send_rs_put,
	     RDY_send_rs_put);
```

Everything comes together in `~/bedrock2/processor/integration` .
Module `system` in `system.v` contains the Verilog glue that ties together the CPU from `mkTop.v`, the FPGA block ram instantiated in module `ram`, and the RISC-V code from `program.hex`.
The same `system` module also implements the SPI and GPIO peripherals the code accesses through MMIO.
The last three rules in `Makefile` take care of compiling `system.v` and its dependencies for the specific FPGA we used;
the three rules correspond to the traditional steps of synthesis, place & route, and bistream generation.

The interface of the system `module` is at the physical boundary of the FPGA, with one declaration per port between the FPGA and the rest of the circuitry.

```verilog
module system(
  input wire clk,
  input wire spi_miso,
  output reg [7:0] led = 8'hff,
  output reg spi_clk = 0,
  output wire spi_mosi,
  output reg spi_csn = 1,
  output reg lightbulb = 0
);
```

Finally, `ecp5evn.lpf` describes the mapping between the `system.v` module interface and the physical pins of the FPGA.
To reproduce our physical experiment using the Lattice ECP5-85k evaluation board and Microchip LAN9250 development board, the header pins on the two would need to be connected with jumper cables according with the same mapping.
Then `prog.sh` can be used to push the processor design (and code ROM) into the FPGA.

## Software in the VM

Here is an exhaustive list of software included in the VM, excerpted from the script that built it.

Artifact git repository: https://github.com/mit-plv/bedrock2 --branch=lightbulb_artifact 
Arch Linux packages: base mkinitcpio linux syslinux openssh sudo git make which gcc ocamlbuild ocaml-findlib python iverilog riscv32-elf-binutils vim emacs-nox coq # 8.13.1
Arch Linux User Repository packages and versions: bluespec-git-r424.88d4eef trellis-git-r992.210a0a7 nextpnr-git-r3205.1aab019f yosys-git-0.9+3981.r10628.375af199e
Coq frontend git repositories: https://github.com/let-def/vimbufsync.git https://github.com/whonore/coqtail.git https://github.com/ProofGeneral/PG
