## Getting Started Guide




## Step-by-Step Instructions

Overview of claims from the paper supported by the artifact (more details on each below):
- The top-level theorem is fully proven in Coq, only references a small number of definitions, and looks reasonable as a translation of our high-level intent.
- The code may be broken into lines in different categories (implementation/interface/interesting proof/low-insight proof), and our process of computing line counts per category is reasonable.
- Our Coq code base can really generate a reasonable RISC-V binary.
- Our Coq code base can really generate a reasonable Bluespec hardware design.

Overview of claims from the paper *not* supported by the artifact:
- It is too hard for us to help you recreate our physical setup, with a specific model of FPGA, a specific network card, and a GPIO-compatible power strip.  (You could probably find a compatible lightbulb to plug into the power strip, though. `:-P`)  See paper Figure 2 for what it would look like.


### Tour through the Coq code, trusted code base

TODO Sam


### Checking the line number counts

The numbers of Table 4 in the paper (Lines of code) can be reproduced as follows.
First, note that `etc/all-files.txt` assigns a category to each file.
To check that we did not miss any file, run

```
etc/completenesscheck.sh
```

whose output should be empty (it lists all Coq files that recursive `find` finds but are not listed in `etc/all-files.txt`).
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
riscv32-unknown-linux-gnu-objdump -D lightbulb.o
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
