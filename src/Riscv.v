Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Import compiler.zcast.
Require Import compiler.PowerFunc.
Require Import compiler.RiscvBitWidths.
Require Import compiler.NameWithEq.
Require Import Coq.omega.Omega.

(* Comments between ``double quotes'' are from quotes from
   The RISC-V Instruction Set Manual
   Volume I: User-Level ISA
   Document Version 2.2
*)

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {Name: NameWithEq}. (* register name *)
  Notation Reg := (@name Name).
  Existing Instance eq_name_dec.

  Inductive Register: Set :=
    | RegO: Register
    | RegS: Reg -> Register.

  Inductive Instruction: Set :=
    | Addi(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Slti(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Sltiu(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Andi(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Ori(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Xori(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Slli(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction
    | Srli(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction
(*  | Srai(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction *)
    | Lui(rd: Register)(imm20: word wupper): Instruction
    | Add(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | And(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Or(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Xor(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Mul(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Slt(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sltu(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Beq(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bne(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Blt(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bltu(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bge(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bgeu(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Jal(rd: Register)(jimm20: word wupper): Instruction.

  Definition Seqz(rd: Register)(rs1: Register) := Sltiu rd rs1 $1.
  Definition Snez(rd: Register)(rs1: Register) := Sltu rd RegO rs1.
  Definition Nop := Addi RegO RegO $0.
  Definition InfiniteJal := Jal RegO (wneg $4).

  Class RiscvState(M: Type -> Type) := mkRiscvState {
    getRegister: Register -> M (word wXLEN);
    setRegister: Register -> (word wXLEN) -> M unit;
    loadInst: (word wXLEN) -> M Instruction; (* decode already included *)
    (* not yet:
    loadWord: (word wXLEN) -> M (word wXLEN);
    storeWord: (word wXLEN) -> (word wXLEN) -> M unit;
    *)
    getPC: M (word wXLEN);
    setPC: word wXLEN -> M unit;
  }.

  (* looks like it's the wrong way round, but that's because the argument order of combine is
     unintuitive *)
  Definition lossless_shl{sz: nat}(v: word sz)(n: nat): word (n + sz) := combine (wzero n) v.

  Goal lossless_shl (WO~0~1~1~0~1)%word 4 = (WO~0~1~1~0~1~0~0~0~0)%word. reflexivity. Qed.

  Definition signed_imm_to_word(v: word wimm): word wXLEN.
    refine (nat_cast word _ (sext v (wXLEN - wimm))). bitwidth_omega.
  Defined.

  Definition signed_jimm_to_word(v: word wupper): word wXLEN.
    refine (nat_cast word _ (sext (lossless_shl v 1) (wXLEN - wupper - 1))). bitwidth_omega.
  Defined.

  Definition signed_bimm_to_word(v: word wimm): word wXLEN.
    refine (nat_cast word _ (sext (lossless_shl v 1) (wXLEN - wimm - 1))). bitwidth_omega.
  Defined.

  Definition upper_imm_to_word(v: word wupper): word wXLEN.
    refine (nat_cast word _ (sext (lossless_shl v wimm) (wXLEN - wInstr))). bitwidth_omega.
  Defined.

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with

    (* ``ADDI adds the sign-extended 12-bit immediate to register rs1. Arithmetic overflow is
       ignored and the result is simply the low XLEN bits of the result.'' *)
    | Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x ^+ (signed_imm_to_word imm12))

    (* ``SLTI (set less than immediate) places the value 1 in register rd if register rs1 is
       less than the sign-extended immediate when both are treated as signed numbers, else 0 is
       written to rd.'' *)
    | Slti rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if wslt_dec x (signed_imm_to_word imm12) then $1 else $0)

    (* ``SLTIU is similar but compares the values as unsigned numbers (i.e., the immediate is
       first sign-extended to XLEN bits then treated as an unsigned number).'' *)
    | Sltiu rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if wlt_dec x (signed_imm_to_word imm12) then $1 else $0)

    (* ``ANDI, ORI, XORI are logical operations that perform bitwise AND, OR, and XOR on register
       rs1 and the sign-extended 12-bit immediate and place the result in rd.'' *)
    | Andi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (wand x (signed_imm_to_word imm12))
    | Ori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (wor x (signed_imm_to_word imm12))
    | Xori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (wxor x (signed_imm_to_word imm12))

    (* ``SLLI is a logical left shift (zeros are shifted into the lower bits);
       SRLI is a logical right shift (zeros are shifted into the upper bits); and SRAI is an
       arithmetic right shift (the original sign bit is copied into the vacated upper bits).'' *)
    | Slli rd rs1 shamt =>
        x <- getRegister rs1;
        setRegister rd (wlshift x (wordToNat shamt))
    | Srli rd rs1 shamt =>
        x <- getRegister rs1;
        setRegister rd (wrshift x (wordToNat shamt))
 (* | Srai rd rs1 shamt => *)

    (* RV32I: ``LUI (load upper immediate) is used to build 32-bit constants and uses the U-type
       format. LUI places the U-immediate value in the top 20 bits of the destination register rd,
       filling in the lowest 12 bits with zeros.''
       RV64I: ``LUI (load upper immediate) uses the same opcode as RV32I. LUI places the 20-bit
       U-immediate into bits 31-12 of register rd and places zero in the lowest 12 bits. The 32-bit
       result is sign-extended to 64 bits. *)
    | Lui rd imm20 =>
        setRegister rd (upper_imm_to_word imm20)

    (* ``ADD and SUB perform addition and subtraction respectively. Overflows are ignored and
       the low XLEN bits of results are written to the destination. *)
    | Add rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^+ y)
    | Sub rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^- y)

    (* ``SLT and SLTU perform signed and unsigned compares respectively, writing 1 to rd
       if rs1 < rs2, 0 otherwise.'' *)
    | Slt rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if wslt_dec x y then $1 else $0)
    | Sltu rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if wlt_dec x y then $1 else $0)

    (* ``AND, OR, and XOR perform bitwise logical operations.'' *)
    | And rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (wand x y)
    | Or rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (wor x y)
    | Xor rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (wxor x y)

    (* ``The jump and link (JAL) instruction uses the J-type format, where the J-immediate encodes
       a signed offset in multiples of 2 bytes. The offset is sign-extended and added to the pc to
       form the jump target address. Jumps can therefore target a +/- 1 MiB range. JAL stores the
       address of the instruction following the jump (pc+4) into register rd.'' *)
    | Jal rd jimm20 =>
        pc <- getPC;
        setRegister rd (pc ^+ $4);;
        setPC (pc ^+ (signed_jimm_to_word jimm20))
    (* Note: The following is not yet implemented:
       ``The JAL and JALR instructions will generate a misaligned instruction fetch exception
       if the target address is not aligned to a four-byte boundary.''
       Also applies to the branch instructions. *)

    (* ``All branch instructions use the B-type instruction format. The 12-bit B-immediate encodes
       signed offsets in multiples of 2, and is added to the current pc to give the target address.
       The conditional branch range is +/- 4 KiB.'' *)

    (* ``BEQ and BNE take the branch if registers rs1 and rs2 are equal or unequal respectively.'' *)
    | Beq rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then (setPC (pc ^+ (signed_bimm_to_word sbimm12))) else Return tt
    | Bne rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then Return tt else (setPC (pc ^+ (signed_bimm_to_word sbimm12)))

    (* ``BLT and BLTU take the branch if rs1 is less than rs2, using signed and unsigned comparison
       respectively.'' *)
    | Blt rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wslt_dec x y then (setPC (pc ^+ (signed_bimm_to_word sbimm12))) else Return tt
    | Bltu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then (setPC (pc ^+ (signed_bimm_to_word sbimm12))) else Return tt

    (* ``BGE and BGEU take the branch if rs1 is greater than or equal to rs2, using signed and
       unsigned comparison respectively.'' *)
    | Bge rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wslt_dec x y then Return tt else (setPC (pc ^+ (signed_bimm_to_word sbimm12)))
    | Bgeu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then Return tt else (setPC (pc ^+ (signed_bimm_to_word sbimm12)))

    (* ``MUL performs an XLEN-bit x XLEN-bit multiplication and places the lower XLEN bits in the
       destination register.'' *)
    | Mul rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^* y)
    end.

  Definition run1{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: M unit :=
    pc <- getPC;
    inst <- loadInst pc;
    setPC (pc ^+ $4);;
    execute inst.

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

  (*
  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fix rec(nSteps: nat) := match nSteps with
    | O => Return tt
    | S m =>
        pc <- getPC;
        inst <- loadInst pc;
        setPC (pc ^+ $4);;
        execute inst;;
        rec m
    end.
  *)

  Record RiscvMachine := mkRiscvMachine {
    instructionMem: word wXLEN -> Instruction;
    registers: Reg -> word wXLEN;
    pc: word wXLEN;
  }.

  Instance IsRiscvMachine: RiscvState (State RiscvMachine) :=
  {|
      getRegister := fun (reg: Register) =>
        match reg with
        | RegO => Return $0
        | RegS r => machine <- get; Return (machine.(registers) r)
        end;
      setRegister := fun (reg: Register) (v: word wXLEN) =>
        match reg with
        | RegO => Return tt
        | RegS r => machine <- get;
                    match machine with
                    | mkRiscvMachine imem regs pc =>
                        put (mkRiscvMachine imem 
                                            (fun reg2 => if dec (r = reg2) then v else regs reg2)
                                            pc)
                    end
        end;
      loadInst := fun (addr: word wXLEN) =>
        im <- gets instructionMem;
        Return (im addr);
      getPC := gets pc;
      setPC := fun (newPC: word wXLEN) =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc =>
            put (mkRiscvMachine imem regs newPC)
        end;
  |}.

  Definition initialRiscvMachine(imem: list Instruction): RiscvMachine := {|
    instructionMem := fun (i: word wXLEN) => nth (Nat.div (wordToNat i) 4) imem InfiniteJal;
    registers := fun (r: Reg) => $0;
    pc := $0
  |}.

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)


Require compiler.RiscvBitWidths32.

Module MachineTest.
  Import compiler.RiscvBitWidths32.

  Instance NatName: NameWithEq := {| name := nat |}.

  Definition m1: RiscvMachine := {|
    instructionMem := fun _ => Nop;
    registers := fun _ => $22;
    pc := $33
  |}.

  Definition prog1: State RiscvMachine (word 32) :=
    x <- getRegister (RegS 2);
    setRegister (RegS 2) (x ^+ $3);;
    getRegister (RegS 2).

  Goal evalState prog1 m1 = $25. reflexivity. Qed.

End MachineTest.
