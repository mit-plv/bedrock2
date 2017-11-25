Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Import compiler.zcast.

Section Riscv.
  Context {w: nat}. (* bit width *)
  Context {Register: Set}. (* register name *)

  Inductive Instruction: Set :=
    | Addi(rd: Register)(rs1: Register)(imm12: word 12): Instruction
    | Add(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Mul(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | And(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Beq(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction
    | Bne(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction
    | Blt(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction
    | Bge(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction
    | Jal(rd: Register)(jimm20: word 20): Instruction.

  Class RiscvState(M: Type -> Type) := mkRiscvState {
    R0: Register;
    getRegister: Register -> M (word w);
    setRegister: Register -> (word w) -> M unit;
    loadInst: (word w) -> M Instruction; (* decode already included *)
    (* not yet:
    loadWord: (word w) -> M (word w);
    storeWord: (word w) -> (word w) -> M unit;
    *)
    getPC: M (word w);
    setPC: word w -> M unit;
  }.

  Definition InfiniteJal{M: Type -> Type}{RVS: RiscvState M} := Jal R0 (wneg $4).

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with
    | Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x ^+ (zcast w imm12))
    | Add rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^+ y)
    | Sub rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^- y)
    | Mul rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^* y)
    | And rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^& y)
    | Beq rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then (setPC (pc ^+ (zcast w sbimm12))) else Return tt
    | Bne rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then Return tt else (setPC (pc ^+ (zcast w sbimm12)))
    | Blt rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then (setPC (pc ^+ (zcast w sbimm12))) else Return tt
    | Bge rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then Return tt else (setPC (pc ^+ (zcast w sbimm12)))
    | Jal rd jimm20 =>
        pc <- getPC;
        setRegister rd (pc ^+ $4);;
        setPC (pc ^+ (zcast w jimm20))
    end.

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fix rec(nSteps: nat) := match nSteps with
    | O => Return tt
    | S m =>
        pc <- getPC;
        inst <- loadInst pc;
        setPC (pc ^+ $4);;
        execute inst
    end.

End Riscv.
