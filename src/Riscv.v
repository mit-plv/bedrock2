Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Import compiler.zcast.
Require Import compiler.PowerFunc.
Require Import Coq.omega.Omega.

Section Riscv.
  Context {wlit: nat}. (* bit width of literals *)
  Context {wdiff: nat}. (* bit width difference between literals and words *)
  Notation w := (wlit + wdiff).
  Context {wjimm: nat}. (* bit width of "jump immediates" *)
  Context {w_lbound: w >= wjimm}.
  Context {Reg: Set}. (* register name *)

  Inductive Register: Set :=
    | RegO: Register
    | RegS: Reg -> Register.

  Inductive Instruction: Set :=
    | Addi(rd: Register)(rs1: Register)(imm12: word wlit): Instruction
    | Add(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Mul(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sltu(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sltiu(rd: Register)(rs1: Register)(imm12: word wlit): Instruction
    | And(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Beq(rs1: Register)(rs2: Register)(sbimm12: word wlit): Instruction
    | Bne(rs1: Register)(rs2: Register)(sbimm12: word wlit): Instruction
    | Blt(rs1: Register)(rs2: Register)(sbimm12: word wlit): Instruction
    | Bge(rs1: Register)(rs2: Register)(sbimm12: word wlit): Instruction
    | Jal(rd: Register)(jimm20: word wjimm): Instruction.

  Definition Seqz(rd: Register)(rs1: Register) := Sltiu rd rs1 $1.
  Definition Snez(rd: Register)(rs1: Register) := Sltu rd RegO rs1.
  Definition Nop := Addi RegO RegO $0.
  Definition InfiniteJal := Jal RegO (wneg $4).

  Class RiscvState(M: Type -> Type) := mkRiscvState {
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

  Definition signed_lit_to_word(v: word wlit): word w := nat_cast word eq_refl (sext v wdiff).

  Definition signed_jimm_to_word(v: word wjimm): word w.
    refine (nat_cast word _ (sext v (w - wjimm))). clear -w_lbound. abstract omega.
  Defined.

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with
    | Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x ^+ (signed_lit_to_word imm12))
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
    | Sltu rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if wlt_dec x y then $1 else $0)
    | Sltiu rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if wlt_dec x (signed_lit_to_word imm12) then $1 else $0)
    | And rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x ^& y)
    | Beq rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then (setPC (pc ^+ (signed_lit_to_word sbimm12))) else Return tt
    | Bne rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if weq x y then Return tt else (setPC (pc ^+ (signed_lit_to_word sbimm12)))
    | Blt rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then (setPC (pc ^+ (signed_lit_to_word sbimm12))) else Return tt
    | Bge rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        if wlt_dec x y then Return tt else (setPC (pc ^+ (signed_lit_to_word sbimm12)))
    | Jal rd jimm20 =>
        pc <- getPC;
        setRegister rd (pc ^+ $4);;
        setPC (pc ^+ (signed_jimm_to_word jimm20))
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
End Riscv.
