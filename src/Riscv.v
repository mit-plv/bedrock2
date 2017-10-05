Require Import bbv.Word.
Require Import compiler.StateMonad.

(* allows inifinite number of registers *)
Definition Register := nat.

Class RiscvState(Val: Type)(M: Type -> Type) := mkRiscvState {
  getRegister: Register -> M Val;
  setRegister: Register -> Val -> M unit;
  loadByte: Val -> M (word 8);
  loadHalf: Val -> M (word 16);
  loadWord: Val -> M (word 32);
  loadDouble: Val -> M (word 64);
  storeByte: word 8 -> Val -> M unit;
  storeHalf: word 16 -> Val -> M unit;
  storeWord: word 32 -> Val -> M unit;
  storeDouble: word 64 -> Val -> M unit;
  (* control and status registers: read-only for now *)
  loadCSR: nat -> M (word 32);
  getPC: M (word 32);
  setPC: word 32 -> M unit;
  (* TODO why is "step" here? *)
}.

Inductive Instruction: Set :=
  | Andi(rd: Register)(rs1: Register)(imm12: word 12): Instruction
  | Add(rd: Register)(rs1: Register)(rs2: Register): Instruction
  | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction.

Definition execute{Val: Type}{M: Type -> Type}{MM: Monad M}{RVS: RiscvState Val M}
  (i: Instruction): M unit
:= match i with
  | Andi rd rs1 imm12 =>
      x <- getRegister rs1;
      setRegister rd x (* TODO and imm12 *)
  | Add rd rs1 rs2 =>
      x <- getRegister rs1;
      y <- getRegister rs2;
      setRegister rd x (* TODO + y *)
  | Sub rd rs1 rs2 =>
      x <- getRegister rs1;
      y <- getRegister rs2;
      setRegister rd x (* TODO - y *)
  end.

