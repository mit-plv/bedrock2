Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Export Coq.omega.Omega.

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
  | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction
  | Mul(rd: Register)(rs1: Register)(rs2: Register): Instruction
  | Beq(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction
  | Blt(rs1: Register)(rs2: Register)(sbimm12: word 12): Instruction.

Definition t: word 4 := $3.

Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (Nat.compare sz sz') eqn: E.
  - apply nat_compare_eq in E. rewrite E in n. exact n.
  - apply nat_compare_Lt_lt in E.
Abort. (*
nat_compare_Gt_gt
forall n m : nat, (n ?= m) = Gt -> n > m
nat_compare_Lt_lt
forall n m : nat, (n ?= m) = Lt -> n < m
nat_compare_eq
*)

(* TODO how to define such a size cast function properly? *)
Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz <= sz')).
  - replace sz' with (sz + (sz' - sz)) by (apply le_plus_minus_r; assumption).
    exact (zext n _).
  - replace sz with ((sz - sz') + sz') in n.
    exact (split2 _ _ n).
    apply Nat.sub_add.
    apply Nat.lt_nge in n0.
    apply Nat.lt_le_incl. assumption.
Defined.

Eval cbv in (zcast 1 t). (* TODO why does this not simplify properly? *)

(*
Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz < sz')).
  - replace sz' with (sz + (sz' - sz)) by omega.
    exact (zext n _).
  - replace sz with ((sz - sz') + sz') in n by omega.
    exact (split2 _ _ n).
Defined.
too expensive to calculate
*)

(* less flexible than inlining it because if can act on any 2-constructor type
Definition when{M: Type -> Type}{MM: Monad M}(cond: bool)(action: M unit): M unit :=
  if cond then action else Return tt. *)

Definition execute{w: nat}{M: Type -> Type}{MM: Monad M}{RVS: RiscvState (word w) M}
  (i: Instruction): M unit
:= match i with
  | Andi rd rs1 imm12 =>
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
  | Beq rs1 rs2 sbimm12 =>
      x <- getRegister rs1;
      y <- getRegister rs2;
      pc <- getPC;
      if weq x y then (setPC (pc ^+ (zcast 32 sbimm12))) else Return tt
  | Blt rs1 rs2 sbimm12 =>
      x <- getRegister rs1;
      y <- getRegister rs2;
      pc <- getPC;
      if wlt_dec x y then (setPC (pc ^+ (zcast 32 sbimm12))) else Return tt
  end.
