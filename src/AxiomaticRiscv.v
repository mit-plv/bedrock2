Require Import riscv.util.Monads.
Require Import compiler.Common.
Require Import riscv.Decode.
Require Import riscv.Program.
Require Import riscv.Minimal.
Require Import riscv.FunctionMemory.
Require Import riscv.RiscvBitWidths.

Set Implicit Arguments.


Section AxiomaticRiscv.

  Context {Bw: RiscvBitWidths}.

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Instance State_is_RegisterFile: RegisterFile state Register (word wXLEN) := {|
    getReg rf r := match get rf r with
                   | Some v => v
                   | None => $0
                   end;
    setReg := put;
    initialRegs := empty;
  |}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) (word wXLEN) _ _ IsRiscvMachine}.  

  (* Note: Register 0 is not considered valid because it cannot be written *)
  Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

  Local Notation RiscvMachine := (@RiscvMachine Bw (mem wXLEN) state).

  Lemma Bind_getRegister0: forall {A: Type} (f: word wXLEN -> OState RiscvMachine A),
      Bind (getRegister Register0) f = f $0.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma Bind_getRegister: forall {A: Type} x
                                 (f: word wXLEN -> OState RiscvMachine A)
                                 (initialL: RiscvMachine),
      valid_register x ->
      execState (Bind (getRegister x) f) initialL =
      execState (f (getReg initialL.(core).(registers) x)) initialL.
  Proof.
    intros. simpl.
    destruct_one_match.
    - exfalso. unfold valid_register, Register0 in *. omega.
    - reflexivity.
  Qed.

  Lemma Bind_setRegister: forall {A: Type} x (v: word wXLEN)
                                 (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
      valid_register x ->
      execState (Bind (setRegister x v) f) initialL =
      execState (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL).
  Proof.
    intros. simpl.
    destruct_one_match.
    - exfalso. unfold valid_register, Register0 in *. omega.
    - reflexivity.
  Qed.

  Lemma Bind_setRegister0: forall {A: Type} (v: word wXLEN)
                                 (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
      execState (Bind (setRegister Register0 v) f) initialL =
      execState (f tt) initialL.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma Bind_getPC: forall {A: Type} (f: word wXLEN -> OState RiscvMachine A) (initialL: RiscvMachine),
      execState (Bind getPC f) initialL =
      execState (f initialL.(core).(pc)) initialL.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma Bind_setPC: forall {A: Type} (v: word wXLEN)
                                 (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
      execState (Bind (setPC v) f) initialL =
      execState (f tt) (with_nextPC v initialL).
  Proof.
    intros. simpl. reflexivity.
  Qed.
  
  Lemma Bind_step: forall {A: Type} (f: unit -> OState RiscvMachine A) m,
      execState (Bind step f) m =
      execState (f tt) (with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m)).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma execState_step: forall m,
      execState step m = with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m).
  Proof.
    intros. reflexivity.
  Qed.
  
  Lemma execState_Return: forall {S A} (s: S) (a: A),
      execState (Return a) s = s.
  Proof. intros. reflexivity. Qed.

End AxiomaticRiscv.

Existing Instance State_is_RegisterFile.
