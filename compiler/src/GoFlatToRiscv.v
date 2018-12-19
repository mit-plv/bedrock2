Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.AxiomaticRiscv.
Require Import coqutil.Tactics.Tactics.


Section Axiomatic.

  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.
  Context {RVAX: AxiomaticRiscv Action M}.

  Hint Resolve
    spec_Bind
    spec_Return
    spec_getRegister
    spec_getRegister0
    spec_setRegister0
    spec_setRegister
    spec_loadWord
    spec_storeWord
    spec_getPC
    spec_setPC
    spec_step
    : spec_hints.

  Ltac t :=
    intros;
    refine (spec_Bind _ _ _ _ (fun a s => a = _ /\ s = _) _ _); cycle 1;
    [ intros;
      destruct_products;
      repeat match goal with
             | E: ?x = _ |- _ => is_var x; progress rewrite E; clear E
             end;
      eassumption
    | eauto with spec_hints ].


  Lemma go_getRegister: forall (initialL: RiscvMachineL) (x: Register) post (f: word -> M unit),
      valid_register x ->
      mcomp_sat (f (getReg initialL.(getRegs) x)) initialL post ->
      mcomp_sat (Bind (getRegister x) f) initialL post.
  Proof. t. Qed.

  Lemma go_getRegister0: forall (initialL: RiscvMachineL) post (f: word -> M unit),
      mcomp_sat (f (word.of_Z 0)) initialL post ->
      mcomp_sat (Bind (getRegister Register0) f) initialL post.
  Proof. t. Qed.

  Lemma go_setRegister0: forall initialL v post (f: unit -> M unit),
      mcomp_sat (f tt) initialL post ->
      mcomp_sat (Bind (setRegister Register0 v) f) initialL post.
  Proof. t. Qed.

  Lemma go_setRegister: forall initialL x v post (f: unit -> M unit),
      valid_register x ->
      mcomp_sat (f tt) (setRegs initialL (setReg initialL.(getRegs) x v)) post ->
      mcomp_sat (Bind (setRegister x v) f) initialL post.
  Proof. t. Qed.

  (* would make more sense on wrapped in ignore_unit_answer *)
  Lemma go_loadWord: forall initialL addr (v: w32) (f: w32 -> M unit) (post: RiscvMachineL -> Prop),
        Memory.loadWord initialL.(getMem) addr = Some v ->
        mcomp_sat (f v) initialL post ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post.
  Proof.

  Qed.

  Lemma go_storeWord: forall initialL addr v m' post (f: unit -> M unit),
        Memory.storeWord initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withMem m' initialL) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post.
  Proof.

  Qed.

  Lemma go_getPC: forall initialL f (post: RiscvMachineL -> Prop),
        mcomp_sat (f initialL.(getPc)) initialL post ->
        mcomp_sat (Bind getPC f) initialL post.
  Proof.

  Qed.

  Lemma go_setPC: forall initialL v post (f: unit -> M unit),
        mcomp_sat (f tt) (setNextPc initialL v) post ->
        mcomp_sat (Bind (setPC v) f) initialL post.
  Proof.

  Qed.

  Lemma go_step: forall initialL (post: RiscvMachineL -> Prop),
        mcomp_sat
          (Return tt)
          (setNextPc (setPc initialL
                            initialL.(getNextPc))
                     (add initialL.(getNextPc) (ZToReg 4)))
          post ->
        mcomp_sat step initialL post.
  Proof.

  Qed.


End Axiomatic.

Arguments AxiomaticRiscv {_} {_} Action {_} M {_} {_}.
