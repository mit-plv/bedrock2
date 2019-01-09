Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.Run.
Require Import riscv.Execute.
Require Import riscv.proofs.DecodeEncode.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import compiler.util.Tactics.
Require Import compiler.SeparationLogic.


Local Unset Universe Polymorphism.

Section Go.

  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.
  Context {RVAX: AxiomaticRiscv Action M}.
  Context {BWS: FlatToRiscvBitWidthSpecifics word}.

  Add Ring wring: (@word.ring_theory width word word_ok).

  Ltac ring' := unfold ZToReg, mul, add, MkMachineWidth.MachineWidth_XLEN in *; ring.

  Lemma go_left_identity{A: Type}: forall initialL post a
         (f : A -> M unit),
      mcomp_sat (f a) initialL post ->
      mcomp_sat (Bind (Return a) f) initialL post.
  Proof.
    intros. rewrite left_identity. assumption.
  Qed.

  Lemma go_right_identity: forall initialL post
         (m: M unit),
      mcomp_sat m initialL post ->
      mcomp_sat (Bind m Return) initialL post.
  Proof.
    intros. rewrite right_identity. assumption.
  Qed.

  Lemma go_associativity{A B: Type}: forall initialL post
         (m: M A)
         (f : A -> M B) (g : B -> M unit),
      mcomp_sat (Bind m (fun x : A => Bind (f x) g)) initialL post ->
      mcomp_sat (Bind (Bind m f) g) initialL post.
  Proof.
    intros. rewrite associativity. assumption.
  Qed.

  Require Import coqutil.Datatypes.PrimitivePair.
  Require Import riscv.Encode.
  Require Import riscv.proofs.EncodeBound.

  Lemma combine_split: forall (n: nat) (z: Z),
      0 <= z < 2 ^ (Z.of_nat n * 8) ->
      LittleEndian.combine n (LittleEndian.split n z) = z.
  Proof.
    induction n; intros.
  Admitted.

  Definition ptsto_bytes(n: nat)(addr: word)(bs: HList.tuple byte n): mem -> Prop :=
    eq (unchecked_store_bytes n map.empty addr bs).

  Lemma impl1_sep_cancel_l: forall P Q1 Q2,
      impl1 Q1 Q2 -> impl1 (P * Q1) (P * Q2).
  Proof.
    unfold impl1 in *.
    intros.
    unfold sep in *.
    destruct_products.
    eauto 10.
  Qed.

  Lemma impl1_sep_cancel_r: forall P Q1 Q2,
      impl1 Q1 Q2 -> impl1 (Q1 * P) (Q2 * P).
  Proof.
    unfold impl1 in *.
    intros.
    unfold sep in *.
    destruct_products.
    eauto 10.
  Qed.

  Lemma impl1_trans: forall {P1 P2 P3: mem -> Prop},
      impl1 P1 P2 ->
      impl1 P2 P3 ->
      impl1 P1 P3.
  Proof.
    unfold impl1. eauto.
  Qed.

  Lemma iff1_trans: forall {P1 P2 P3: mem -> Prop},
      iff1 P1 P2 ->
      iff1 P2 P3 ->
      iff1 P1 P3.
  Proof.
    unfold iff1. intros. split; intros; edestruct H; edestruct H0; eauto.
  Qed.

  Lemma impl1_refl: forall {P: mem -> Prop},
      impl1 P P.
  Proof.
    unfold impl1. eauto.
  Qed.

  Lemma iff1_fst: forall {P1 P2: mem -> Prop},
      iff1 P1 P2 ->
      impl1 P1 P2.
  Proof.
    unfold iff1, impl1. intros. apply H. assumption.
  Qed.

  Lemma iff1_snd: forall {P1 P2: mem -> Prop},
      iff1 P1 P2 ->
      impl1 P2 P1.
  Proof.
    unfold iff1, impl1. intros. apply H. assumption.
  Qed.

  (* Note: there's only iff1_sep_cancel, which cancels on the left, but the default
     associativity says that (P * Q * R) is parsed as ((P * Q) * R), so canceling on
     the right by default would make more sense *)
  Lemma iff1_sep_cancel_r: forall {P1 P2 Q: mem -> Prop},
      iff1 P1 P2 ->
      iff1 (P1 * Q) (P2 * Q).
  Proof.
    intros.
    refine (iff1_trans _ (sep_comm _ _)).
    refine (iff1_trans (sep_comm _ _) _).
    apply iff1_sep_cancel.
    assumption.
  Qed.

  Lemma ptsto_bytes_to_load_bytes: forall n m v addr R,
      (ptsto_bytes n addr v * R)%sep m ->
      Memory.load_bytes n m addr = Some v.
  Proof.
    cbv [ptsto_bytes sep load_bytes unchecked_store_bytes].
    intros.
    destruct_products.
    (* TODO *)
  Admitted.

  Lemma load_bytes_to_ptsto_bytes: forall n m v addr,
      Memory.load_bytes n m addr = Some v ->
      exists R, (ptsto_bytes n addr v * R)%sep m.
  Proof.
    cbv [ptsto_bytes sep load_bytes unchecked_store_bytes].
    intros.
    (* TODO *)
  Admitted.

  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    ptsto_bytes 4 addr (LittleEndian.split 4 (encode instr)).

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma go_fetch_inst: forall {inst initialL pc0} {R: mem -> Prop} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      (program pc0 [inst] * R)%sep initialL.(getMem) ->
      verify inst (@RV_wXLEN_IM (@BitWidth _ _ _ BWS)) ->
      mcomp_sat (Bind (execute inst) (fun _ => step)) initialL post ->
      mcomp_sat (run1 (B := BitWidth)) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold program, array, ptsto_instr in *.

    eapply go_loadWord; [eapply ptsto_bytes_to_load_bytes; seplog|].
    rewrite combine_split, decode_encode; auto using encode_range.
  Qed.

End Go.
