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

  Fixpoint ptsto_bytes(n: nat)(addr: word): HList.tuple byte n -> mem -> Prop :=
    match n with
    | O => fun _ => emp True
    | S n0 => fun bytes =>
                sep (ptsto addr (pair._1 bytes))
                    (ptsto_bytes n0 (word.add addr (word.of_Z 1)) (pair._2 bytes))
    end.

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

  Lemma ptsto_bytes_to_load: forall n m v addr R,
      (ptsto_bytes n addr v * R)%sep m ->
      Memory.load n m addr = Some v.
  Proof.
    induction n; intros.
    - simpl in *. destruct v. reflexivity.
    - destruct v as [b v].
      simpl in *.
      specialize (IHn m v (word.add addr (word.of_Z 1)) (ptsto addr b * R)%sep).
      rewrite IHn.
      + erewrite get_sep; [reflexivity|].
        apply sep_assoc in H.
        exact H.
      + apply sep_assoc.
        (* TODO should "ecancel" do this step as well? *)
        revert H. clear -mem_ok. revert m.
        match goal with
        | |- forall m, ?P m -> ?Q m => change (impl1 P Q)
        end.
        (* TODO why does "ecancel" not solve this? *)
        (* manually: *)
        apply impl1_sep_cancel_r.
        intros x H.
        match type of H with
        | (?p * ?q)%sep x => pose proof (sep_comm p q) as C
        end.
        apply C.
        apply H.
  Qed.

  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    ptsto_bytes 4 addr (LittleEndian.split 4 (encode instr)).

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Ltac sep :=
    let m := lazymatch goal with |- _ ?m => m end in
    let H := multimatch goal with H: _ m |- _ => H end  in
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
    repeat rewrite !sep_assoc; (* TODO: maybe this should be a part of reify_goal *)
    SeparationLogic.ecancel; fail.

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

    eapply go_loadWord; [eapply ptsto_bytes_to_load; sep|].
    rewrite combine_split, decode_encode; auto using encode_range.
  Qed.

End Go.
