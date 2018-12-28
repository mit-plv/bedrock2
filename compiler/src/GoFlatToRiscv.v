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
Require Import coqutil.Tactics.Tactics.
Require Import compiler.containsProgram.
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

  Fixpoint ptsto_bytes(n: nat)(addr: word): HList.tuple byte n -> mem -> Prop :=
    match n with
    | O => fun _ => emp True
    | S n0 => fun bytes =>
                sep (ptsto addr (PrimitivePair.pair._1 bytes))
                    (ptsto_bytes n0 (word.add addr (word.of_Z 1)) (PrimitivePair.pair._2 bytes))
    end.

  Lemma impl1_sep_cancel_l: forall P Q1 Q2,
      impl1 Q1 Q2 -> impl1 (P * Q1)%type (P * Q2)%type.
  Proof.
    unfold impl1 in *.
    intros.
    unfold sep in *.
    destruct_products.
    eauto 10.
  Qed.

  Lemma impl1_sep_cancel_r: forall P Q1 Q2,
      impl1 Q1 Q2 -> impl1 (Q1 * P)%type (Q2 * P)%type.
  Proof.
    unfold impl1 in *.
    intros.
    unfold sep in *.
    destruct_products.
    eauto 10.
  Qed.

  Lemma ptsto_bytes_to_load: forall n m v addr R,
      (ptsto_bytes n addr v * R)%type m ->
      Memory.load n m addr = Some v.
  Proof.
    induction n; intros.
    - simpl in *. destruct v. reflexivity.
    - destruct v as [b v].
      simpl in *.
      specialize (IHn m v (word.add addr (word.of_Z 1)) (ptsto addr b * R)%type).
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
        | (?p * ?q)%type x => pose proof (sep_comm p q) as C
        end.
        apply C.
        apply H.
  Qed.

  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    ex1 (fun (w: w32) =>
           sep (ptsto_bytes 4 addr w)
               (emp (decode (RV_wXLEN_IM (B := BitWidth)) (LittleEndian.combine 4 w) = instr))).

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma go_fetch_inst: forall {inst initialL pc0} {R: mem -> Prop} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      (program pc0 [inst] * R) initialL.(getMem) ->
      mcomp_sat (Bind (execute inst) (fun _ => step)) initialL post ->
      mcomp_sat (run1 (B := BitWidth)) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold program, array, ptsto_instr in H0.
    (* TODO how can I destruct this existential? *)
    eapply go_loadWord.
    - eapply ptsto_bytes_to_load.
      (* TODO this is implied by H0 *)
      admit.
    - (* TODO this is implied by H1 and the equality "inst = ..." in H0 *)
      admit.
  Admitted.

End Go.
