Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import riscv.Utility.Utility.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.MkMachineWidth.

Local Open Scope Z_scope.

Set Implicit Arguments.


Section Rem4.
  Context {W: Words}.

  Ltac mword_cst w :=
    match w with
    | ZToReg ?x => let b := isZcst x in
                  match b with
                  | true => x
                  | _ => constr:(NotConstant)
                  end
    | _ => constr:(NotConstant)
  end.

  (*
  Hint Rewrite
    ZToReg_morphism.(morph_add)
    ZToReg_morphism.(morph_sub)
    ZToReg_morphism.(morph_mul)
    ZToReg_morphism.(morph_opp)
  : rew_ZToReg_morphism.

  Add Ring mword_ring : (@regRing mword MW)
      (preprocess [autorewrite with rew_ZToReg_morphism],
       morphism (@ZToReg_morphism mword MW),
       constants [mword_cst]).
   *)
  Add Ring wring: (@word.ring_theory width word word_ok).

  Ltac ring' := unfold ZToReg, mul, add, MachineWidth_XLEN in *; ring.

  (* put here so that rem picks up the MachineWidth for wXLEN *)

  (*
  Lemma four_divides_Npow2_wXLEN:
      exists k : N, (wordToN (natToWord wXLEN 4) * k)%N = Npow2 wXLEN.
  Proof.
    unfold wXLEN, bitwidth in *.
    destruct Bw.
    - exists (Npow2 30). reflexivity.
    - exists (Npow2 62). reflexivity.
  Qed.
   *)

  (* check lower two bits approach: how to connect to remu? or replace remu in spec? *)

  Axiom euclid_unsigned: forall (a b: word), a = add (mul (divu a b) b) (remu a b).
  Axiom remu_range: forall (a b: word), 0 <= regToZ_unsigned (remu a b) < regToZ_unsigned b.

  Axiom unique: forall a b q r,
      a = add (mul b q) r ->
      0 <= regToZ_unsigned r < regToZ_unsigned b ->
      q = divu a b /\ r = remu a b.

  Definition divisibleBy4(a: word): Prop := exists q, mul (ZToReg 4) q = a.

  Lemma remu40_divisibleBy4: forall (a: word),
      remu a (ZToReg 4) = ZToReg 0 ->
      divisibleBy4 a.
  Proof.
    intros.
    unfold divisibleBy4.
    exists (divu a (ZToReg 4)).
    pose proof (euclid_unsigned a (ZToReg 4)) as P.
    rewrite P at 2.
    rewrite H at 1.
    ring'.
  Qed.

  Lemma divisibleBy4_remu40: forall (a: word),
      divisibleBy4 a ->
      remu a (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    unfold divisibleBy4 in *.
    destruct H as [q H].
    destruct (@unique a (ZToReg 4) q (ZToReg 0)).
    - subst a. ring'.
    - (*pose proof pow2_sz_4.
      rewrite regToZ_ZToReg_unsigned by blia.
      rewrite regToZ_ZToReg_unsigned by blia.
      blia.
    - congruence.
  Qed.*) Admitted.

  Lemma remu_four_undo: forall a, remu (mul (ZToReg 4) a) (ZToReg 4) = ZToReg 0.
  Proof. Admitted. (*
    intros.
    rewrite remu_def.
    f_equal.
    pose proof pow2_sz_4.
    rewrite mul_def_unsigned.
    rewrite regToZ_ZToReg_unsigned_mod.
    rewrite (regToZ_ZToReg_unsigned 4) by blia.
    pose proof XLEN_lbound.
    apply Z.rem_mod_eq_0; [blia|].
    replace XLEN with (2 + (XLEN - 2)) by blia.
    rewrite Z.pow_add_r by blia.
    change (2 ^ 2) with 4.
    pose proof (pow2_pos (XLEN - 2)).
    div_mod_to_quot_rem. nia.
  Qed.*)

  Lemma remu_four_four: remu (ZToReg 4) (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    apply divisibleBy4_remu40. unfold divisibleBy4.
    exists (ZToReg 1). ring'.
  Qed.

  Lemma remu_four_zero_distrib_plus: forall a b,
      remu a (ZToReg 4) = ZToReg 0 ->
      remu b (ZToReg 4) = ZToReg 0 ->
      remu (add a b) (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    apply divisibleBy4_remu40.
    apply remu40_divisibleBy4 in H.  destruct H  as [q1 H1].
    apply remu40_divisibleBy4 in H0. destruct H0 as [q2 H2].
    unfold divisibleBy4 in *.
    subst.
    exists (add q1 q2).
    ring'.
  Qed.
End Rem4.
