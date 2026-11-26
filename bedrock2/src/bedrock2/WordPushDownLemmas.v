Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Z.ZLib.
Require Import coqutil.Z.Lia.

(* Folds a modulus evaluated to [Z.pow_pos 2 p] or to a literal back to [2 ^ k]. *)
Ltac pow2_form m :=
  lazymatch m with
  | 2 ^ _ => fail
  | Z.pow_pos 2 ?p => constr:(2 ^ Z.pos p)
  | _ => lazymatch isZcst m with
         | true => let k := eval vm_compute in (Z.log2 m) in
                   lazymatch eval vm_compute in (Z.eqb (2 ^ k) m) with
                   | true => constr:(2 ^ k)
                   end
         end
  end.

Ltac fold_pow2_moduli :=
  repeat match goal with
         | H: context[Zmod ?m] |- _ => let p := pow2_form m in change m with p in H
         | H: context[@Zmod.unsigned ?m _] |- _ => let p := pow2_form m in change m with p in H
         | H: context[@Zmod.signed ?m _] |- _ => let p := pow2_form m in change m with p in H
         | H: context[@Zmod.of_Z ?m _] |- _ => let p := pow2_form m in change m with p in H
         | |- context[Zmod ?m] => let p := pow2_form m in change m with p
         | |- context[@Zmod.unsigned ?m _] => let p := pow2_form m in change m with p
         | |- context[@Zmod.signed ?m _] => let p := pow2_form m in change m with p
         | |- context[@Zmod.of_Z ?m _] => let p := pow2_form m in change m with p
         end.

(* A constant shift amount below the width is unchanged by the masking that
   [Semantics.interp_binop] applies to shift amounts. *)
Lemma unsigned_of_Z_shamt{w: Z}(a: Z)
  (H: andb (Z.leb 0 a) (Z.ltb a w) = true)(Hw: 2 ^ Z.log2 w = w):
  Zmod.unsigned (bits.of_Z w a) mod 2 ^ Z.log2 w = a.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (Z.pow_gt_lin_r 2 w ltac:(lia) ltac:(lia)).
  rewrite bits.unsigned_of_Z_small, Hw by lia.
  apply Z.mod_small. lia.
Qed.

(* ZnWords reduces bitwise word operations to Z operations under [mod 2 ^ w] so
   that [Z.div_mod_to_equations] gives lia the range of the result; the
   mod-free [bits.unsigned_or]/[bits.unsigned_xor] would leave [Z.lor]/[Z.lxor]
   as unbounded atoms. *)
Lemma unsigned_or_modwrap [m] (x y : Zmod m) :
  Zmod.unsigned (Zmod.or x y) = Z.lor (Zmod.unsigned x) (Zmod.unsigned y) mod m.
Proof. apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_xor_modwrap [m] (x y : Zmod m) :
  Zmod.unsigned (Zmod.xor x y) = Z.lxor (Zmod.unsigned x) (Zmod.unsigned y) mod m.
Proof. apply Zmod.unsigned_of_Z. Qed.

Module word.
  Section WithWord.
    Context [width] [BW: Bitwidth width].
    Local Set Default Proof Using "All".
    Local Notation word := (bits width).

    (* Pushing down Zmod.unsigned, using sideconditions to prevent overflow: *)

    Lemma unsigned_of_Z_modwrap: forall (z: Z),
        Zmod.unsigned (bits.of_Z width z) = z mod 2 ^ width.
    Proof. apply bits.unsigned_of_Z. Qed.

    Lemma unsigned_opp_eq_nowrap: forall [a: word] [ua: Z],
        Zmod.unsigned a = ua ->
        ua <> 0 ->
        Zmod.unsigned (Zmod.opp a) = 2 ^ width - ua.
    Proof. intros. subst. apply word.unsigned_opp_nowrap; auto using width_pos. Qed.
    (* and lemma word.unsigned_opp_0 can be used as-is *)

    Lemma unsigned_add_eq_nowrap: forall [a b: word] [ua ub: Z],
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        ua + ub < 2 ^ width ->
        Zmod.unsigned (Zmod.add a b) = ua + ub.
    Proof. intros. subst. apply word.unsigned_add_nowrap; auto using width_pos. Qed.

    Lemma unsigned_sub_eq_nowrap: forall [a b: word] [ua ub: Z],
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        0 <= ua - ub ->
        Zmod.unsigned (Zmod.sub a b) = ua - ub.
    Proof. intros. subst. apply word.unsigned_sub_nowrap; auto using width_pos. Qed.

    Lemma unsigned_mul_eq_nowrap: forall [a b: word] [ua ub: Z],
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        ua * ub < 2 ^ width ->
        Zmod.unsigned (Zmod.mul a b) = ua * ub.
    Proof. intros. subst. apply word.unsigned_mul_nowrap; auto using width_pos. Qed.

    Lemma unsigned_divu_eq_nowrap: forall [a b: word] [ua ub: Z],
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        ub <> 0 ->
        Zmod.unsigned (Zmod.udiv a b) = ua / ub. (* note: division is not LIA *)
    Proof.
      intros. subst. apply Zmod.unsigned_udiv_nonneg. 2: assumption.
      pose proof modulus_pos. lia.
    Qed.

    (* Pushing down Zmod.unsigned, using modulos expressed as (dividend - k * divisor),
       with k being a division that can be treated opaquely *)

    Lemma unsigned_range_eq{z}{x: word}: Zmod.unsigned x = z -> 0 <= z < 2 ^ width.
    Proof. intros. subst. eapply bits.unsigned_range, width_nonneg. Qed.

    (* The RHSs of the conclusions of the lemmas below are modulos expressed without
       using modulo.
       After using the equations, we have to eapply unsigned_range_eq in them to
       make sure we have the bounds of the modulo. *)

    Lemma unsigned_of_Z_eq_wrap_for_lia: forall (z z': Z),
        z = z' ->
        Zmod.unsigned (bits.of_Z width z) = z' - 2 ^ width * (z' / 2 ^ width).
    Proof.
      intros. subst z'. rewrite bits.unsigned_of_Z.
      eapply Z.mod_eq. pose proof modulus_pos. lia.
    Qed.

    Lemma unsigned_add_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        Zmod.unsigned (Zmod.add a b) = ua + ub - 2 ^ width * ((ua + ub) / 2 ^ width).
    Proof.
      intros. subst. rewrite Zmod.unsigned_add.
      eapply Z.mod_eq. pose proof modulus_pos. lia.
    Qed.

    Lemma unsigned_sub_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        Zmod.unsigned (Zmod.sub a b) = ua - ub - 2 ^ width * ((ua - ub) / 2 ^ width).
    Proof.
      intros. subst. rewrite Zmod.unsigned_sub.
      eapply Z.mod_eq. pose proof modulus_pos. lia.
    Qed.

    Lemma unsigned_mul_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        Zmod.unsigned (Zmod.mul a b) = ua * ub - 2 ^ width * ((ua * ub) / 2 ^ width).
    Proof.
      intros. subst. rewrite Zmod.unsigned_mul.
      eapply Z.mod_eq. pose proof modulus_pos. lia.
    Qed.

    (* The shift amount n is the constant a, possibly masked by Semantics.interp_binop. *)
    (* wa is (width - a), passed separately so that the caller can pre-compute it
       when width is concrete: lia treats 2 ^ (32 - 3) as an opaque atom, but
       understands 2 ^ 29. *)
    Lemma unsigned_slu_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a n wa: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        n = a ->
        width - a = wa ->
        Zmod.unsigned x = ux ->
        Zmod.unsigned (Zmod.slu x n) =
          ux * 2 ^ a - 2 ^ width * (ux / 2 ^ wa).
    Proof.
      intros. subst. rewrite Zmod.unsigned_slu.
      rewrite Z.shiftl_mul_pow2 by lia.
      pose proof modulus_pos.
      rewrite Z.mod_eq by lia.
      rewrite <- (Z.div_mul_cancel_r _ (2 ^ (width - a)) (2 ^ a)) by (apply Z.pow_nonzero; lia).
      rewrite <- Z.pow_add_r by lia.
      replace (width - a + a) with width by lia.
      reflexivity.
    Qed.

    Lemma unsigned_sru_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a n: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        n = a ->
        Zmod.unsigned x = ux ->
        Zmod.unsigned (Zmod.sru x n) = ux / 2 ^ a.
    Proof.
      intros. subst. rewrite Zmod.unsigned_sru by lia.
      rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    Qed.

    Lemma unsigned_eqb_eq: forall (a b: word) (ua ub: Z),
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        Zmod.eqb a b = Z.eqb ua ub.
    Proof. intros. subst. reflexivity. Qed.

    Lemma unsigned_if_eq_for_lia: forall (c crhs: bool) (a b: word) (ua ub: Z),
        c = crhs ->
        Zmod.unsigned a = ua ->
        Zmod.unsigned b = ub ->
        crhs = true /\ Zmod.unsigned (if c then a else b) = ua \/
        crhs = false /\ Zmod.unsigned (if c then a else b) = ub.
    Proof using. intros. subst. destruct crhs; intuition. Qed.

    Lemma unsigned_opp_eq_for_lia: forall [a: word] [ua: Z],
        Zmod.unsigned a = ua ->
        (ua <> 0 /\ Zmod.unsigned (Zmod.opp a) = 2 ^ width - ua) \/
        (ua = 0 /\ Zmod.unsigned (Zmod.opp a) = 0).
    Proof.
      intros. assert (ua = 0 \/ ua <> 0) as C by lia. subst.
      destruct C as [C | C].
      - rewrite word.unsigned_opp_0 by assumption. lia.
      - erewrite unsigned_opp_eq_nowrap. 2: reflexivity. 2: exact C. lia.
    Qed.

    (* Pushing down bits.of_Z: *)

    (* lemmas Zmod.of_Z_unsigned and bits.of_Z_mod can be used as-is *)

    Lemma of_Z_mod_eq: forall [z: Z] [w: word],
        bits.of_Z width z = w ->
        bits.of_Z width (z mod 2 ^ width) = w.
    Proof. intros. subst. apply bits.of_Z_mod. Qed.

    Lemma of_Z_opp_eq: forall [z: Z] [w: word],
        bits.of_Z width z = w ->
        bits.of_Z width (- z) = Zmod.opp w.
    Proof. intros. subst. apply Zmod.of_Z_opp. Qed.

    Lemma of_Z_add_eq: forall [z1 z2: Z] [w1 w2: word],
        bits.of_Z width z1 = w1 ->
        bits.of_Z width z2 = w2 ->
        bits.of_Z width (z1 + z2) = Zmod.add w1 w2.
    Proof. intros. subst. apply Zmod.of_Z_add. Qed.

    Lemma of_Z_sub_eq: forall [z1 z2: Z] [w1 w2: word],
        bits.of_Z width z1 = w1 ->
        bits.of_Z width z2 = w2 ->
        bits.of_Z width (z1 - z2) = Zmod.sub w1 w2.
    Proof. intros. subst. apply Zmod.of_Z_sub. Qed.

    Lemma of_Z_mul_eq: forall [z1 z2: Z] [w1 w2: word],
        bits.of_Z width z1 = w1 ->
        bits.of_Z width z2 = w2 ->
        bits.of_Z width (z1 * z2) = Zmod.mul w1 w2.
    Proof. intros. subst. apply Zmod.of_Z_mul. Qed.

    (* Zmod.signed: don't push it down, but just express it in terms of Zmod.unsigned *)

    Lemma signed_eq_unsigned_wrap_for_lia: forall (w: word) (uw: Z),
        Zmod.unsigned w = uw ->
        Zmod.signed w = uw - 2 ^ width * ((uw + 2 ^ (width - 1)) / 2 ^ width).
    Proof.
      intros. subst uw.
      rewrite <- Zmod.smod_unsigned, Z.smodulo_pow2.
      pose proof modulus_pos.
      etransitivity.
      - eapply Z.sub_cancel_r. eapply Z.mod_eq. lia.
      - ring.
    Qed.

    Lemma signed_range_eq_for_lia{z}{x: word}:
      Zmod.signed x = z ->
      - 2 ^ width <= 2 * z < 2 ^ width. (* <- avoid using 2^(width-1) *)
    Proof. intros. subst. apply bits.signed_range, width_nonneg. Qed.
  End WithWord.
End word.
