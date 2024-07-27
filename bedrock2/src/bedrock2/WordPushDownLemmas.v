From Coq Require Import ZArith. Local Open Scope Z_scope.
From Coq Require Import Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Module word.
  Section WithWord.
    Context [width] [word : word.word width] [word_ok : word.ok word].

    (* Pushing down word.unsigned, using sideconditions to prevent overflow: *)

    Lemma unsigned_of_Z_modwrap: forall (z: Z),
        word.unsigned (word.of_Z (word := word) z) = z mod 2 ^ width.
    Proof. apply word.unsigned_of_Z. Qed.

    Lemma unsigned_opp_eq_nowrap: forall [a: word] [ua: Z],
        word.unsigned a = ua ->
        ua <> 0 ->
        word.unsigned (word.opp a) = 2 ^ width - ua.
    Proof. intros. subst. apply word.unsigned_opp_nowrap. assumption. Qed.
    (* and lemma word.unsigned_opp_0 can be used as-is *)

    Lemma unsigned_add_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        ua + ub < 2 ^ width ->
        word.unsigned (word.add a b) = ua + ub.
    Proof. intros. subst. apply word.unsigned_add_nowrap. assumption. Qed.

    Lemma unsigned_sub_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        0 <= ua - ub ->
        word.unsigned (word.sub a b) = ua - ub.
    Proof. intros. subst. apply word.unsigned_sub_nowrap. assumption. Qed.

    Lemma unsigned_mul_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        ua * ub < 2 ^ width ->
        word.unsigned (word.mul a b) = ua * ub.
    Proof. intros. subst. apply word.unsigned_mul_nowrap. assumption. Qed.

    Lemma unsigned_divu_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        ub <> 0 ->
        word.unsigned (word.divu a b) = ua / ub. (* note: division is not LIA *)
    Proof. intros. subst. apply word.unsigned_divu_nowrap. assumption. Qed.

    (* Pushing down word.unsigned, using modulos expressed as (dividend - k * divisor),
       with k being a division that can be treated opaquely *)

    Lemma unsigned_range_eq{z}{x: word}: word.unsigned x = z -> 0 <= z < 2 ^ width.
    Proof. intros. subst. eapply word.unsigned_range. Qed.

    (* The RHSs of the conclusions of the lemmas below are modulos expressed without
       using modulo.
       After using the equations, we have to eapply unsigned_range_eq in them to
       make sure we have the bounds of the modulo. *)

    Lemma unsigned_of_Z_eq_wrap_for_lia: forall (z z': Z),
        z = z' ->
        word.unsigned (word.of_Z (word := word) z) = z' - 2 ^ width * (z' / 2 ^ width).
    Proof.
      intros. subst z'.
      rewrite word.unsigned_of_Z. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_add_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.add a b) = ua + ub - 2 ^ width * ((ua + ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_add. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_sub_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.sub a b) = ua - ub - 2 ^ width * ((ua - ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_sub. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_mul_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.mul a b) = ua * ub - 2 ^ width * ((ua * ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_mul. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_slu_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        word.unsigned x = ux ->
        word.unsigned (word.slu x (word.of_Z a)) =
          ux * 2 ^ a - 2 ^ width * (ux / 2 ^ (width - a)).
    Proof.
      intros. subst. rewrite word.unsigned_slu_shamtZ by lia.
      unfold word.wrap. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.mod_eq by apply word.modulus_nonzero.
      replace (2 ^ width) with (2 ^ (width - a) * 2 ^ a) at 2.
      2: {
        rewrite <-Z.pow_add_r. 1: f_equal. all: lia.
      }
      rewrite Z.div_mul_cancel_r.
      1: reflexivity.
      all: apply Z.pow_nonzero; lia.
    Qed.

    Lemma unsigned_sru_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        word.unsigned x = ux ->
        word.unsigned (word.sru x (word.of_Z a)) = ux / 2 ^ a.
    Proof.
      intros. subst. rewrite word.unsigned_sru_shamtZ by lia.
      rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    Qed.

    Lemma unsigned_ltu_eq: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.ltu a b = Z.ltb ua ub.
    Proof. intros. subst. apply word.unsigned_ltu. Qed.

    Lemma unsigned_eqb_eq: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.eqb a b = Z.eqb ua ub.
    Proof. intros. subst. apply word.unsigned_eqb. Qed.

    Lemma unsigned_if_eq_for_lia: forall (c crhs: bool) (a b: word) (ua ub: Z),
        c = crhs ->
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        crhs = true /\ word.unsigned (if c then a else b) = ua \/
        crhs = false /\ word.unsigned (if c then a else b) = ub.
    Proof using. intros. subst. destruct crhs; intuition. Qed.

    Lemma unsigned_opp_eq_for_lia: forall [a: word] [ua: Z],
        word.unsigned a = ua ->
        (ua <> 0 /\ word.unsigned (word.opp a) = 2 ^ width - ua) \/
        (ua = 0 /\ word.unsigned (word.opp a) = 0).
    Proof.
      intros. assert (ua = 0 \/ ua <> 0) as C by lia. subst.
      destruct C as [C | C].
      - rewrite word.unsigned_opp_0 by assumption. lia.
      - erewrite unsigned_opp_eq_nowrap. 2: reflexivity. 2: exact C. lia.
    Qed.

    (* Pushing down word.of_Z: *)

    (* lemma word.of_Z_unsigned can be used as-is *)

    Lemma of_Z_mod: forall (z: Z),
        word.of_Z (word := word) (z mod 2 ^ width) = word.of_Z (word := word) z.
    Proof.
      intros. change (z mod 2 ^ width) with (word.wrap z).
      rewrite <- word.unsigned_of_Z. apply word.of_Z_unsigned.
    Qed.

    Lemma of_Z_mod_eq: forall [z: Z] [w: word],
        word.of_Z z = w ->
        word.of_Z (z mod 2 ^ width) = w.
    Proof. intros. subst. apply of_Z_mod. Qed.

    Lemma of_Z_opp_eq: forall [z: Z] [w: word],
        word.of_Z z = w ->
        word.of_Z (- z) = word.opp w.
    Proof. intros. subst. apply word.ring_morph_opp. Qed.

    Lemma of_Z_add_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 + z2) = word.add w1 w2.
    Proof. intros. subst. apply word.ring_morph_add. Qed.

    Lemma of_Z_sub_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 - z2) = word.sub w1 w2.
    Proof. intros. subst. apply word.ring_morph_sub. Qed.

    Lemma of_Z_mul_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 * z2) = word.mul w1 w2.
    Proof. intros. subst. apply word.ring_morph_mul. Qed.

    (* word.signed: don't push it down, but just express it in terms of word.unsigned *)

    Lemma signed_eq_unsigned_wrap_for_lia: forall (w: word) (uw: Z),
        word.unsigned w = uw ->
        word.signed w = uw - 2 ^ width * ((uw + 2 ^ (width - 1)) / 2 ^ width).
    Proof.
      intros. subst uw.
      rewrite word.signed_eq_swrap_unsigned. unfold word.swrap.
      etransitivity.
      - eapply Z.sub_cancel_r. eapply Z.mod_eq. eapply word.modulus_nonzero.
      - ring.
    Qed.

    Lemma signed_range_eq_for_lia{z}{x: word}:
      word.signed x = z ->
      - 2 ^ width <= 2 * z < 2 ^ width. (* <- avoid using 2^(width-1) *)
    Proof.
      intros. pose proof (word.signed_range x).
      replace (2 ^ width) with (2 * 2 ^ (width - 1)). 1: lia.
      replace width with (width - 1 + 1) at 2 by lia.
      pose proof word.width_pos.
      rewrite Z.pow_add_r; simpl (2 ^ 1); lia.
    Qed.
  End WithWord.
End word.
