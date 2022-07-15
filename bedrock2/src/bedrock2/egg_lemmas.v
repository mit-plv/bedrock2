Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import egg.Loader.
Require Import Coq.Logic.PropExtensionality.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.

Local Open Scope Z_scope.


Lemma neq_sym{A: Type}: forall (x y: A), x <> y -> y <> x. Proof. congruence. Qed.

Lemma eq_eq_sym: forall {A: Type} (x y: A), (x = y) = (y = x).
Proof.
  intros. apply propositional_extensionality. split; intros; congruence.
Qed.

Lemma eq_same_True: forall (A: Type) (a: A), (a = a) = True.
Proof. intros. apply propositional_extensionality; split; intros; auto. Qed.

Lemma and_True_l: forall P, and True P = P.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

Lemma and_True_r: forall P, and P True = P.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

Lemma or_True_l: forall P, or True P = True.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

Lemma or_True_r: forall P, or P True = True.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

(* stated in a convoluted way because each quantified variable must appear in conclusion *)
Lemma and_proj_l: forall P Q, and P Q -> and P Q = P.
Proof. intros. apply propositional_extensionality. intuition idtac. Qed.

Lemma and_proj_r: forall P Q, and P Q -> and P Q = Q.
Proof. intros. apply propositional_extensionality. intuition idtac. Qed.

Inductive worth_considering_status: Set := is_worth_considering.

Definition consider{T: Type}(x: T) := is_worth_considering.


Module word.
  Section WithWord.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Local Hint Mode word.word - : typeclass_instances.

    Add Ring wring: (@word.ring_theory width word word_ok).

    Lemma add_0_l: forall x, word.add (word.of_Z 0) x = x.
    Proof. intros. ring. Qed.
    Lemma add_0_r: forall x, word.add x (word.of_Z 0) = x.
    Proof. intros. ring. Qed.
    Lemma mul_0_l: forall x, word.mul (word.of_Z 0) x = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma mul_0_r: forall x, word.mul x (word.of_Z 0) = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma mul_1_l: forall x, word.mul (word.of_Z 1) x = x.
    Proof. intros. ring. Qed.
    Lemma mul_1_r: forall x, word.mul x (word.of_Z 1) = x.
    Proof. intros. ring. Qed.

    Lemma add_comm: forall a b, word.add a b = word.add b a.
    Proof. intros. ring. Qed.
    Lemma add_rot: forall a m b, word.add (word.add a m) b = word.add (word.add b a) m.
    Proof. intros. ring. Qed.
    Lemma add_join: forall a m b, word.add (word.add a m) b = word.add m (word.add a b).
    Proof. intros. ring. Qed.
    Lemma add_to_left_assoc: forall a b c,
        word.add a (word.add b c) = word.add (word.add a b) c.
    Proof. intros. ring. Qed.
    Lemma add_to_right_assoc: forall a b c,
        word.add (word.add a b) c = word.add a (word.add b c).
    Proof. intros. ring. Qed.
    Lemma add_opp: forall a, word.add a (word.opp a) = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma add_opp_l_distant: forall a m, word.add (word.opp a) (word.add m a) = m.
    Proof. intros. ring. Qed.
    Lemma add_opp_r_distant: forall a m, word.add a (word.add m (word.opp a)) = m.
    Proof. intros. ring. Qed.
    Lemma sub_def: forall a b, word.sub a b = word.add a (word.opp b).
    Proof. intros. ring. Qed.

    Lemma unsigned_slu_to_mul_pow2: forall (x: word) a,
        0 <= a < width ->
        word.unsigned (word.slu x (word.of_Z a)) = (word.unsigned x * 2 ^ a) mod 2 ^ width.
    Proof.
      intros. rewrite word.unsigned_slu_shamtZ by assumption. unfold word.wrap.
      rewrite Z.shiftl_mul_pow2. 2: apply H. reflexivity.
    Qed.

    Lemma unsigned_sru_to_div_pow2: forall (x: word) a,
        0 <= a < width ->
        word.unsigned (word.sru x (word.of_Z a)) = word.unsigned x / 2 ^ a.
    Proof.
      intros. rewrite word.unsigned_sru_shamtZ by assumption.
      rewrite Z.shiftr_div_pow2. 2: apply H. reflexivity.
    Qed.

    Lemma unsigned_nonneg: forall x: word, 0 <= word.unsigned x.
    Proof. intros. apply word.unsigned_range. Qed.

    Lemma unsigned_upper: forall x: word, word.unsigned x < 2 ^ width.
    Proof. intros. apply word.unsigned_range. Qed.
  End WithWord.
End word.

Module Z.
  Lemma div_mul_lt: forall x d1 d2,
      0 < x ->
      0 < d1 ->
      d1 < d2 ->
      x / d2 * d1 < x.
  Proof. intros. Z.to_euclidean_division_equations. Lia.nia. Qed.

  Lemma lt_from_le_and_neq: forall x y,
      x <= y -> x <> y -> x < y.
  Proof. intros. Lia.lia. Qed.

  Lemma mul_nonneg : forall e1 e2 : Z, 0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2.
  Proof. intros. Lia.nia. Qed.

  Lemma div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a / b.
  Proof. intros. apply Z.div_pos; assumption. Qed.

  Lemma forget_mod_in_lt_l : forall a b m : Z,
      0 <= a ->
      0 < m ->
      a < b ->
      a mod m < b.
  Proof.
    intros. eapply Z.le_lt_trans. 1: eapply Z.mod_le. all: assumption.
  Qed.

  Lemma remove_inner_mod: forall n m a : Z,
      0 < n ->
      0 < m ->
      (n | m) ->
      (a mod m) mod n = a mod n.
  Proof. intros. symmetry. apply Znumtheory.Zmod_div_mod; assumption. Qed.

  Lemma euclidean_decomp: forall a b, a = a / b * b + a mod b.
  Proof.
    intros.
    etransitivity. 1: eapply (Z_div_mod_eq_full a b). f_equal.
    apply Z.mul_comm.
  Qed.

  Lemma add_rot: forall a m b, Z.add (Z.add a m) b = Z.add (Z.add b a) m.
  Proof. intros. ring. Qed.
  Lemma add_join: forall a m b, Z.add (Z.add a m) b = Z.add m (Z.add a b).
  Proof. intros. ring. Qed.

  Lemma add_opp_l_distant: forall a m, Z.add (Z.opp a) (Z.add m a) = m.
  Proof. intros. ring. Qed.
  Lemma add_opp_r_distant: forall a m, Z.add a (Z.add m (Z.opp a)) = m.
  Proof. intros. ring. Qed.

  Lemma factor_add_mul_11: forall a, a + a = a * 2.
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_1q: forall a q, a + a * q = a * (1 + q).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_q1: forall a q, a * q + a = a * (q + 1).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_qq: forall a p q, a * p + a * q = a * (p + q).
  Proof. intros. Lia.lia. Qed.

  (* Lemma factor_sub_mul_11: forall a, a - a = a * 2. already Z.sub_diag *)
  Lemma factor_sub_mul_1q: forall a q, a - a * q = a * (1 - q).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_sub_mul_q1: forall a q, a * q - a = a * (q - 1).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_sub_mul_qq: forall a p q, a * p - a * q = a * (p - q).
  Proof. intros. Lia.lia. Qed.

  Lemma not_lt: forall a b, ~ a < b -> b <= a.
  Proof. intros. Lia.lia. Qed.

  Lemma not_le: forall a b, ~ a <= b -> b < a.
  Proof. intros. Lia.lia. Qed.

End Z.

Lemma Z_cancel_mul_ll: forall f a b,
    f <> 0 ->
    (f * a = f * b) = (a = b).
Proof.
  intros. apply propositional_extensionality. split; intros; Lia.nia.
Qed.

Lemma Z_add_add_mod_idemp: forall a b c n : Z,
    (a + b mod n + c) mod n = (a + b + c) mod n.
Proof.
  intros. rewrite (Z.add_comm a (b mod n)).
  rewrite <- Z.add_assoc. rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.

Lemma Z_add_sub_mod_idemp: forall a b c n : Z,
    (a + b mod n - c) mod n = (a + b - c) mod n.
Proof.
  intros. replace (a + b mod n - c) with (a - c + b mod n) by ring.
  rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma Z_sub_add_mod_idemp: forall a b c n : Z,
    (a - b mod n + c) mod n = (a - b + c) mod n.
Proof.
  intros. replace (a - b mod n + c) with (a + c - b mod n) by ring.
  rewrite Zminus_mod_idemp_r. f_equal. ring.
Qed.

Lemma Z_sub_sub_mod_idemp: forall a b c n : Z,
             (a - b mod n - c) mod n = (a - b - c) mod n.
Proof.
  intros. replace (a - b mod n - c) with (a - c - b mod n) by ring.
  rewrite Zminus_mod_idemp_r. f_equal. ring.
Qed.

Lemma Z_plus_mod_idemp_r_bw : forall a b n,
    trigger! ((b mod n)) ((a + b) mod n = (a + b mod n) mod n).
Proof. symmetry; apply Zplus_mod_idemp_r. Qed.

Lemma Z_plus_mod_idemp_l_bw : forall a b n,
    trigger! ((a mod n)) ((a + b) mod n = (a mod n + b) mod n).
Proof. symmetry; apply Zplus_mod_idemp_l. Qed.

Lemma Z_minus_mod_idemp_r_bw : forall a b n,
    trigger! ((b mod n)) ((a - b) mod n = (a - b mod n) mod n).
Proof. symmetry; apply Zminus_mod_idemp_r. Qed.

Lemma Z_minus_mod_idemp_l_bw : forall a b n,
    trigger! ((a mod n)) ((a - b) mod n = (a mod n - b) mod n).
Proof. symmetry; apply Zminus_mod_idemp_l. Qed.

(* less important, and some are expensive:

  assert (z_div_lt_to_mul: forall a b d, 0 < d -> (a / d < b) = (a < b * d)). {
    clear. intros. apply propositional_extensionality.
    Z.to_euclidean_division_equations.
    split; intros; Lia.nia.
  }
  assert (z_forget_mul_in_lt: forall a b f,
    trigger! ((a < f * b)) (0 < f -> 0 < b -> a < b -> a < f * b)). {
    clear. unfold with_trigger. intros. eapply Z.lt_le_trans. 1: eassumption.
    replace b with (1 * b) at 1 by Lia.lia.
    pose proof Z.mul_le_mono_pos_r as P. specialize P with (1 := H0).
    specialize (P 1 f). eapply P. Lia.lia.
  }

  assert (forall a b: Z, trigger! ((a mod b)) (a = (a / b) * b + a mod b)) as
    z_euclidean_decomp_mod_trigger by apply Z.euclidean_decomp.
  assert (forall a b: Z, trigger! ((a / b)) (a = (a / b) * b + a mod b)) as
    z_euclidean_decomp_div_trigger by apply Z.euclidean_decomp.

  assert (z_mod_lower: forall a b,
             trigger! ((a mod b)) (0 < b -> 0 <= a mod b)). {
    unfold with_trigger. eapply Z.mod_pos_bound.
  }
  assert (z_mod_upper: forall a b,
             trigger! ((a mod b)) (0 < b -> a mod b < b)). {
    unfold with_trigger. eapply Z.mod_pos_bound.
  }

  assert (z_neq_mul: forall n m, (n * m <> 0) = (n <> 0 /\ m <> 0)). {
    intros. symmetry. apply propositional_extensionality. eapply Z.neq_mul_0.
  }
  assert (z_mod_neq_0: forall n m, n mod m <> 0 -> n <> 0). {
    clear. intros. intro C. subst. apply H. apply Zmod_0_l.
  }
  assert (z_unfold_times_2: forall x, x * 2 = x + x). {
    clear. intros. Lia.lia.
  }
  (* not really helpful because where it looked useful, the (d * x) that was created
     contained a division in x, but that doesn't simplify away with the (d *...)
  assert (z_bounds_div: forall x b d,
             0 < d ->
             (d | b) ->
             (0 <= x < b / d) = (0 <= d * x < b)). {
    clear. intros.
    pose proof (Z.mul_lt_mono_pos_r d x (b / d) H) as P.
    apply propositional_extensionality. split; intros [? ?]; split; try Lia.lia.
    - eapply proj1 in P. specialize (P H2).
      rewrite Z.mul_comm. eapply Z.lt_le_trans. 1: exact P.
      apply Z.div_mul_undo_le. assumption.
    - unfold Z.divide in H0. destruct H0 as [z H0]. subst b.
      eapply proj2 in P. eapply P.
      rewrite Z.mul_comm. rewrite Z.div_mul by Lia.lia. assumption.
  }
  *)

  assert (z_mul_lt_to_lt_div: forall x b d,
             0 < d ->
             (d | b) ->
             (d * x < b) = (x < b / d)). {
    clear. intros.
    pose proof (Z.mul_lt_mono_pos_r d x (b / d) H) as P.
    apply propositional_extensionality. split; intros.
    - unfold Z.divide in H0. destruct H0 as [z H0]. subst b.
      eapply proj2 in P. eapply P.
      rewrite Z.mul_comm. rewrite Z.div_mul by Lia.lia. assumption.
    - eapply proj1 in P. specialize (P H1).
      rewrite Z.mul_comm. eapply Z.lt_le_trans. 1: exact P.
      apply Z.div_mul_undo_le. assumption.
  }

assert (z_div_upper_bound: forall x b d,
           trigger! ((x / d)) (0 < d -> x < b -> x / d < b / d + 1)). {
  clear. unfold with_trigger. intros. Z.to_euclidean_division_equations. Lia.nia.
}

*)

Ltac pose_word_lemmas width word :=
  pose proof word.add_0_l as wadd_0_l;
  pose proof word.add_0_r as wadd_0_r;
  pose proof (word.add_join: forall a m b,
       trigger! ((word.add a b)) (word.add (word.add a m) b = word.add m (word.add a b)))
       as wadd_join;
  pose proof (word.add_rot: forall a m b,
       trigger! ((word.add b a)) (word.add (word.add a m) b = word.add (word.add b a) m))
       as wadd_rot;
  pose proof word.add_to_left_assoc as wadd_to_left_assoc;
  pose proof word.add_to_right_assoc as wadd_to_right_assoc;
  pose proof word.add_opp as wadd_opp;
  pose proof word.add_opp_l_distant as wadd_opp_l_distant;
  pose proof word.add_opp_r_distant as wadd_opp_r_distant;
  pose proof word.sub_def as wsub_def;
  pose proof word.unsigned_of_Z_nowrap as wunsigned_of_Z_nowrap;
  pose proof (word.unsigned_nonneg: forall x: word,
                 trigger! ((word.unsigned x)) (0 <= word.unsigned x))
    as wunsigned_nonneg;
  pose proof (word.unsigned_upper: forall x : word,
                 trigger! ((word.unsigned x)) (word.unsigned x < 2 ^ width))
    as wunsigned_upper;
  pose proof word.unsigned_sru_to_div_pow2 as wunsigned_sru_to_div_pow2;
  pose proof word.unsigned_slu_to_mul_pow2 as wunsigned_slu_to_mul_pow2;
  pose proof word.unsigned_sub as wunsigned_sub; unfold word.wrap in wunsigned_sub;
  pose proof word.unsigned_add as wunsigned_add; unfold word.wrap in wunsigned_add.

Ltac pose_basic_Z_lemmas :=
  pose proof Z.not_lt as z_not_lt;
  pose proof Z.not_le as Z_not_le.

Ltac pose_Z_lemmas :=
  pose proof Z.forget_mod_in_lt_l as Z_forget_mod_in_lt_l;
  pose proof (Z.mul_nonneg: forall e1 e2 : Z,
                 trigger! ((e1 * e2)) (0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2))
    as z_mul_nonneg;
  pose proof (Z.div_nonneg: forall a b : Z,
                 trigger! ((a / b)) (0 <= a -> 0 < b -> 0 <= a / b))
    as z_div_nonneg;
  pose proof Z.div_mul_lt as z_div_mul_lt;
  pose proof Z.lt_from_le_and_neq as z_lt_from_le_and_neq;
  pose proof Z.remove_inner_mod as z_remove_inner_mod;
  pose proof Z_mod_mult as z_mod_mult;
  pose proof Zplus_mod_idemp_r as z_plus_mod_idemp_r;
  pose proof Zplus_mod_idemp_l as z_plus_mod_idemp_l;
  pose proof Zminus_mod_idemp_r as z_minus_mod_idemp_r;
  pose proof Zminus_mod_idemp_l as z_minus_mod_idemp_l;
  pose proof Z_add_add_mod_idemp as z_add_add_mod_idemp;
  pose proof Z_add_sub_mod_idemp as z_add_sub_mod_idemp;
  pose proof Z_sub_add_mod_idemp as z_sub_add_mod_idemp;
  pose proof Z_sub_sub_mod_idemp as z_sub_sub_mod_idemp;
  pose proof Z_plus_mod_idemp_r_bw as z_plus_mod_idemp_r_bw;
  pose proof Z_plus_mod_idemp_l_bw as z_plus_mod_idemp_l_bw;
  pose proof Z_minus_mod_idemp_r_bw as z_minus_mod_idemp_r_bw;
  pose proof Z_minus_mod_idemp_l_bw as z_minus_mod_idemp_l_bw;
  pose proof Z.add_0_l as z_add_0_l;
  pose proof (Z.add_join: forall a m b,
       trigger! ((Z.add a b)) (Z.add (Z.add a m) b = Z.add m (Z.add a b))) as z_add_join;
  pose proof (Z.add_rot: forall a m b,
       trigger! ((Z.add b a)) (Z.add (Z.add a m) b = Z.add (Z.add b a) m))
       as z_add_rot;
  pose proof Z.add_assoc as z_add_to_left_assoc;
  pose proof Z.add_assoc as z_add_to_right_assoc; symmetry in z_add_to_right_assoc;
  pose proof Z.add_opp_diag_r as z_add_opp;
  pose proof Z.add_opp_r as z_sub_def; symmetry in z_sub_def;
  pose proof Z.add_opp_l_distant as z_add_opp_l_distant;
  pose proof Z.add_opp_r_distant as z_add_opp_r_distant;
  (* shortcuts to not depend on sub_def, which requires too high ffn: *)
  pose proof Z.sub_add_distr as z_sub_add_to_left_assoc;
  pose proof Z.sub_add_distr as z_sub_sub_to_right_assoc;
    symmetry in z_sub_sub_to_right_assoc;
  pose proof Z.sub_sub_distr as z_sub_sub_to_left_assoc;
  pose proof Z.sub_sub_distr as z_sub_add_to_right_assoc;
    symmetry in z_sub_add_to_right_assoc;
  pose proof Z.add_sub_assoc as z_add_sub_to_left_assoc;
  pose proof Z.add_sub_assoc as z_add_sub_to_right_assoc;
    symmetry in z_add_sub_to_right_assoc;
  pose proof Z.mul_0_l as z_mul_0_l;
  pose proof Z.mul_comm as z_mul_comm;
  pose proof Z.mul_assoc as z_mul_to_left_assoc;
  pose proof Z.mul_assoc as z_mul_to_right_assoc; symmetry in z_mul_to_right_assoc;
  pose proof Z.mul_add_distr_l as z_mul_add_distr_l;
  pose proof Z.mul_opp_r as z_mul_opp_r;
  pose proof Nat2Z.inj_sub_max as Nat2Z_inj_sub_max;
  pose proof (Nat2Z.inj_succ: forall n: nat, Z.of_nat (S n) = Z.of_nat n + 1) as
    Nat2Z_inj_succ;
  pose proof ZifyInst.of_nat_to_nat_eq as z_of_nat_to_nat;
  pose proof Z.mul_max_distr_nonneg_l as z_mul_max_distr_nonneg_l;
    symmetry in z_mul_max_distr_nonneg_l;
  pose proof Z.mul_min_distr_nonpos_l as z_mul_max_distr_nonpos_l;
    symmetry in z_mul_max_distr_nonpos_l;
  pose proof Zmod_eq as z_mod_eq;
  pose proof Z.opp_add_distr as z_opp_add_distr;
  pose proof Z.add_opp_r as z_sub_def_bw;
  pose proof word.unsigned_sub as wunsigned_sub_bw;
    unfold word.wrap in wunsigned_sub_bw; symmetry in wunsigned_sub_bw;
  pose proof word.unsigned_add as wunsigned_add_bw;
    unfold word.wrap in wunsigned_add_bw; symmetry in wunsigned_add_bw;
  pose proof Z.mul_sub_distr_l as z_mul_sub_distr_l;
  pose proof Z.mod_small as z_mod_small;
  assert (z_mod_small_precond: forall a b,
           trigger! ((a mod b)) (is_worth_considering = consider (0 <= a < b)))
    by reflexivity;
  pose proof Z_mod_plus_full as z_mod_plus_full;
  pose proof Zmult_mod_distr_l as z_mult_mod_distr_l;
  pose proof Zmult_mod_distr_r as z_mult_mod_distr_r;
  pose proof Z.mul_1_r as z_mul_1_r;
  pose proof Z.mul_add_distr_l as z_mul_add_distr_l_bw; symmetry in z_mul_add_distr_l_bw;
  pose proof Z.mul_opp_r as z_mul_opp_r_bw; symmetry in z_mul_opp_r_bw;
  pose proof Z_div_mult_full as z_div_mult_full;
  pose proof Zdiv_mult_cancel_l as z_div_mult_cancel_l;
  pose proof Z.factor_add_mul_11 as z_factor_add_mul_11;
  pose proof Z.factor_add_mul_1q as z_factor_add_mul_1q;
  pose proof Z.factor_add_mul_q1 as z_factor_add_mul_q1;
  pose proof Z.factor_add_mul_qq as z_factor_add_mul_qq;
  pose proof Z.factor_sub_mul_1q as z_factor_sub_mul_1q;
  pose proof Z.factor_sub_mul_q1 as z_factor_sub_mul_q1;
  pose proof Z.factor_sub_mul_qq as z_factor_sub_mul_qq;
  pose proof Z_cancel_mul_ll as z_cancel_mul_ll.

Ltac pose_Prop_lemmas :=
  pose proof @eq_eq_sym as H_eq_eq_sym;
  pose proof eq_same_True as H_eq_same_True;
  pose proof and_True_l as and_True_l;
  pose proof and_True_r as and_True_r;
  pose proof or_True_l as or_True_l;
  pose proof or_True_r as or_True_r;
  pose proof and_proj_l as and_proj_l;
  pose proof and_proj_r as and_proj_r.

Ltac pose_list_lemmas :=
  pose proof @length_skipn as L_length_skipn;
  pose proof @List.firstn_length as L_firstn_length;
  pose proof @List.app_length as L_app_length;
  pose proof @length_cons as L_length_cons;
  pose proof @length_nil as L_length_nil.

Tactic Notation "egg_step" int(n) :=
  let G := lazymatch goal with |- ?x => x end in
  egg_simpl_goal n;
  [ try assumption; assert (is_worth_considering = consider G) by reflexivity  ..
  | cbv beta; try exact I].
