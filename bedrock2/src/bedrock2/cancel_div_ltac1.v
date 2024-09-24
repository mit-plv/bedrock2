From Coq Require Import ZArith. Local Open Scope Z_scope.

(* For the division canceler, we use statements of the form (a = d * a') instead of
   (a / d = a'), because the former also states that the remainder of the division is 0.
   Using the following lemma, we can go from the former to the latter form: *)
Lemma cancel_div_done: forall [d x x': Z], d <> 0 -> x = d * x' -> x / d = x'.
Proof. intros. subst. rewrite Z.mul_comm. apply Z.div_mul. assumption. Qed.

Lemma cancel_div_same: forall (d: Z), d = d * 1. intros. symmetry. apply Z.mul_1_r. Qed.

Lemma cancel_div_add_eq: forall [d a b a' b': Z],
    a = d * a' ->
    b = d * b' ->
    a + b = d * (a' + b').
Proof. intros. subst. symmetry. apply Z.mul_add_distr_l. Qed.

Lemma cancel_div_sub_eq: forall [d a b a' b': Z],
    a = d * a' ->
    b = d * b' ->
    a - b = d * (a' - b').
Proof. intros. subst. symmetry. apply Z.mul_sub_distr_l. Qed.

Lemma cancel_div_opp_eq: forall [d a a': Z],
    a = d * a' ->
    - a = d * (- a').
Proof. intros. subst. symmetry. apply Z.mul_opp_r. Qed.

Lemma cancel_div_mul_l_eq: forall [d a a'] (b: Z),
    a = d * a' ->
    a * b = d * (a' * b).
Proof. intros. subst. symmetry. apply Z.mul_assoc. Qed.

Lemma cancel_div_mul_r_eq: forall [d b b': Z] (a: Z),
    b = d * b' ->
    a * b = d * (a * b').
Proof. intros. subst. ring. Qed.

(* Given a divisor d and an expression e of type Z,
   returns a proof of type `e = d * q` for some quotient q if possible, or else fails. *)
Ltac cancel_div_rec d e :=
  lazymatch e with
  | d => constr:(cancel_div_same d)
  | Z.add ?a ?b =>
      let pfa := cancel_div_rec d a in
      let pfb := cancel_div_rec d b in
      constr:(cancel_div_add_eq pfa pfb)
  | Z.sub ?a ?b =>
      let pfa := cancel_div_rec d a in
      let pfb := cancel_div_rec d b in
      constr:(cancel_div_sub_eq pfa pfb)
  | Z.mul d ?a => constr:(@eq_refl Z e)
  | Z.mul ?a d => constr:(Z.mul_comm a d)
  | Z.mul ?a ?b =>
      match constr:(Set) with
      | _ => let pfa := cancel_div_rec d a in constr:(cancel_div_mul_l_eq b pfa)
      | _ => let pfb := cancel_div_rec d b in constr:(cancel_div_mul_r_eq a pfb)
      end
  | Z.opp ?a => let pfa := cancel_div_rec d a in constr:(cancel_div_opp_eq pfa)
  end.

(* Given a divisor d, a proof that `d <> 0`, and an expression e of type Z,
   returns a proof of type `e / d = q` for some quotient q if possible, or else fails. *)
Ltac cancel_div d d_nonzero_pf e :=
  let e_eq_prod_pf := cancel_div_rec d e in
  constr:(cancel_div_done d_nonzero_pf e_eq_prod_pf).

Goal forall (i j k count d: Z),
    d <> 0 ->
    (d * j - i * d * k + count * d) / d = j - i * k + count.
Proof.
  intros.
  lazymatch goal with
  | |- ?e / _ = _ => let r := cancel_div d H e in exact r
  end.
Abort.
