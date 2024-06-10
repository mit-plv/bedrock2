(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Require Coq.Bool.Bool.

(* sometimes used in a heuristic to differentiate between maps
   - representing memory
   - representing the content of a CBT *)
Require Import coqutil.Tactics.ident_ops.

(* needed because the other notation contains a closing C comment *)
Notation "a ||| b" := (mmap.du a b) (at level 34, no associativity).

(*
  file layout (sequentially):
  - GENERAL: tactics (and lemmas) that don't depend on definitions specific to this file
  - INDIVIDUAL BITS: defs, lemmas, and tactics for reasoning about
    the individual bits of a word (defining bit_at)
  - PREFIXES: defs, lemmas, and tactics about prefixes (:= list bool),
    (no pfx_mmeet yet, i.e., nothing operating on maps)
  - BASIC SMALL MAP OPS: lemmas and tactics for coqutil-defined
    map operations on small maps (map.empty and map.singleton _ _)
  - MAPS: general lemmas and tactics for maps
  - CUSTOM MAP OPS: defs, lemmas, and tactics for custom-defined
    operations on maps that are useful for CBTs (but no direct
    mention of CBTs yet)
  - CBT STRUCTURES: defs, lemmas, and tactics for CBTs and their parts
  - FRAMEWORK SETUP: a few things to set up in the live verification
    framework before providing implementations
  - CBT NODE MEM IMPL: the implementaiton of several utility functions for
    manipulating the raw memory of CBT nodes (allocation, freeing,
    possibly copying / moving)
  - CBT IMPL: the implementation of all the CBT functions
    (currently lookup, insert, delete) and any necessary utility functions)
*)

Load LiveVerif.

(* BEGIN GENERAL *)

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Ltac apply_ne :=
  match goal with
  | H: _ <> _ |- False => apply H; clear H
  end.

Ltac apply_neg :=
  match goal with
  | H: ~_ |- False => apply H; clear H
  end.

Ltac apply_forall :=
  match goal with
  | H: forall _, _ |- _ => apply H
  end.

Ltac f_apply f H :=
  match type of H with
  | ?lhs = ?rhs =>
      let h := fresh "H" in assert (h: f lhs = f rhs); [ rewrite H; reflexivity | ];
                            cbv beta in h; clear H; rename h into H
  end.

Ltac prove_ante H :=
  match type of H with
  | ?A -> ?C => let HA := fresh in assert (HA: A); [ | specialize (H HA); clear HA ]
  end.

Ltac purge x := repeat match goal with
                       | H: context[ x ] |- _ => clear H
                       end; clear x.

Ltac eq_neq_cases k1 k2 :=
  let H := fresh "H" in assert (H: k1 = k2 \/ k1 <> k2) by solve [ steps ]; destruct H.

Ltac none_nnone_cases opt :=
  let H := fresh "H" in assert (H: opt = None \/ opt <> None) by
    solve [ destruct opt; [ right | left ]; congruence ];
  destruct H.

Lemma eq_None_by_false {X : Type}: forall o: option X, ~(o <> None) -> o = None.
Proof.
  intros. destruct o. exfalso. apply H. congruence. congruence.
Qed.

(* an obvious finishing step that `steps` doesn't do *)
Ltac simple_finish_step :=
  solve [match goal with
  | H: ?P |- ?P => exact H
  | |- ?P <-> ?P => reflexivity
  | H1: ?P, H2: ~?P |- _ => apply H2 in H1; destruct H1
  | H: ?x <> ?x |- _ => exfalso; apply (H (eq_refl x))
  | H: ?a = ?b |- ?b = ?a => symmetry; exact H
  | H: ?a <> ?b |- ?b <> ?a => exact (not_eq_sym H)
  | H: Some _ = None |- _ => discriminate H
  | H: None = Some _ |- _ => discriminate H
  | |- Some _ <> None => let H := fresh "H" in intro H; discriminate H
  | |- None <> Some _ => let H := fresh "H" in intro H; discriminate H
  | H: ?a = Some _ |- ?a <> None => rewrite H;
      let He := fresh in intro He; discriminate He
  end].

(* replacing Bool.eqb _ _, word.eqb _ _, or _ =? _ with true or false
   when it's clear that that's what it evaluates to;
   should replace in all the hyps the same way it does in the goal *)
Ltac comparison_simpl_step :=
  match goal with
  (* _ =? _ *)
  | H: context[ ?n =? ?n ] |- _ => rewrite Z.eqb_refl in H
  | |- context[ ?n =? ?n ] => rewrite Z.eqb_refl

  | Heq: ?n = ?m, H: context con [ ?n =? ?m ] |- _ =>
      let cnvrt := context con [ n =? m ] in change cnvrt in H;
      replace (n =? m) with true in H by (rewrite Heq; rewrite Z.eqb_refl; reflexivity)
  | Heq: ?n = ?m |- context con [ ?n =? ?m ] =>
      let cnvrt := context con [ n =? m ] in change cnvrt;
      replace (n =? m) with true by (rewrite Heq; rewrite Z.eqb_refl; reflexivity)

  | Heq: ?n = ?m, H: context con [ ?m =? ?n ] |- _ =>
      let cnvrt := context con [ m =? n ] in change cnvrt in H;
      replace (m =? n) with true in H by (rewrite Heq; rewrite Z.eqb_refl; reflexivity)
  | Heq: ?n = ?m |- context con [ ?m =? ?n ] =>
      let cnvrt := context con [ m =? n ] in change cnvrt;
      replace (m =? n) with true by (rewrite Heq; rewrite Z.eqb_refl; reflexivity)

  | Hne: ?n <> ?m, H: context con [ ?n =? ?m ] |- _ =>
      let cnvrt := context con [ n =? m ] in change cnvrt in H;
      replace (n =? m) with false in H by (symmetry; apply Z.eqb_neq; exact Hne)
  | Hne: ?n <> ?m |- context con [ ?n =? ?m ] =>
      let cnvrt := context con [ n =? m ] in change cnvrt;
      replace (n =? m) with false by (symmetry; apply Z.eqb_neq; exact Hne)

  | Hne: ?n <> ?m, H: context con [ ?m =? ?n ] |- _ =>
      let cnvrt := context con [ m =? n ] in change cnvrt in H;
      replace (m =? n) with false in H
        by (symmetry; apply Z.eqb_neq; symmetry; exact Hne)
  | Hne: ?n <> ?m |- context con [ ?m =? ?n ] =>
      let cnvrt := context con [ m =? n ] in change cnvrt;
      replace (m =? n) with false
        by (symmetry; apply Z.eqb_neq; symmetry; exact Hne)

  | Hne: ?w <> /[0] |- context[ \[?w] =? 0 ] => replace (\[w] =? 0) with false by hwlia
  | Hne: ?w <> /[0], H2: context[ \[?w] =? 0 ] |- _ =>
        replace (\[w] =? 0) with false in H2 by hwlia

  (* Bool.eqb _ _ *)
  | H: context[ Bool.eqb ?b ?b ] |- _ => rewrite Bool.eqb_reflx in H
  | |- context[ Bool.eqb ?b ?b ] => rewrite Bool.eqb_reflx

  | H: context[ Bool.eqb (negb ?b) ?b ] |- _ => rewrite Bool.eqb_negb1 in H
  | |- context[ Bool.eqb (negb ?b) ?b ]  => rewrite Bool.eqb_negb1
  | H: context[ Bool.eqb ?b (negb ?b) ] |- _ => rewrite Bool.eqb_negb2 in H
  | |- context[ Bool.eqb ?b (negb ?b) ]  => rewrite Bool.eqb_negb2

  | H: context[ Bool.eqb false true ] |- _ => simpl Bool.eqb in H
  | |- context[ Bool.eqb false true ] => simpl Bool.eqb
  | H: context[ Bool.eqb true false ] |- _ => simpl Bool.eqb in H
  | |- context[ Bool.eqb true false ] => simpl Bool.eqb

  | Heq: ?b1 = ?c1, H: context con [ Bool.eqb ?b1 ?c2 ] |- _ =>
      is_constructor c1; is_constructor c2;
      let cnvrt := context con [ Bool.eqb b1 c2 ] in change cnvrt in H;
      replace (Bool.eqb b1 c2) with (Bool.eqb c1 c2) in H
        by (rewrite Heq; reflexivity)
  | Heq: ?b1 = ?c1 |- context con [ Bool.eqb ?b1 ?c2 ] =>
      is_constructor c1; is_constructor c2;
      let cnvrt := context con [ Bool.eqb b1 c2 ] in change cnvrt;
      replace (Bool.eqb b1 c2) with (Bool.eqb c1 c2)
        by (rewrite Heq; reflexivity)

  | Heq: ?b1 = ?c1, H: context con [ Bool.eqb ?c2 ?b1 ] |- _ =>
      is_constructor c1; is_constructor c2;
      let cnvrt := context con [ Bool.eqb c2 b1 ] in change cnvrt in H;
      replace (Bool.eqb c2 b1) with (Bool.eqb c2 c1) in H
        by (rewrite Heq; reflexivity)
  | Heq: ?b1 = ?c1 |- context con [ Bool.eqb ?c2 ?b1 ] =>
      is_constructor c1; is_constructor c2;
      let cnvrt := context con [ Bool.eqb c2 b1 ] in change cnvrt;
      replace (Bool.eqb c2 b1) with (Bool.eqb c2 c1)
        by (rewrite Heq; reflexivity)

  | Hne: ?b1 <> ?b2, H: context con [ Bool.eqb ?b1 ?b2 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt in H;
      replace (Bool.eqb b1 b2) with false in H
        by (symmetry; apply Bool.eqb_false_iff; exact Hne)
  | Hne: ?b1 <> ?b2 |- context con [ Bool.eqb ?b1 ?b2 ] =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt;
      replace (Bool.eqb b1 b2) with false
        by (symmetry; apply Bool.eqb_false_iff; exact Hne)

  | Hne: ?b1 <> ?b2, H: context con [ Bool.eqb ?b2 ?b1 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt in H;
      replace (Bool.eqb b2 b1) with false in H
        by (symmetry; apply Bool.eqb_false_iff; exact (not_eq_sym Hne))
  | Hne: ?b1 <> ?b2 |- context con [ Bool.eqb ?b2 ?b1 ] =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt;
      replace (Bool.eqb b2 b1) with false
        by (symmetry; apply Bool.eqb_false_iff; exact (not_eq_sym Hne))

  | Heq: ?b1 = ?b2, H: context con [ Bool.eqb ?b1 ?b2 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt in H;
      replace (Bool.eqb b1 b2) with true in H
        by (symmetry; rewrite Bool.eqb_true_iff; exact Heq)
  | Heq: ?b1 = ?b2 |- context con [ Bool.eqb ?b1 ?b2 ] =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt;
      replace (Bool.eqb b1 b2) with true
        by (symmetry; rewrite Bool.eqb_true_iff; exact Heq)

  | Heq: ?b1 = ?b2, H: context con [ Bool.eqb ?b2 ?b1 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt in H;
      replace (Bool.eqb b2 b1) with true in H
        by (symmetry; rewrite Bool.eqb_true_iff; symmetry; exact Heq)
  | Heq: ?b1 = ?b2 |- context con [ Bool.eqb ?b2 ?b1 ] =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt;
      replace (Bool.eqb b2 b1) with true
        by (symmetry; rewrite Bool.eqb_true_iff; symmetry; exact Heq)

  | Hne: ?b1 <> ?b2, H: context con [ Bool.eqb ?b1 ?b2 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt in H;
      replace (Bool.eqb b1 b2) with false in H
        by (symmetry; rewrite Bool.eqb_false_iff; exact Hne)
  | Hne: ?b1 <> ?b2 |- context con [ Bool.eqb ?b1 ?b2 ] =>
      let cnvrt := context con [ Bool.eqb b1 b2 ] in change cnvrt;
      replace (Bool.eqb b1 b2) with false
        by (symmetry; rewrite Bool.eqb_false_iff; exact Hne)

  | Hne: ?b1 <> ?b2, H: context con [ Bool.eqb ?b2 ?b1 ] |- _ =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt in H;
      replace (Bool.eqb b2 b1) with false in H
        by (symmetry; rewrite Bool.eqb_false_iff; symmetry; exact Hne)
  | Hne: ?b1 <> ?b2 |- context con [ Bool.eqb ?b2 ?b1 ] =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt;
      replace (Bool.eqb b2 b1) with false
        by (symmetry; rewrite Bool.eqb_false_iff; symmetry; exact Hne)

  | H: Bool.eqb ?b1 ?b2 = true |- _ => apply Bool.eqb_prop in H
  | H: Bool.eqb ?b1 ?b2 = false |- _ => rewrite Bool.eqb_false_iff in H

  (* word.eqb _ _ *)
  | H: context[ word.eqb ?w ?w ] |- _ => rewrite word.eqb_eq in H by reflexivity
  | |- context[ word.eqb ?w ?w ] => rewrite word.eqb_eq by reflexivity

  | Heq: ?w1 = ?w2, H: context con [ word.eqb ?w1 ?w2 ] |- _ =>
      let cnvrt := context con [ word.eqb w1 w2 ] in change cnvrt in H;
      replace (word.eqb w1 w2) with true in H
        by (symmetry; apply word.eqb_eq; exact Heq)
  | Heq: ?w1 = ?w2 |- context con [ word.eqb ?w1 ?w2 ] =>
      let cnvrt := context con [ word.eqb w1 w2 ] in change cnvrt;
      replace (word.eqb w1 w2) with true
        by (symmetry; apply word.eqb_eq; exact Heq)

  | Heq: ?w1 = ?w2, H: context con [ word.eqb ?w2 ?w1 ] |- _ =>
      let cnvrt := context con [ word.eqb w2 w1 ] in change cnvrt in H;
      replace (word.eqb w2 w1) with true in H
        by (symmetry; apply word.eqb_eq; symmetry; exact Heq)
  | Heq: ?w1 = ?w2 |- context con [ word.eqb ?w2 ?w1 ] =>
      let cnvrt := context con [ word.eqb w2 w1 ] in change cnvrt;
      replace (word.eqb w2 w1) with true
        by (symmetry; apply word.eqb_eq; symmetry; exact Heq)

  | Hne: ?w1 <> ?w2, H: context con [ word.eqb ?w1 ?w2 ] |- _ =>
      let cnvrt := context con [ word.eqb w1 w2 ] in change cnvrt in H;
      replace (word.eqb w1 w2) with false in H
        by (symmetry; apply word.eqb_ne; exact Hne)
  | Hne: ?w1 <> ?w2 |- context con [ word.eqb ?w1 ?w2 ] =>
      let cnvrt := context con [ word.eqb w1 w2 ] in change cnvrt;
      replace (word.eqb w1 w2) with false
        by (symmetry; apply word.eqb_ne; exact Hne)

  | Hne: ?w1 <> ?w2, H: context con [ word.eqb ?w2 ?w1 ] |- _ =>
      let cnvrt := context con [ word.eqb w2 w1 ] in change cnvrt in H;
      replace (word.eqb w2 w1) with false in H
        by (symmetry; apply word.eqb_ne; symmetry; exact Hne)
  | Hne: ?w1 <> ?w2 |- context con [ word.eqb ?w2 ?w1 ] =>
      let cnvrt := context con [ word.eqb w2 w1 ] in change cnvrt;
      replace (word.eqb w2 w1) with false
        by (symmetry; apply word.eqb_ne; symmetry; exact Hne)
end.

Lemma identical_if_branches : forall {T} (b: bool) (v: T), (if b then v else v) = v.
Proof.
  destruct b; reflexivity.
Qed.

Lemma neq_negb_eq : forall b1 b2, b1 <> negb b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2; steps.
Qed.

(* 12 because it comes up as the size (in bytes) of a CBT node allocation *)
Lemma unsigned_of_Z_12 : \[/[12]] = 12.
Proof.
  hwlia.
Qed.

Ltac misc_simpl_step :=
  match goal with
  | H: context [ negb ?c ] |- _ => is_constructor c; simpl negb in H
  | |- context [ negb ?c ] => is_constructor c; simpl negb
  | H: context [ negb (negb ?b) ] |- _ => rewrite Bool.negb_involutive in H
  | |- context [ negb (negb ?b) ] => rewrite Bool.negb_involutive
  | H: ?b = negb ?b |- _ => symmetry in H; destruct (Bool.no_fixpoint_negb b H)
  | H: negb ?b = ?b |- _ => destruct (Bool.no_fixpoint_negb b H)
  | H: ?b1 <> negb ?b2 |- _ => apply neq_negb_eq in H

  | H: context [ false && ?b ] |- _ => rewrite Bool.andb_false_l in H
  | |- context [ false && ?b ] => rewrite Bool.andb_false_l
  | H: context [ ?b && false ] |- _ => rewrite Bool.andb_false_r in H
  | |- context [ ?b && false ] => rewrite Bool.andb_false_r
  | H: context [ true && ?b ] |- _ => rewrite Bool.andb_true_l in H
  | |- context [ true && ?b ] => rewrite Bool.andb_true_l
  | H: context [ ?b && true ] |- _ => rewrite Bool.andb_true_r in H
  | |- context [ ?b && true ] => rewrite Bool.andb_true_r

  | H: context [ /[\[ _ ]] ] |- _ => rewrite word.of_Z_unsigned in H
  | |- context [ /[\[ _ ]] ] => rewrite word.of_Z_unsigned
  | H: context [ \[/[0]] ] |- _ => rewrite word.unsigned_of_Z_0 in H
  | |- context [ \[/[0]] ] => rewrite word.unsigned_of_Z_0
  | H: context [ \[/[1]] ] |- _ => rewrite word.unsigned_of_Z_1 in H
  | |- context [ \[/[1]] ] => rewrite word.unsigned_of_Z_1
  | H: context [ \[/[12]] ] |- _ => rewrite unsigned_of_Z_12 in H
  | |- context [ \[/[12]] ] => rewrite unsigned_of_Z_12

  | H: context[ if false then _ else _ ] |- _ => cbv iota in H
  | |- context[ if false then _ else _ ] => cbv iota
  | H: context[ if true then _ else _ ] |- _ => cbv iota in H
  | |- context[ if true then _ else _ ] => cbv iota

  | H: context[ if ?b then ?v else ?v ] |- _ => rewrite identical_if_branches in H
  | |- context[ if ?b then ?v else ?v ]  => rewrite identical_if_branches

  | |- impl1 (uintptr ?w1 ?a) (uintptr ?w2 ?a) =>
       (* using `set` because replace-ing (or also rewrite-ing) can
          instantiate evars (unexpectedly)
          see also https://github.com/coq/coq/issues/2072 *)
       let w1' := fresh in let w2' := fresh in set (w1' := w1); set (w2' := w2);
       replace w2' with w1'; [ reflexivity | subst w1' w2' ]

  | H: ?Q, H2: ?Q -> ?P |- _ => specialize (H2 H)
  | H: ?b = ?a, H2: ?a = ?b -> ?P |- _ => specialize (H2 (eq_sym H))
  | H: Some _ <> None |- _ => clear H
  | H: None <> Some _ |- _ => clear H
  end.

(* substitute a variable if it is equal to one of several selected expressions *)
Ltac subst_step :=
  match goal with
  | H: ?c = map.empty |- _ => is_var c; subst c
  | H: ?c = map.singleton _ _ |- _ => is_var c; subst c
  end.

Lemma Bool_neq_eq_negb : forall b1 b2, b1 <> b2 -> b1 = negb b2.
Proof.
  steps. destruct b1, b2; tauto.
Qed.

(* END GENERAL *)
(* BEGIN INDIVIDUAL BITS *)

Definition bit_at (w: word) (i: Z) := word.eqb (word.and (w ^>> /[i]) /[1]) /[1].

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  end.

Lemma and_not_1_iff_bit_at_false : forall (w: word) (i: Z),
  word.and (w ^>> /[i]) /[1] <> /[1] <-> bit_at w i = false.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_not_1_iff_bit_at_false_w : forall w i: word,
  word.and (w ^>> i) /[1] <> /[1] <-> bit_at w \[i] = false.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_1_iff_bit_at_true : forall (w: word) (i: Z),
  word.and (w ^>> /[i]) /[1] = /[1] <-> bit_at w i = true.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_1_iff_bit_at_true_w : forall w i: word,
  word.and (w ^>> i) /[1] = /[1] <-> bit_at w \[i] = true.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_1_eq_bit_at : forall (w1 i1 w2 i2: word),
  word.and (w1 ^>> i1) /[1] = word.and (w2 ^>> i2) /[1] ->
  bit_at w1 \[i1] = bit_at w2 \[i2].
Proof.
  unfold bit_at. steps.
Qed.

Lemma Z_bits_1 : forall n : Z, Z.testbit 1 n = (n =? 0).
Proof.
  intros. assert (Hcmp: n < 0 \/ 0 <= n) by lia. destruct Hcmp.
  - rewrite Z.testbit_neg_r; lia.
  - replace 1 with (2 ^ 0) by reflexivity. rewrite Z.pow2_bits_eqb; lia.
Qed.

Lemma Z_land_1_r : forall n, Z.land n 1 = if Z.testbit n 0 then 1 else 0.
Proof.
  intros. apply Z.bits_inj. unfold Z.eqf. intros.
  rewrite Z.land_spec.
  destruct (n0 =? 0) eqn:E; steps; destruct (Z.testbit n 0) eqn:E2; steps.
  - tauto.
  - rewrite Z_bits_1. steps.
  - rewrite Z_bits_1. rewrite Z.bits_0. steps.
Qed.

Lemma and_1_not_1_0 : forall w,
  word.and w /[1] <> /[1] -> word.and w /[1] = /[0].
Proof.
  steps. apply word.unsigned_inj. rewrite word.unsigned_and_nowrap.
  apply word.unsigned_inj' in H. rewrite word.unsigned_and_nowrap in H.
  steps. rewrite Z_land_1_r in *. steps.
Qed.

Lemma and_1_ne_bit_at : forall (w1 i1 w2 i2: word),
  word.and (w1 ^>> i1) /[1] <> word.and (w2 ^>> i2) /[1] ->
  bit_at w1 \[i1] <> bit_at w2 \[i2].
Proof.
  unfold bit_at. steps. intro. apply_ne.
  match goal with
  | H: _ = word.eqb ?wa ?wb |- _ => destruct (word.eqb wa wb) eqn:E
  end; steps.
  do 2 match goal with
  | H: _ <> /[1] |- _ => apply and_1_not_1_0 in H
  end. steps.
Qed.

Lemma bit_at_expand : forall w i,
  bit_at w i = word.eqb (word.and (w ^>> /[i]) /[1]) /[1].
Proof.
  unfold bit_at. steps.
Qed.

Ltac bit_at_step :=
  match goal with
  | H: word.and (_ ^>> /[_]) /[1] = /[1] |- _ => apply and_1_iff_bit_at_true in H
  | H: word.and (_ ^>> _) /[1] = /[1] |- _ => apply and_1_iff_bit_at_true_w in H
  | H: word.and (_ ^>> /[_]) /[1] <> /[1] |- _ => apply and_not_1_iff_bit_at_false in H
  | H: word.and (_ ^>> _) /[1] <> /[1] |- _ => apply and_not_1_iff_bit_at_false_w in H
  | H: word.and (_ ^>> _) /[1] = word.and (_ ^>> _) /[1] |- _ =>
       apply and_1_eq_bit_at
  | H: word.and (_ ^>> _) /[1] <> word.and (_ ^>> _) /[1] |- _ =>
       apply and_1_ne_bit_at
  | H: context [ word.eqb (word.and (?w ^>> /[?i]) /[1]) /[1] ] |- _ =>
       rewrite <- bit_at_expand in H
  | |- context [ word.eqb (word.and (?w ^>> /[?i]) /[1]) /[1] ] =>
       rewrite <- bit_at_expand
  end.

Lemma Z_testbit_is_bit_at : forall w i, 0 <= i < 32 -> Z.testbit \[w] i = bit_at w i.
Proof.
  intros. unfold bit_at. rewrite word.unsigned_eqb. rewrite word.unsigned_and_nowrap.
  steps. rewrite word.unsigned_sru_nowrap by hwlia. replace \[/[i]] with i by hwlia.
  rewrite Z_land_1_r.
  match goal with
  | |- _ = ?rhs => match rhs with
                   | context [ if ?b then _ else _ ] => replace rhs with b;
                                                        [ | destruct b; steps ]
                   end
  end.
  rewrite Z.bit0_odd. rewrite Z.testbit_odd. reflexivity.
Qed.

Lemma Z_testbit_past_word_width : forall w i, ~(0 <= i < 32) -> Z.testbit \[w] i = false.
Proof.
  intros. assert (Hcmp: i < 0 \/ 0 <= i < 32 \/ 32 <= i) by lia.
  destruct Hcmp as [ Hc | [ Hc | Hc ] ]; steps.
  - apply Z.testbit_neg_r. lia.
  - replace w with /[\[w]] by steps. rewrite word.unsigned_of_Z. unfold word.wrap.
    rewrite Z.mod_pow2_bits_high; steps.
Qed.

Lemma bit_at_inj : forall w1 w2,
  (forall i, 0 <= i < 32 -> bit_at w1 i = bit_at w2 i) -> w1 = w2.
Proof.
  steps. apply word.unsigned_inj. apply Z.bits_inj. unfold Z.eqf. intros.
  assert (Hcmp: 0 <= n < 32 \/ ~(0 <= n < 32)) by lia. destruct Hcmp.
  - repeat rewrite Z_testbit_is_bit_at by lia.
    match goal with
    | H: forall _, _ |- _ => apply H
    end.
    lia.
  - repeat rewrite Z_testbit_past_word_width; steps.
Qed.

Opaque bit_at.

(* END INDIVIDUAL BITS *)
(* BEGIN PREFIXES *)

Class pfx := {
  prefix : Type;

  pfx_len : prefix -> Z;
  pfx_len_nneg : forall p, 0 <= pfx_len p;

  pfx_bit : prefix -> Z -> option bool;
  pfx_bit_len : forall p i, 0 <= i < pfx_len p <-> pfx_bit p i <> None;
  pfx_bit_ext : forall p1 p2, (forall i, pfx_bit p1 i = pfx_bit p2 i) -> p1 = p2;

  (* all further operations are axiomatized in terms of pfx_len and pfx_bit *)

  (* pfx_nil *)
  pfx_nil : prefix;
  pfx_nil_len : pfx_len pfx_nil = 0;

  (* pfx_le *)
  pfx_le : prefix -> prefix -> Prop;
  pfx_le_spec : forall p1 p2,
    (forall i, 0 <= i < pfx_len p1 -> pfx_bit p1 i = pfx_bit p2 i) <-> pfx_le p1 p2;

  (* pfx_meet *)
  pfx_meet : prefix -> prefix -> prefix;
  pfx_meet_spec : forall p1 p2 p,
    pfx_le p (pfx_meet p1 p2) <-> pfx_le p p1 /\ pfx_le p p2;

  (* we use snoc to prove that given a set of prefixes, they cannot all have the same
     bit at the index equal to the length of their meet *)
  (* for pfx_meet (meet of just two prefixes), we could just prove this fact as a lemma
     (without explicitly using pfx_snoc). However, pfx_snoc makes the reasoning easier
     especially for pfx_mmeet (meet of many prefixes) -- mostly because at the time we
     introduce pfx_mmeet, we don't want to directly reasons about prefixes using raw
     bits anymore *)
  (* pfx_snoc *)
  pfx_snoc : prefix -> bool -> prefix;
  pfx_snoc_len : forall p b, pfx_len (pfx_snoc p b) = pfx_len p + 1;
  pfx_snoc_le : forall p b, pfx_le p (pfx_snoc p b);
  pfx_snoc_bit : forall p b, pfx_bit (pfx_snoc p b) (pfx_len p) = Some b;

  (* pfx_emb *)
  pfx_emb : word -> prefix;
  pfx_emb_len : forall w, pfx_len (pfx_emb w) = 32;
  pfx_emb_spec : forall w i,
    0 <= i < 32 -> pfx_bit (pfx_emb w) i = Some (bit_at w i)
}.

Fixpoint pfx'_le (l1 l2: list bool) :=
  match l1 with
  | nil => True
  | cons b1 l1' => match l2 with
                   | nil => False
                   | cons b2 l2' => if Bool.eqb b1 b2 then pfx'_le l1' l2' else False
                   end
  end.

Fixpoint pfx'_meet (l1 l2: list bool) :=
  match l1 with
  | nil => nil
  | cons b1 l1' => match l2 with
                   | nil => nil
                   | cons b2 l2' => if Bool.eqb b1 b2 then
                                      cons b1 (pfx'_meet l1' l2')
                                    else nil
                   end
  end.

Fixpoint pfx'_emb_rec (w: word) (remaining: nat): list bool :=
  match remaining with
  | O => nil
  | S n => cons (bit_at w (32 - Z.of_nat remaining)) (pfx'_emb_rec w n)
  end.

Lemma pfx'_emb_rec_bit : forall w (n: nat) i,
  0 <= i < Z.of_nat n -> List.get (pfx'_emb_rec w n) i = bit_at w (32 - Z.of_nat n + i).
Proof.
  induction n.
  - lia.
  - intros. unfold pfx'_emb_rec. fold pfx'_emb_rec. destruct (i =? 0) eqn:E; steps.
    rewrite IHn. steps. lia.
Qed.

#[refine]
Instance list_pfx : pfx := {
  prefix := list bool;
  pfx_len p := len p;
  pfx_bit p i := if (0 <=? i) && (i <? len p) then Some (List.get p i) else None;
  pfx_nil := nil;
  pfx_le := pfx'_le;
  pfx_meet := pfx'_meet;
  pfx_snoc p b := p ++ [|b|];
  pfx_emb w := pfx'_emb_rec w 32
}.
Proof.
  - lia.
  - intros.
    match goal with
    | |- context [ if ?cond then _ else _ ] => destruct cond eqn:E
    end; split; steps.
  - induction p1; destruct p2; intros;
    match goal with
    | H: forall _, _ = _ |- _ => rename H into HH
    end.
    + steps.
    + specialize (HH 0). steps. simpl (len nil) in *. lia.
    + specialize (HH 0). simpl len in *. steps; lia.
    + f_equal.
      * specialize (HH 0). steps.
      * match goal with
        | H: forall _, _ -> _ |- _ => apply H
        end. steps. specialize (HH (i + 1)).
        destruct (0 <=? i) eqn:E; steps.
        replace (0 <=? i + 1) with true in *; steps.
        replace (i + 1 <? len (a :: p1)) with (i <? len p1) in * by steps.
        replace (i + 1 <? len (b :: p2)) with (i <? len p2) in * by steps.
        replace ((a :: p1)[i + 1]) with (p1[i]) in * by steps.
        replace ((b :: p2)[i + 1]) with (p2[i]) in * by steps.
        steps.
  - steps.
  - induction p1; destruct p2; split; intros; simpl pfx'_le; simpl (len nil) in *;
    try match goal with
        | H: forall _, _ -> _ |- _ => rename H into HH
        end;
    try match goal with
        | H: forall _, _ <-> _ |- _ => rename H into IH
        end.
    + steps.
    + steps.
    + steps.
    + steps.
    + specialize (HH 0). simpl in *. prove_ante HH. lia. steps.
    + simpl in *. steps.
    + assert (a = b). { specialize (HH 0). simpl in *. prove_ante HH. lia. steps. }
      steps. apply IH. intros. specialize (HH (i + 1)). prove_ante HH. simpl len. lia.
      replace (0 <=? i) with true; steps. replace (0 <=? i + 1) with true in *; steps.
      replace (i + 1 <? len (a :: p1)) with (i <? len p1) in * by steps.
      replace (i + 1 <? len (b :: p2)) with (i <? len p2) in * by steps.
      replace (a :: p1)[i + 1] with p1[i] in * by steps.
      replace (b :: p2)[i + 1] with p2[i] in * by steps.
      steps.
    + specialize (IH p2). simpl pfx'_le in *.  destruct (Bool.eqb a b) eqn:E; steps.
      match goal with
      | H: pfx'_le _ _ |- _ => rewrite <- IH in H; rename H into HH
      end.
      clear IH. destruct (i =? 0) eqn:E2.
      * steps. subst. simpl.
        replace (0 <? len p1 + 1) with true by steps.
        replace (0 <? len p2 + 1) with true by steps.
        steps.
      * specialize (HH (i - 1)). prove_ante HH. { simpl len in *. lia. } simpl.
        replace (a :: p1)[i] with p1[i - 1] by steps.
        replace (b :: p2)[i] with p2[i - 1] by steps.
        replace (0 <=? i - 1) with true in * by steps.
        replace (0 <=? i) with true in * by steps.
        replace (i - 1 <? len p1) with (i <? len p1 + 1) in * by steps.
        replace (i - 1 <? len p2) with (i <? len p2 + 1) in * by steps.
        steps.
  - intros. generalize dependent p1. generalize dependent p2. induction p.
    { simpl. steps. }
    destruct p1, p2; simpl; steps. destruct a, b, b0; steps; auto.
  - steps.
  - induction p; simpl; steps.
  - intros. replace ((0 <=? len p) && (len p <? len (p ++ [|b|]))) with true by steps.
    steps.
  - intros. simpl. steps.
  - intros. simpl len.
    match goal with
    | |- context [ if ?cond then _ else _ ] => replace cond with true by steps
    end.
    rewrite pfx'_emb_rec_bit. steps. steps.
Qed.

Lemma pfx_le_nil : forall p, pfx_le pfx_nil p.
Proof.
  intros. rewrite <- pfx_le_spec. rewrite pfx_nil_len. lia.
Qed.

Lemma pfx_le_reflx : forall p, pfx_le p p.
Proof.
  intros. rewrite <- pfx_le_spec. steps.
Qed.

Lemma pfx_le_len : forall p1 p2, pfx_le p1 p2 -> pfx_len p1 <= pfx_len p2.
Proof.
  intros. enough (~(pfx_len p2 < pfx_len p1)) by lia. intro.
  pose proof (pfx_len_nneg p2).
  match goal with
  | H: pfx_le _ _ |- _ =>
       rewrite <- pfx_le_spec in H; specialize (H (pfx_len p2)); prove_ante H
  end.
  lia.
  pose proof (pfx_bit_len p1 (pfx_len p2)).
  pose proof (pfx_bit_len p2 (pfx_len p2)).
  match goal with
  | H: pfx_bit _ _ = pfx_bit _ _ |- _ => rewrite H in *; clear H
  end.
  match goal with
  | H: _ <-> _ |- _ => rewrite <- H in *; clear H
  end.
  lia.
Qed.

Lemma pfx_le_asym : forall p1 p2, pfx_le p1 p2 -> pfx_le p2 p1 -> p1 = p2.
Proof.
  intros. assert (pfx_len p1 = pfx_len p2).
  do 2 match goal with
       | H: pfx_le _ _ |- _ => apply pfx_le_len in H
       end. lia.
  apply pfx_bit_ext. steps.
  assert (Hinrange: 0 <= i < pfx_len p1 \/ ~(0 <= i < pfx_len p1)) by lia.
  destruct Hinrange.
  - match goal with
    | H: pfx_le _ _ |- _ => rewrite <- pfx_le_spec in H; specialize (H i); prove_ante H
    end.
    lia. steps.
  - pose proof (pfx_bit_len p1 i) as Hbl1. pose proof (pfx_bit_len p2 i) as Hbl2.
    match goal with
    | H: pfx_len _ = pfx_len _ |- _ => rewrite H in *; clear H
    end.
    assert (pfx_bit p1 i = None).
    { rewrite Hbl1 in *. destruct (pfx_bit p1 i). exfalso. apply_neg. steps. steps. }
    assert (pfx_bit p2 i = None).
    { rewrite Hbl2 in *. destruct (pfx_bit p2 i). exfalso. apply_neg. steps. steps. }
    congruence.
Qed.

Lemma pfx_le_trans : forall p1 p2 p3, pfx_le p1 p2 -> pfx_le p2 p3 -> pfx_le p1 p3.
Proof.
  intros. eassert _. { apply (pfx_le_len p1 p2). assumption. }
  rewrite <- pfx_le_spec. intros.
  do 2 match goal with
       | H: pfx_le _ _ |- _ =>
            rewrite <- pfx_le_spec in H; specialize (H i); prove_ante H; [ lia | ]
       end.
  congruence.
Qed.

Lemma pfx_lele_len_ord : forall p1 p2 p,
  pfx_le p1 p -> pfx_le p2 p -> pfx_len p1 <= pfx_len p2 -> pfx_le p1 p2.
Proof.
  intros. rewrite <- pfx_le_spec in *. intros.
  do 2 match goal with
       | H: forall _, _ |- _ => specialize (H i); prove_ante H; [ lia | ]
       end.
  congruence.
Qed.

Lemma pfx_lele_len_eq : forall p1 p2 p,
  pfx_le p1 p -> pfx_le p2 p -> pfx_len p1 = pfx_len p2 -> p1 = p2.
Proof.
  intros. apply pfx_le_asym; apply pfx_lele_len_ord with (p:=p); steps.
Qed.

Lemma pfx_lele_tot : forall p1 p2 p,
  pfx_le p1 p -> pfx_le p2 p -> pfx_le p1 p2 \/ pfx_le p2 p1.
Proof.
  intros. assert (Hor: pfx_len p1 <= pfx_len p2 \/ pfx_len p2 <= pfx_len p1) by lia.
  destruct Hor; [ left | right ]; apply pfx_lele_len_ord with (p:=p); assumption.
Qed.

Lemma pfx_meet_le_both : forall p p1 p2,
  pfx_le p p1 -> pfx_le p p2 -> pfx_le p (pfx_meet p1 p2).
Proof.
  intros. apply pfx_meet_spec. tauto.
Qed.

Lemma pfx_meet_le_l : forall p1 p2, pfx_le (pfx_meet p1 p2) p1.
Proof.
  intros. eapply proj1. rewrite <- pfx_meet_spec. eapply pfx_le_reflx.
Qed.

Lemma pfx_meet_le_r : forall p1 p2, pfx_le (pfx_meet p1 p2) p2.
Proof.
  intros. eapply proj2. rewrite <- pfx_meet_spec. eapply pfx_le_reflx.
Qed.

(* TODO: consider using a hint database for the `auto`s and `eauto`s below *)

Lemma pfx_meet_id : forall p, pfx_meet p p = p.
Proof.
  auto using pfx_le_asym, pfx_meet_le_l, pfx_le_reflx, pfx_meet_le_both.
Qed.

Lemma pfx_meet_comm : forall p1 p2, pfx_meet p1 p2 = pfx_meet p2 p1.
Proof.
  auto using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_l, pfx_meet_le_r.
Qed.

Lemma pfx_meet_assoc : forall p1 p2 p3,
  pfx_meet (pfx_meet p1 p2) p3 = pfx_meet p1 (pfx_meet p2 p3).
Proof.
  eauto 10
    using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_l, pfx_meet_le_r, pfx_le_trans.
Qed.

Lemma pfx_meet_nil_l : forall p, pfx_meet pfx_nil p = pfx_nil.
Proof.
  auto using pfx_le_asym, pfx_meet_le_l, pfx_le_nil.
Qed.

Lemma pfx_meet_nil_r : forall p, pfx_meet p pfx_nil = pfx_nil.
Proof.
  auto using pfx_le_asym, pfx_meet_le_r, pfx_le_nil.
Qed.

Lemma pfx_meet_le_meet_l : forall p1 p2 p,
  pfx_le p1 p2 -> pfx_le (pfx_meet p1 p) (pfx_meet p2 p).
Proof.
  eauto 10
    using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_l, pfx_meet_le_r, pfx_le_trans.
Qed.

Lemma pfx_meet_le_meet_r : forall p1 p2 p,
  pfx_le p1 p2 -> pfx_le (pfx_meet p p1) (pfx_meet p p2).
Proof.
  eauto 10
    using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_l, pfx_meet_le_r, pfx_le_trans.
Qed.

Lemma pfx_meet_le_eq : forall p1 p2, pfx_le p1 p2 -> pfx_meet p1 p2 = p1.
Proof.
  auto using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_l, pfx_le_reflx.
Qed.

Lemma pfx_meet_le_eq' : forall p1 p2, pfx_le p1 p2 -> pfx_meet p2 p1 = p1.
Proof.
  auto using pfx_le_asym, pfx_meet_le_both, pfx_meet_le_r, pfx_le_reflx.
Qed.

Lemma pfx_snoc_ext_le : forall p1 p2 b,
  pfx_le p1 p2 -> pfx_bit p2 (pfx_len p1) = Some b -> pfx_le (pfx_snoc p1 b) p2.
Proof.
  intros. rewrite <- pfx_le_spec. rewrite pfx_snoc_len. steps.
  destruct (i =? pfx_len p1) eqn:E; steps.
  - subst. rewrite pfx_snoc_bit. steps.
  - pose proof (pfx_snoc_le p1 b) as Hsl. rewrite <- pfx_le_spec in Hsl.
    specialize (Hsl i). prove_ante Hsl. lia.
    match goal with
    | H: pfx_le _ _ |- _ => rewrite <- pfx_le_spec in H; specialize (H i); prove_ante H
    end.
    lia. congruence.
Qed.

Lemma pfx_snoc_le_self : forall p b, ~pfx_le (pfx_snoc p b) p.
Proof.
  intros. intro Hle. apply pfx_le_len in Hle. rewrite pfx_snoc_len in Hle. lia.
Qed.

Lemma pfx_emb_inj : forall k1 k2, pfx_emb k1 = pfx_emb k2 -> k1 = k2.
Proof.
  intros. apply bit_at_inj. intros.
  match goal with
  | H: pfx_emb _ = pfx_emb _ |- _ => f_apply (fun p => pfx_bit p i) H
  end.
  do 2 rewrite pfx_emb_spec in *; steps.
Qed.

Lemma pfx_meet_neq_emb_len : forall w1 w2,
  w1 <> w2 -> pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2)) < 32.
Proof.
  intros.
  match goal with
  | |- ?l < 32 => assert (Hb: l <= 32);
       [ rewrite <- (pfx_emb_len w1); apply pfx_le_len; apply pfx_meet_le_l
       | enough (l <> 32) by lia ]; clear Hb
  end.
  intro. apply_ne. assert (pfx_meet (pfx_emb w1) (pfx_emb w2) = pfx_emb w1). {
    apply pfx_lele_len_eq with (p:=pfx_emb w1). apply pfx_meet_le_l.
    apply pfx_le_reflx. rewrite pfx_emb_len. congruence. }
  assert (pfx_meet (pfx_emb w1) (pfx_emb w2) = pfx_emb w2). {
    apply pfx_lele_len_eq with (p:=pfx_emb w2). apply pfx_meet_le_r.
    apply pfx_le_reflx. rewrite pfx_emb_len. congruence. }
  apply pfx_emb_inj. congruence.
Qed.

Lemma pfx_meet_emb_bit_at_len : forall w1 w2,
  w1 <> w2 ->
  bit_at w1 (pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2))) <>
  bit_at w2 (pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2))).
Proof.
  intros. intro. eassert _. { apply pfx_meet_neq_emb_len. eassumption. }
  apply (pfx_snoc_le_self (pfx_meet (pfx_emb w1) (pfx_emb w2))
         (bit_at w1 (pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2))))).
  rewrite pfx_meet_spec. split; apply pfx_snoc_ext_le;
    try apply pfx_meet_le_l; try apply pfx_meet_le_r.
  apply pfx_emb_spec.
  pose proof (pfx_len_nneg (pfx_meet (pfx_emb w1) (pfx_emb w2))). lia.
  match goal with
  | H: bit_at _ _ = bit_at _ _ |- _ => rewrite H
  end.
  apply pfx_emb_spec.
  pose proof (pfx_len_nneg (pfx_meet (pfx_emb w1) (pfx_emb w2))). lia.
Qed.

Lemma pfx_meet_bit_diff_len : forall k1 k2 i b1 b2,
  0 <= i -> bit_at k1 i = b1 -> bit_at k2 i = b2 -> b1 <> b2 ->
  pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)) <= i.
Proof.
  intros.
  enough (~(i < pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)))) by lia. intro.
  apply_ne. steps.
  pose proof (pfx_meet_le_l (pfx_emb k1) (pfx_emb k2)).
  pose proof (pfx_meet_le_r (pfx_emb k1) (pfx_emb k2)).
  eassert (Hle: _). eapply pfx_le_len. apply pfx_meet_le_l.
  erewrite pfx_emb_len in Hle. instantiate (2:=k1) in Hle.
  instantiate (1:=pfx_emb k2) in Hle.
  do 2 match goal with
       | H: pfx_le _ _ |- _ =>
            rewrite <- pfx_le_spec in H; specialize (H i); prove_ante H; [ lia | ];
            rewrite pfx_emb_spec in H by lia
       end.
  congruence.
Qed.

Lemma pfx_cb_charac : forall k1 k2 n,
  0 <= n < 32 ->
  (forall i, 0 <= i < n -> bit_at k1 i = bit_at k2 i) -> bit_at k1 n <> bit_at k2 n ->
  pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)) = n.
Proof.
  intros. apply Z.le_antisymm.
  - eapply pfx_meet_bit_diff_len. lia. reflexivity. reflexivity. assumption.
  - eq_neq_cases k1 k2; subst; steps.
    eassert _. { apply pfx_meet_emb_bit_at_len. eassumption. }
    match goal with
    | H: bit_at _ (pfx_len ?pl) <> bit_at _ _ |- _ =>
         pose proof (pfx_len_nneg pl); remember (pfx_len pl) as l; clear Heql
    end.
    enough (~(l < n)) by lia. intro.
    apply_ne. apply_forall. lia.
Qed.

Lemma pfx_meet_left_emb_len_bound : forall p w,
  pfx_len (pfx_meet (pfx_emb w) p) <= 32.
Proof.
  intros. rewrite <- (pfx_emb_len w). apply pfx_le_len. apply pfx_meet_le_l.
Qed.

Lemma pfx_meet_right_emb_len_bound : forall p w,
  pfx_len (pfx_meet p (pfx_emb w)) <= 32.
Proof.
  intros. rewrite <- (pfx_emb_len w). apply pfx_le_len. apply pfx_meet_le_r.
Qed.

Ltac pfx_step :=
  match goal with
  | H: context [ pfx_len (pfx_emb _) ] |- _ => rewrite pfx_emb_len in H
  | |- context [ pfx_len (pfx_emb _) ] => rewrite pfx_emb_len
  | H: context [ pfx_len pfx_nil ] |- _ => rewrite pfx_nil_len in H
  | |- context [ pfx_len pfx_nil ] => rewrite pfx_nil_len
  | H: context [ pfx_meet pfx_nil _ ] |- _ => rewrite pfx_meet_nil_l in H
  | |- context [ pfx_meet pfx_nil _ ] => rewrite pfx_meet_nil_l
  | H: context [ pfx_meet _ pfx_nil ] |- _ => rewrite pfx_meet_nil_r in H
  | |- context [ pfx_meet _ pfx_nil ] => rewrite pfx_meet_nil_r
  | H: context [ pfx_meet ?p ?p ] |- _ => rewrite pfx_meet_id in H
  | |- context [ pfx_meet ?p ?p ] => rewrite pfx_meet_id
  | |- pfx_le (pfx_meet ?p _) ?p => apply pfx_meet_le_l
  | |- pfx_le (pfx_meet _ ?p) ?p => apply pfx_meet_le_r
  | |- pfx_le ?p ?p => apply pfx_le_reflx
  | Hle: pfx_le ?p1 ?p2, H: context [ pfx_meet ?p1 ?p2 ] |- _ =>
       rewrite (pfx_meet_le_eq p1 p2 Hle) in H
  | Hle: pfx_le ?p1 ?p2 |- context [ pfx_meet ?p1 ?p2 ] =>
       rewrite (pfx_meet_le_eq p1 p2 Hle)
  | Hle: pfx_le ?p1 ?p2, H: context [ pfx_meet ?p2 ?p1 ] |- _ =>
       rewrite (pfx_meet_le_eq' p1 p2 Hle) in H
  | Hle: pfx_le ?p1 ?p2 |- context [ pfx_meet ?p2 ?p1 ] =>
       rewrite (pfx_meet_le_eq' p1 p2 Hle)
  | |- pfx_len (pfx_meet (pfx_emb _) _) <= 32 => apply pfx_meet_left_emb_len_bound
  | |- pfx_len (pfx_meet _ (pfx_emb _)) <= 32 => apply pfx_meet_right_emb_len_bound
  | |- ?p1 = pfx_meet ?p1 ?p2 => symmetry; apply pfx_meet_le_eq
  | |- ?p1 = pfx_meet ?p2 ?p1 => symmetry; apply pfx_meet_le_eq'
  | |- pfx_meet ?p1 ?p2 = ?p1 => apply pfx_meet_le_eq
  | |- pfx_meet ?p2 ?p1 = ?p1 => apply pfx_meet_le_eq'
  | H: ?k1 <> ?k2 |- pfx_len (pfx_meet (pfx_emb ?k1) (pfx_emb ?k2)) < 32 =>
       exact (pfx_meet_neq_emb_len k1 k2 H)
  end.

(* END PREFIXES *)
(* BEGIN BASIC SMALL MAP OPS *)

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

Lemma map_get_singleton_same : forall (k v: word),
  map.get (map.singleton k v) k = Some v.
Proof.
  intros. unfold map.singleton. apply map.get_put_same.
Qed.

Lemma map_get_singleton_same_eq : forall k v k': word,
  k = k' -> map.get (map.singleton k v) k' = Some v.
Proof.
  intros. subst. apply map_get_singleton_same.
Qed.

Lemma map_get_singleton_diff : forall k v k' : word,
  k <> k' -> map.get (map.singleton k v) k' = None.
Proof.
  intros. unfold map.singleton. rewrite map.get_put_diff. apply map.get_empty.
  congruence.
Qed.

Lemma map_put_singleton_same : forall k v v': word,
  map.put (map.singleton k v) k v' = map.singleton k v'.
Proof.
  intros. unfold map.singleton. apply map.put_put_same.
Qed.

Lemma map_put_singleton_same_eq : forall k v k' v': word,
  k = k' -> map.put (map.singleton k v) k' v' = map.singleton k v'.
Proof.
  intros. subst. apply map_put_singleton_same.
Qed.

Lemma map_remove_singleton_same : forall k v : word,
  map.remove (map.singleton k v) k = map.empty.
Proof.
  intros. unfold map.singleton. rewrite map.remove_put_same.
  rewrite map.remove_empty. reflexivity.
Qed.

Lemma map_remove_singleton_same_eq : forall k v k' : word,
  k = k' -> map.remove (map.singleton k v) k' = map.empty.
Proof.
  intros. subst. apply map_remove_singleton_same.
Qed.

Lemma map_remove_singleton_diff : forall k v k' : word,
  k <> k' -> map.remove (map.singleton k v) k' = map.singleton k v.
Proof.
  intros. unfold map.singleton. rewrite map.remove_put_diff.
  rewrite map.remove_empty. reflexivity. congruence.
Qed.

(* simplify basic map operations (get, put, remove) operating on
   map.empty or map.singleton *)
Ltac small_map_basic_op_simpl_step :=
  match goal with
  (* map.get *)
  | H: context [ map.get map.empty _ ] |- _ => rewrite map.get_empty in H
  | |- context [ map.get map.empty _ ] => rewrite map.get_empty

  | H: context [ map.get (map.singleton ?k ?v) ?k ] |- _ =>
      rewrite map_get_singleton_same in H
  | |- context [ map.get (map.singleton ?k ?v) ?k ] =>
      rewrite map_get_singleton_same

  | Heq: ?k = ?k', H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_get_singleton_same_eq k v k') in H by (exact Heq)
  | Heq: ?k = ?k' |- context [ map.get (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_get_singleton_same_eq k v k') by (exact Heq)

  | Heq: ?k' = ?k, H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_get_singleton_same_eq k v k') in H by (symmetry; exact Heq)
  | Heq: ?k' = ?k |- context [ map.get (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_get_singleton_same_eq k v k') by (symmetry; exact Heq)

  | Hne: ?k <> ?k', H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_get_singleton_diff k v k') in H by (exact Hne)
  | Hne: ?k <> ?k' |- context [ map.get (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_get_singleton_diff k v k') by (exact Hne)

  | Hne: ?k' <> ?k, H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_get_singleton_diff k v k') in H by (symmetry; exact Hne)
  | Hne: ?k' <> ?k |- context [ map.get (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_get_singleton_diff k v k') by (symmetry; exact Hne)

  (* map.put *)
  | H: context [ map.put map.empty ?k ?v ] |- _ =>
      change (map.put map.empty k v) with (map.singleton k v) in H
  | |- context [ map.put map.empty ?k ?v ] =>
      change (map.put map.empty k v) with (map.singleton k v)

  | H: context [ map.put (map.singleton ?k ?v) ?k ?v' ] |- _ =>
      rewrite map_put_singleton_same in H
  | |- context [ map.put (map.singleton ?k ?v) ?k ?v' ] =>
      rewrite map_put_singleton_same

  | Heq: ?k = ?k', H: context [ map.put (map.singleton ?k ?v) ?k' ?v' ] |- _ =>
      rewrite (map_put_singleton_same_eq k v k' v') in H by (exact Heq)
  | Heq: ?k = ?k' |- context [ map.put (map.singleton ?k ?v) ?k' ?v' ] =>
      rewrite (map_put_singleton_same_eq k v k' v') by (exact Heq)

  | Heq: ?k' = ?k, H: context [ map.put (map.singleton ?k ?v) ?k' ?v' ] |- _ =>
      rewrite (map_put_singleton_same_eq k v k' v') in H by (symmetry; exact Heq)
  | Heq: ?k' = ?k |- context [ map.put (map.singleton ?k ?v) ?k' ?v' ] =>
      rewrite (map_put_singleton_same_eq k v k' v') by (symmetry; exact Heq)

  (* map.remove *)
  | H: context [ map.remove map.empty _ ] |- _ =>
      rewrite map.remove_empty in H
  | |- context [ map.remove map.empty _ ] =>
      rewrite map.remove_empty

  | H: context [ map.remove (map.singleton ?k ?v) ?k ] |- _ =>
      rewrite map_remove_singleton_same in H
  | |- context [ map.remove (map.singleton ?k ?v) ?k ] =>
      rewrite map_remove_singleton_same

  | Heq: ?k = ?k', H: context [ map.remove (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_remove_singleton_same_eq k v k') in H by (exact Heq)
  | Heq: ?k = ?k' |- context [ map.remove (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_remove_singleton_same_eq k v k') by (exact Heq)

  | Heq: ?k' = ?k, H: context [ map.remove (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_remove_singleton_same_eq k v k') in H by (symmetry; exact Heq)
  | Heq: ?k' = ?k |- context [ map.remove (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_remove_singleton_same_eq k v k') by (symmetry; exact Heq)

  | Hne: ?k <> ?k', H: context [ map.remove (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_remove_singleton_diff k v k') in H by (exact Hne)
  | Hne: ?k <> ?k' |- context [ map.remove (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_remove_singleton_diff k v k') by (exact Hne)

  | Hne: ?k' <> ?k, H: context [ map.remove (map.singleton ?k ?v) ?k' ] |- _ =>
      rewrite (map_remove_singleton_diff k v k') in H by (symmetry; exact Hne)
  | Hne: ?k' <> ?k |- context [ map.remove (map.singleton ?k ?v) ?k' ] =>
      rewrite (map_remove_singleton_diff k v k') by (symmetry; exact Hne)
  end.

(* END BASIC SMALL MAP OPS *)
(* BEGIN MAPS *)

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => bit_at_step
  | |- _ => pfx_step
  | |- _ => small_map_basic_op_simpl_step
  end.

Lemma map_get_singleton_not_None : forall (k v k': word),
  map.get (map.singleton k v) k' <> None -> k = k'.
Proof.
  intros. eq_neq_cases k k'; steps.
Qed.

Lemma map_singleton_inj : forall (k1 k2 v1 v2 : word),
    map.singleton k1 v1 = map.singleton k2 v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros. assert (k1 = k2). { eq_neq_cases k1 k2; steps. exfalso.
  f_apply (fun m: word_map => map.get m k2) H. steps. }
  steps. f_apply (fun m: word_map => map.get m k2) H. steps.
Qed.

Lemma map_extends_nonempty : forall (cbig csmall: word_map),
  map.extends cbig csmall -> csmall <> map.empty -> cbig <> map.empty.
Proof.
  unfold map.extends. intros. intro.
  match goal with
  | H: csmall <> map.empty |- _ => apply H
  end. apply map.map_ext. steps. destruct (map.get csmall k) eqn:E;
  [ exfalso | reflexivity ].
  match goal with
  | H: forall _, _ |- _ => apply H in E
  end.
  steps.
Qed.

Lemma map_extends_get_nnone : forall (cbig csmall: word_map) k,
  map.extends cbig csmall -> map.get csmall k <> None -> map.get cbig k <> None.
Proof.
  unfold map.extends. intros. destruct (map.get csmall k) eqn:E; steps.
  match goal with
  | H: forall _, _ |- _ => apply H in E
  end.
  congruence.
Qed.

Lemma map_extends_put_new : forall (c: word_map) (k v: word),
  map.get c k = None -> map.extends (map.put c k v) c.
Proof.
  unfold map.extends. intros. eq_neq_cases k x.
  - congruence.
  - rewrite map.get_put_diff; steps.
Qed.

Lemma map_extends_trans : forall c1 c2 c3: word_map,
  map.extends c1 c2 -> map.extends c2 c3 -> map.extends c1 c3.
Proof.
  unfold map.extends. auto.
Qed.

Lemma map_put_nonempty : forall (c: word_map) k v,
  map.put c k v <> map.empty.
Proof.
  intros.
  match goal with
  | |- ?L <> ?R => enough (map.get L k <> map.get R k)
  end.
  congruence.
  steps. rewrite map.get_put_same. steps.
Qed.

Lemma map_get_nnone_nonempty : forall (c: word_map) k,
  map.get c k <> None -> c <> map.empty.
Proof.
  intros. intro. steps.
Qed.

Lemma map_singleton_nonempty : forall (k v: word), map.singleton k v <> map.empty.
Proof.
  intros. intro He. f_apply (fun m: word_map => map.get m k) He. steps.
Qed.

Ltac map_step :=
  match goal with
  | H: map.get (map.singleton ?k ?v) ?k' <> None |- _ =>
        apply map_get_singleton_not_None in H
  | H: map.singleton ?k1 ?v1 = map.singleton ?k2 ?v2 |- _ =>
        apply map_singleton_inj in H

  | H: context [ map.get (map.put _ ?k _) ?k ] |- _ => rewrite map.get_put_same in H
  | |- context [ map.get (map.put _ ?k _) ?k ] => rewrite map.get_put_same
  | Heq: ?k = ?k', H: context [ map.get (map.put ?c ?k ?v) ?k' ] |- _ =>
        replace (map.get (map.put c k v) k') with (Some v) in H by
        (rewrite Heq; symmetry; apply map.get_put_same)
  | Heq: ?k = ?k' |- context [ map.get (map.put ?c ?k ?v) ?k' ] =>
        replace (map.get (map.put c k v) k') with (Some v) by
        (rewrite Heq; symmetry; apply map.get_put_same)
  | Heq: ?k' = ?k, H: context [ map.get (map.put ?c ?k ?v) ?k' ] |- _ =>
        replace (map.get (map.put c k v) k') with (Some v) in H by
        (rewrite Heq; symmetry; apply map.get_put_same)
  | Heq: ?k' = ?k |- context [ map.get (map.put ?c ?k ?v) ?k' ] =>
        replace (map.get (map.put c k v) k') with (Some v) by
        (rewrite Heq; symmetry; apply map.get_put_same)

  | Hne: ?k <> ?k', H: context [ map.get (map.put ?c ?k ?v) ?k' ] |- _ =>
        replace (map.get (map.put c k v) k') with (map.get c k') in H by
        (symmetry; apply map.get_put_diff; exact (not_eq_sym Hne))
  | Hne: ?k <> ?k' |- context [ map.get (map.put ?c ?k ?v) ?k' ] =>
        replace (map.get (map.put c k v) k') with (map.get c k') by
        (symmetry; apply map.get_put_diff; exact (not_eq_sym Hne))
  | Hne: ?k' <> ?k, H: context [ map.get (map.put ?c ?k ?v) ?k' ] |- _ =>
        replace (map.get (map.put c k v) k') with (map.get c k') in H by
        (symmetry; apply map.get_put_diff; exact Hne)
  | Hne: ?k' <> ?k |- context [ map.get (map.put ?c ?k ?v) ?k' ] =>
        replace (map.get (map.put c k v) k') with (map.get c k') by
        (symmetry; apply map.get_put_diff; exact Hne)

  | H: map.empty = map.put _ _ _ |- _ =>
        symmetry in H;destruct (map_put_nonempty _ _ _ H)
  | H: map.put _ _ _ = map.empty |- _ => destruct (map_put_nonempty _ _ _ H)

  | H: context [ map.get (map.remove _ ?k) ?k ] |- _ =>
        rewrite map.get_remove_same in H
  | |- context [ map.get (map.remove _ ?k) ?k ] => rewrite map.get_remove_same
  | Heq: ?k = ?k', H: context [ map.get (map.remove ?c ?k) ?k' ] |- _ =>
        replace (map.get (map.remove c k) k') with None in H by
        (rewrite Heq; symmetry; apply map.get_remove_same)
  | Heq: ?k = ?k' |- context [ map.get (map.remove ?c ?k) ?k' ] =>
        replace (map.get (map.remove c k) k') with None by
        (rewrite Heq; symmetry; apply map.get_remove_same)
  | Heq: ?k' = ?k, H: context [ map.get (map.remove ?c ?k) ?k' ] |- _ =>
        replace (map.get (map.remove c k) k') with None in H by
        (rewrite Heq; symmetry; apply map.get_remove_same)
  | Heq: ?k' = ?k |- context [ map.get (map.remove ?c ?k) ?k' ] =>
        replace (map.get (map.remove c k) k') with None by
        (rewrite Heq; symmetry; apply map.get_remove_same)

  | Hne: ?k <> ?k', H: context [ map.get (map.remove ?c ?k) ?k' ] |- _ =>
        replace (map.get (map.remove c k) k') with (map.get c k') in H by
        (symmetry; apply map.get_remove_diff; exact (not_eq_sym Hne))
  | Hne: ?k <> ?k' |- context [ map.get (map.remove ?c ?k) ?k' ] =>
        replace (map.get (map.remove c k) k') with (map.get c k') by
        (symmetry; apply map.get_remove_diff; exact (not_eq_sym Hne))
  | Hne: ?k' <> ?k, H: context [ map.get (map.remove ?c ?k) ?k' ] |- _ =>
        replace (map.get (map.remove c k) k') with (map.get c k') in H by
        (symmetry; apply map.get_remove_diff; exact Hne)
  | Hne: ?k' <> ?k |- context [ map.get (map.remove ?c ?k) ?k' ] =>
        replace (map.get (map.remove c k) k') with (map.get c k') by
        (symmetry; apply map.get_remove_diff; exact Hne)

  | H: map.get ?c ?k <> None |- ?c <> map.empty => apply (map_get_nnone_nonempty c k H)

  | |- map.singleton _ _ <> map.empty => apply map_singleton_nonempty
  end.

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => bit_at_step
  | |- _ => pfx_step
  | |- _ => small_map_basic_op_simpl_step
  | |- _ => map_step
  end.

Lemma map_extends_remove_in_both : forall (cbig csmall: word_map) k,
  map.extends cbig csmall -> map.extends (map.remove cbig k) (map.remove csmall k).
Proof.
  unfold map.extends. intros. eq_neq_cases k x.
  - subst. rewrite map.get_remove_same in *. discriminate.
  - rewrite map.get_remove_diff in *. auto. congruence. congruence.
Qed.

Lemma map_extends_remove : forall (c: word_map) k,
  map.extends c (map.remove c k).
Proof.
  unfold map.extends. intros. eq_neq_cases k x; subst; steps.
Qed.

Lemma map_nonempty_exists_key : forall (c: word_map),
  c <> map.empty -> exists k, map.get c k <> None.
Proof.
  intros. exists (map.fold (fun _ k _ => k) /[0] c).
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => m <> map.empty -> map.get m state <> None)
         (m:=c) (r0:=/[0]) (f:=fun _ k _ => k); steps.
  auto.
Qed.

Lemma map_empty_eq : forall c: word_map,
   c = map.empty <-> map.fold (fun _ _ _ => true) false c = false.
Proof.
  intros. split.
  - intros. subst. apply map.fold_empty.
  - apply map.fold_spec; steps.
Qed.

Lemma map_eq_empty_dec : forall (c1: word_map), c1 = map.empty \/ c1 <> map.empty.
Proof.
  intros. rewrite map_empty_eq.
  match goal with
  | |- context [ ?E = false ] => destruct E
  end; steps.
Qed.

Lemma map_remove_get_nnone : forall (c: word_map) k k',
  map.get (map.remove c k) k' <> None -> map.get c k' <> None.
Proof.
  intros. eapply map_extends_get_nnone. 2: eassumption. apply map_extends_remove.
Qed.

(* END MAPS *)
(* BEGIN CUSTOM MAP OPS *)

Definition pfx'_mmeet (c: word_map) :=
  map.fold (fun state k v => match state with
                             | Some p => Some (pfx_meet (pfx_emb k) p)
                             | None => Some (pfx_emb k)
                             end) None c.

Definition pfx_mmeet (c: word_map) :=
  match pfx'_mmeet c with
  | Some p => p
  | None => pfx_nil
  end.

Lemma pfx_mmeet_singleton : forall (k v: word),
  pfx_mmeet (map.singleton k v) = pfx_emb k.
Proof.
  intros. unfold pfx_mmeet, map.singleton, pfx'_mmeet.
  rewrite map.fold_singleton. reflexivity.
Qed.

Lemma pfx_mmeet_len : forall c, pfx_len (pfx_mmeet c) <= 32.
Proof.
  intros. unfold pfx_mmeet, pfx'_mmeet.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun _ state => state = None \/ exists p, state = Some p /\ pfx_len p <= 32).
  3: (destruct HP as [ HP | HP ]; [ rewrite HP | ]).
  left. steps. steps. right. destruct_or. all: steps.
Qed.

Lemma pfx_mmeet_len_unsigned_word : forall c,
  \[/[pfx_len (pfx_mmeet c)]] = pfx_len (pfx_mmeet c).
Proof.
  intros. apply word.unsigned_of_Z_nowrap.
  pose proof (pfx_mmeet_len c).
  pose proof (pfx_len_nneg (pfx_mmeet c)).
  lia.
Qed.

Definition map_filter (c: word_map) (f: word -> bool) :=
  map.fold (fun state k v => if f k then map.put state k v else state)
           map.empty
           c.

Lemma map_filter_get : forall c f k,
  map.get (map_filter c f) k = if f k then map.get c k else None.
Proof.
  intros. unfold map_filter. apply map.fold_spec; steps.
  destruct (f k0) eqn:E; destruct (f k) eqn:E2; eq_neq_cases k k0; subst; steps;
  congruence.
Qed.

Definition half_subcontent c b :=
  map_filter c (fun k => Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b).

Lemma map_filter_extends : forall c f,
  map.extends c (map_filter c f).
Proof.
  unfold map.extends. intros. rewrite map_filter_get in *. destruct (f x); congruence.
Qed.

Lemma half_subcontent_extends : forall c b,
  map.extends c (half_subcontent c b).
Proof.
  intros. apply map_filter_extends.
Qed.

Lemma half_subcontent_get : forall c b k,
  map.get (half_subcontent c b) k = if Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b
                                    then map.get c k
                                    else None.
Proof.
  intros. unfold half_subcontent. apply map_filter_get.
Qed.

Lemma half_subcontent_get_nNone : forall c k,
  map.get c k <> None ->
  map.get (half_subcontent c (bit_at k (pfx_len (pfx_mmeet c)))) k <> None.
Proof.
  intros. rewrite half_subcontent_get. steps.
Qed.

Lemma pfx_mmeet_key_le : forall c k,
  map.get c k <> None -> pfx_le (pfx_mmeet c) (pfx_emb k).
Proof.
  intros. unfold pfx_mmeet, pfx'_mmeet.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => map.get m k <> None ->
                   exists p, state = Some p /\ pfx_le p (pfx_emb k)) (m:=c).
  3: (steps; match goal with | H: map.fold _ _ _ = _ |- _ => rewrite H end; steps).
  steps. intros. steps.
  instantiate (1:=match r with
                  | Some p => pfx_meet (pfx_emb k0) p
                  | None => pfx_emb k0
                  end). destruct r; steps.
  eq_neq_cases k k0.
  - subst. destruct r; steps.
  - steps. apply pfx_le_trans with p; steps.
Qed.

Lemma pfx_mmeet_empty : pfx_mmeet map.empty = pfx_nil.
Proof.
  unfold pfx_mmeet, pfx'_mmeet. rewrite map.fold_empty. steps.
Qed.

Lemma pfx'_mmeet_nonempty : forall c, c <> map.empty -> pfx'_mmeet c <> None.
Proof.
  intros. unfold pfx'_mmeet.
  eenough (Himp: c <> map.empty -> _) by (apply Himp; assumption).
  apply map.fold_spec; steps.
  destruct r; steps.
Qed.

Lemma pfx_mmeet_put_new : forall c k v,
  c <> map.empty -> map.get c k = None ->
  pfx_mmeet (map.put c k v) = pfx_meet (pfx_emb k) (pfx_mmeet c).
Proof.
  intros. unfold pfx_mmeet, pfx'_mmeet. rewrite map.fold_put.
  match goal with
  | |- context [ map.fold ?f ?r0 ?c ]  => remember (map.fold f r0 c) as cm
  end.
  { destruct cm.
    - steps.
    - symmetry in Heqcm. apply pfx'_mmeet_nonempty in Heqcm; steps. }
  steps.
  { destruct r.
    - do 2 rewrite <- pfx_meet_assoc. do 2 f_equal. apply pfx_meet_comm.
    - steps. apply pfx_meet_comm. }
  steps.
Qed.

Lemma pfx_mmeet_put_old : forall c k v,
  map.get c k <> None -> pfx_mmeet (map.put c k v) = pfx_mmeet c.
Proof.
  intros.
  replace (map.put c k v) with (map.put (map.remove c k) k v)
    by (apply map.put_remove_same).
  destruct (map.get c k) eqn:E; steps.
  replace c with (map.put (map.remove c k) k r) at 2
    by (rewrite map.put_remove_same; apply map.put_idemp; assumption).
  pose proof (map_eq_empty_dec (map.remove c k)) as Hemp.
  destruct Hemp as [ Hemp | Hemp ].
    - rewrite Hemp. steps. do 2 rewrite pfx_mmeet_singleton. steps.
    - repeat rewrite pfx_mmeet_put_new; steps. all: apply map.get_remove_same.
Qed.

Ltac custom_map_ops_pre_step :=
  match goal with
  | H: map.get ?c ?k <> None |- pfx_le (pfx_mmeet ?c) (pfx_emb ?k) =>
       exact (pfx_mmeet_key_le c k H)
  | H: map.get ?c ?k = Some _ |- pfx_le (pfx_mmeet ?c) (pfx_emb ?k) =>
       apply (pfx_mmeet_key_le c k)
  | H: context [ pfx_mmeet map.empty ] |- _ => rewrite pfx_mmeet_empty in H
  | |- context [ pfx_mmeet map.empty ] => rewrite pfx_mmeet_empty
  | |- map.extends ?c (half_subcontent ?c _) => apply half_subcontent_extends
  end.

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => bit_at_step
  | |- _ => pfx_step
  | |- _ => small_map_basic_op_simpl_step
  | |- _ => map_step
  | |- _ => custom_map_ops_pre_step
  end.

Lemma pfx_mmeet_put : forall c k v,
  c <> map.empty -> pfx_mmeet (map.put c k v) = pfx_meet (pfx_emb k) (pfx_mmeet c).
Proof.
  intros. destruct (map.get c k) eqn:E.
  - rewrite pfx_mmeet_put_old by steps. steps.
  - apply pfx_mmeet_put_new; steps.
Qed.

Lemma pfx_mmeet_put_has_prefix : forall c k v,
  c <> map.empty -> pfx_le (pfx_mmeet c) (pfx_emb k) ->
  pfx_mmeet (map.put c k v) = pfx_mmeet c.
Proof.
  intros. rewrite pfx_mmeet_put; steps.
Qed.

Lemma half_subcontent_put_excl_key : forall c k v b,
  pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) < pfx_len (pfx_mmeet c) ->
  bit_at k (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c))) = b ->
  half_subcontent (map.put c k v) b = map.singleton k v.
Proof.
  intros. assert (c <> map.empty). { intro. steps. }
  apply map.map_ext. intros. rewrite half_subcontent_get. subst.
  rewrite pfx_mmeet_put by assumption. eq_neq_cases k k0.
  - subst. steps.
  - steps. destruct (map.get c k0) eqn:E; steps.
    replace (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)))
        with (pfx_len (pfx_meet (pfx_emb k) (pfx_emb k0))).
    pose proof (pfx_meet_emb_bit_at_len k k0). steps.
    assert (map.get c k0 <> None) by steps.
    assert (pfx_le (pfx_mmeet c) (pfx_emb k0)) by steps.
    eassert _. {
    eapply (pfx_lele_tot (pfx_mmeet c) (pfx_meet (pfx_emb k) (pfx_emb k0)) (pfx_emb k0));
     steps. } destruct_or.
    + exfalso. eassert _. { eapply pfx_meet_le_meet_l with (p:=pfx_mmeet c).
      match goal with
      | H: pfx_le _ (pfx_meet _ _) |- _ => exact H
      end. }
      rewrite pfx_meet_assoc in *. steps.
      match goal with
      | H: pfx_le _(pfx_meet _ (pfx_mmeet c)) |- _ => apply pfx_le_len in H
      end. lia.
    + f_equal. apply pfx_le_asym.
      * apply pfx_meet_le_both; steps.
      * apply pfx_meet_le_meet_r. steps.
Qed.

Lemma half_subcontent_put_excl_bulk : forall c k v b,
  pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) < pfx_len (pfx_mmeet c) ->
  bit_at k (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c))) = negb b ->
  half_subcontent (map.put c k v) b = c.
Proof.
  intros. assert (c <> map.empty). { intro. steps. }
  apply map.map_ext. intros. rewrite half_subcontent_get.
  rewrite pfx_mmeet_put by assumption. eq_neq_cases k k0.
  - subst.
    match goal with
    | H: context [ _ = negb _ ] |- _ => rewrite H
    end.
    steps. symmetry. apply eq_None_by_false. intro.
    match goal with
    | H: _ < _ |- _ => rewrite pfx_meet_le_eq' in H
    end; steps.
  - steps. destruct (map.get c k0) eqn:E; steps.
    eassert _. { apply pfx_mmeet_key_le. rewrite E. steps. }
    assert (pfx_le (pfx_meet (pfx_emb k) (pfx_emb k0)) (pfx_mmeet c)). {
      eassert _. {
        eapply (pfx_lele_tot (pfx_mmeet c)
                 (pfx_meet (pfx_emb k) (pfx_emb k0))
                 (pfx_emb k0)); steps. }
      destruct_or; [ exfalso | assumption ].
      assert (pfx_le (pfx_mmeet c) (pfx_emb k)). {
        eapply pfx_le_trans. 2: apply pfx_meet_le_l. eassumption. }
      assert (Hmeq: pfx_meet (pfx_emb k) (pfx_mmeet c) = pfx_mmeet c) by steps.
      rewrite Hmeq in *. steps. }
    assert (Hmmeq:
     pfx_meet (pfx_emb k) (pfx_mmeet c) = pfx_meet (pfx_emb k) (pfx_emb k0)). {
      apply pfx_le_asym; apply pfx_meet_le_both; steps.
      apply pfx_le_trans with (pfx_mmeet c); steps. }
    rewrite Hmmeq in *.
    eassert (Hbitneq: _). { apply (pfx_meet_emb_bit_at_len k k0). assumption. }
    apply not_eq_sym in Hbitneq. apply Bool_neq_eq_negb in Hbitneq.
    rewrite Hbitneq in *.
    match goal with
    | H: bit_at _ _ = negb b |- _ => rewrite H in *
    end. steps.
Qed.

Lemma half_subcontent_put_has_prefix : forall c k v b,
  c <> map.empty ->
  pfx_le (pfx_mmeet c) (pfx_emb k) ->
  half_subcontent (map.put c k v) b =
    if Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b then
       map.put (half_subcontent c b) k v
    else
       half_subcontent c b.
Proof.
  intros. apply map.map_ext. intros. rewrite half_subcontent_get.
  rewrite pfx_mmeet_put_has_prefix by assumption.
  destruct (Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b) eqn:E;
  eq_neq_cases k k0; subst; steps; rewrite half_subcontent_get; steps.
Qed.

Lemma half_subcontent_put_update : forall c k v b,
  map.get c k <> None ->
  half_subcontent (map.put c k v) b =
    if Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b then
       map.put (half_subcontent c b) k v
    else
       half_subcontent c b.
Proof.
  intros. apply half_subcontent_put_has_prefix; steps.
Qed.

Lemma half_subcontent_in_bit : forall c k b,
  map.get (half_subcontent c b) k <> None -> bit_at k (pfx_len (pfx_mmeet c)) = b.
Proof.
  intros. rewrite half_subcontent_get in *. steps.
Qed.

Definition map_some_key (c: word_map) default := map.fold (fun _ k _ => k) default c.

Lemma map_some_key_singleton : forall k v k', map_some_key (map.singleton k v) k' = k.
Proof.
  intros. unfold map_some_key, map.singleton. apply map.fold_singleton.
Qed.

Lemma pfx_mmeet_all_le : forall c p,
  c <> map.empty ->
  (forall k, map.get c k <> None -> pfx_le p (pfx_emb k)) -> (pfx_le p (pfx_mmeet c)).
Proof.
  intros.
  unfold pfx_mmeet, pfx'_mmeet.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state =>
      (forall p',
        (forall k, map.get m k <> None -> pfx_le p' (pfx_emb k)) ->
        match state with
        | Some p0 => pfx_le p' p0
        | None => m = map.empty
        end)) (m:=c) (r0:=None). steps.
  2:
  match goal with
  | |- context [ map.fold ?af ] => instantiate (1:=af) in HP
  end.
  intros. cbv beta.
  match goal with
  | H1: forall _, (_ <> None) -> _,
    H2: forall _, (forall _, (_ <> None) -> _) -> _ |- _ =>
      rename H1 into CH; rename H2 into IH
  end.
  destruct r eqn:E. apply pfx_meet_le_both. apply CH. steps. apply IH. steps. apply CH.
  eq_neq_cases k k0; steps. apply CH. steps.
  eassert (HP2: _). { apply (HP p). assumption. } clear HP.
  match goal with
  | |- context [ map.fold ?f ?r0 ?m ] => destruct (map.fold f r0 m) eqn:E
  end; steps.
Qed.

Lemma pfx_mmeet_remove_le : forall c k,
  map.remove c k <> map.empty ->
  pfx_le (pfx_mmeet c) (pfx_mmeet (map.remove c k)).
Proof.
  intros. apply pfx_mmeet_all_le; steps. eq_neq_cases k k0; subst; steps.
Qed.

Lemma pfx_mmeet_nonsingle_len : forall (c: word_map) k0 k1,
  map.get c k0 <> None -> map.get c k1 <> None -> k0 <> k1 -> pfx_len (pfx_mmeet c) < 32.
Proof.
  intros.
  enough (pfx_len (pfx_mmeet c) <= pfx_len (pfx_meet (pfx_emb k0) (pfx_emb k1)) < 32)
  by lia. split. apply pfx_le_len. apply pfx_meet_le_both; steps. steps.
Qed.

Lemma half_subcontent_empty : forall (c: word_map) b k0 k1,
  half_subcontent c b = map.empty -> map.get c k0 <> None -> map.get c k1 <> None ->
  k0 = k1.
Proof.
  intros. eq_neq_cases k0 k1; [ assumption | exfalso ].
  eassert _ by (apply (pfx_mmeet_nonsingle_len c k0 k1); assumption).
  assert (Hcontr: pfx_le (pfx_snoc (pfx_mmeet c) (negb b)) (pfx_mmeet c)). {
    apply pfx_mmeet_all_le. steps. steps. apply pfx_snoc_ext_le. steps.
    rewrite pfx_emb_spec; [ steps | pose proof (pfx_len_nneg (pfx_mmeet c)); lia ].
    match goal with
    | H: half_subcontent _ _ = map.empty |- _ =>
         f_apply (fun m: word_map => map.get m k) H; rewrite half_subcontent_get in H
    end.
    steps. destruct (Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b) eqn:E; steps.
    apply Bool_neq_eq_negb in E. steps. }
  apply pfx_snoc_le_self in Hcontr. steps.
Qed.

Lemma pfx_mmeet_remove_unchanged : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  pfx_mmeet (map.remove c k) = pfx_mmeet c.
Proof.
  intros.
  destruct (map.get c k) eqn:E.
  1: assert (E': map.get c k <> None) by steps; clear E.
  2: rewrite map.remove_not_in by assumption; steps.
  apply pfx_le_asym.
  - enough (pfx_le (pfx_mmeet (map.remove c k)) (pfx_emb k)).
    + apply pfx_mmeet_all_le. steps. intros. eq_neq_cases k k0; subst; steps.
      apply pfx_mmeet_key_le. steps.
    + destruct (map_eq_empty_dec (half_subcontent c (negb b))).
      * match goal with
        | H: _ <> map.empty |- _ => apply map_nonempty_exists_key in H
        end. fwd. eq_neq_cases k k0; subst; steps. assert (map.get c k0 <> None).
        eapply map_extends_get_nnone. 2: eassumption. steps.
        exfalso. eauto using half_subcontent_empty.
      * do 2 match goal with
           | H: _ <> map.empty |- _ => apply map_nonempty_exists_key in H
           end.
        fwd. apply pfx_le_trans with (pfx_meet (pfx_emb k0) (pfx_emb k1)).
        apply pfx_meet_le_both; apply pfx_mmeet_key_le. assert (k <> k0). {
        assert (bit_at k0 (pfx_len (pfx_mmeet c)) = negb b).
        rewrite half_subcontent_get in *. steps.
        intro. subst. steps. }
      steps. eapply map_extends_get_nnone. 2: eassumption. steps.
      eapply map_extends_get_nnone. 2: eassumption.
      apply map_extends_remove_in_both. steps.
      apply pfx_le_trans with (pfx_mmeet c). 2: steps.
      apply pfx_lele_len_ord with (pfx_emb k0); steps. apply pfx_mmeet_key_le.
      eapply map_extends_get_nnone. 2: eassumption. steps.
      match goal with
      | H: context [ map.remove ] |- _ => apply map_remove_get_nnone in H
      end.
      do 2 match goal with
           | H: map.get (half_subcontent _ _) _ <> None |- _ =>
                rewrite half_subcontent_get in H
           end. steps.
      purge k. subst.
      assert (0 <= pfx_len (pfx_mmeet c) < 32). {
        eassert _. { apply (pfx_mmeet_nonsingle_len c k0 k1); steps.
          intro. subst. steps. }
        pose proof (pfx_len_nneg (pfx_mmeet c)). lia. }
      eapply pfx_meet_bit_diff_len. lia.
      1-2: reflexivity.
      match goal with
      | H: _ = negb _ |- _ => rewrite H
      end.
      apply Bool.no_fixpoint_negb.
  - apply pfx_mmeet_remove_le. eapply map_extends_nonempty. 2: eassumption.
    apply map_extends_remove_in_both. apply half_subcontent_extends.
Qed.

Lemma half_subcontent_remove_same : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  half_subcontent (map.remove c k) b = map.remove (half_subcontent c b) k.
Proof.
  intros. apply map.map_ext. intros. eq_neq_cases k k0.
  - subst. steps. apply eq_None_by_false. intro Hnn.
    eapply map_extends_get_nnone in Hnn. 2: apply half_subcontent_extends. steps.
  - steps. do 2 rewrite half_subcontent_get. steps.
    rewrite pfx_mmeet_remove_unchanged with (b:=b); steps.
Qed.

Lemma half_subcontent_remove_other : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  half_subcontent (map.remove c k) (negb b) = half_subcontent c (negb b).
Proof.
  intros. apply map.map_ext. intros. do 2 rewrite half_subcontent_get.
  rewrite pfx_mmeet_remove_unchanged with (b:=b) by steps.
  eq_neq_cases k k0; subst; steps.
Qed.

Lemma half_subcontent_removed_half_leaf : forall c k v b,
  half_subcontent c b = map.singleton k v ->
  half_subcontent c (negb b) = map.remove c k.
Proof.
  intros. apply map.map_ext. intros. rewrite half_subcontent_get.
  match goal with
  | |- context [ if ?cond then _ else _ ] => destruct cond eqn:E
  end; steps.
  - assert (bit_at k (pfx_len (pfx_mmeet c)) = b). {
      match goal with
      | H: half_subcontent _ _ = map.singleton _ _ |- _ =>
           f_apply (fun m: word_map => map.get m k) H
      end.
      steps. rewrite half_subcontent_get in *. steps. }
    assert (k <> k0) by (intro; subst; steps). steps.
  - match goal with
    | H: half_subcontent _ _ = map.singleton _ _ |- _ =>
         f_apply (fun m: word_map => map.get m k0) H
    end.
    eq_neq_cases k k0; subst; steps.
    rewrite half_subcontent_get in *. steps.
Qed.

Lemma half_subcontent_get_nnone : forall c b k,
  map.get (half_subcontent c b) k <> None -> map.get c k <> None.
Proof.
  intros. eapply map_extends_get_nnone. eapply half_subcontent_extends. eassumption.
Qed.

Ltac custom_map_ops_step :=
  match goal with
  | H: context [ pfx_mmeet (map.singleton _ _) ] |- _ => rewrite pfx_mmeet_singleton in H
  | |- context [ pfx_mmeet (map.singleton _ _) ] => rewrite pfx_mmeet_singleton
  | H: context [ \[/[ pfx_len (pfx_mmeet _) ]] ] |- _ =>
      rewrite pfx_mmeet_len_unsigned_word in H
  | |- context [ \[/[ pfx_len (pfx_mmeet _) ]] ] =>
      rewrite pfx_mmeet_len_unsigned_word


  | Hinsub: map.get (half_subcontent ?c ?b) ?k <> None |- map.get ?c ?k <> None =>
      apply (half_subcontent_get_nnone c b k Hinsub)

  | Hin: map.get ?c ?k <> None, Hbit: bit_at ?k (pfx_len (pfx_mmeet ?c)) = ?b1
    |- context [ half_subcontent (map.put ?c ?k ?v) ?b2 ] =>
      rewrite (half_subcontent_put_update c k v b2) by (exact Hin); rewrite Hbit

  | Hin: map.get ?c ?k <> None |- context [ pfx_mmeet (map.put ?c ?k ?v) ] =>
      rewrite (pfx_mmeet_put_old c k v) by (exact Hin)


  | Hbit: bit_at ?k (pfx_len (pfx_mmeet ?c)) = ?b
    |- context [ map.get (half_subcontent ?c ?b) ?k ] =>
      rewrite (half_subcontent_get c b k); rewrite Hbit

  end.

(* END CUSTOM MAP OPS *)
(* BEGIN CBT STRUCTURES *)

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => bit_at_step
  | |- _ => pfx_step
  | |- _ => small_map_basic_op_simpl_step
  | |- _ => map_step
  | |- _ => custom_map_ops_pre_step
  | |- _ => custom_map_ops_step
  end.

Inductive tree_skeleton: Set :=
| Leaf
| Node (skL skR: tree_skeleton).

Definition tree_skeleton_lt(sk1 sk2: tree_skeleton): Prop :=
  match sk2 with
  | Node treeL treeR  => sk1 = treeL \/ sk1 = treeR
  | Leaf => False
  end.

Lemma tree_skeleton_lt_wf: well_founded tree_skeleton_lt.
Proof.
  unfold well_founded. intros sk2.
  induction sk2; eapply Acc_intro; intros sk1 Lt; unfold tree_skeleton_lt in Lt.
  - contradiction.
  - destruct Lt; subst; assumption.
Qed.

#[local] Hint Resolve tree_skeleton_lt_wf: wf_of_type.

Lemma tree_skeleton_lt_l: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk1 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

Lemma tree_skeleton_lt_r: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk2 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

#[local] Hint Resolve tree_skeleton_lt_l tree_skeleton_lt_r : safe_implication.

Fixpoint acbt tree c: Prop :=
  match tree with
  | Leaf => exists k v, c = map.singleton k v
  | Node treeL treeR =>
     acbt treeL (half_subcontent c false) /\
     acbt treeR (half_subcontent c true)
  end.

Context {consts: malloc_constants}.

Fixpoint cbt' (tree: tree_skeleton) (c: word_map) (a: word): mem -> Prop :=
  match tree with
  | Leaf => EX k v,
        <{ * emp (a <> /[0])
           * freeable 12 a
           * <{ + uintptr /[32]
                + uintptr k
                + uintptr v }> a
           * emp (c = map.singleton k v) }>
  | Node treeL treeR => EX (aL: word) (aR: word),
          <{ * emp (a <> /[0])
             * freeable 12 a
             * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                  + uintptr aL
                  + uintptr aR }> a
             * cbt' treeL (half_subcontent c false) aL
             * cbt' treeR (half_subcontent c true) aR }>
  end.

Definition nncbt (c: word_map) (a: word): mem -> Prop := EX tree, cbt' tree c a.

(* in full generality, a CBT can be represented as a pointer which is either
   - NULL for an empty CBT, or
   - pointing to the CBT root node *)
Definition cbt (c: word_map) (a: word): mem -> Prop :=
  if \[a] =? 0 then emp (c = map.empty) else nncbt c a.

Ltac to_with_mem_hyps := repeat
  match goal with
  | H: ?P ?m |- _ => match type of m with
                   | _ mem => change (m |= P) in H
                   end
  end.

Lemma to_with_mem : forall (P : mem -> Prop) (m : mem), P m -> with_mem m P.
Proof.
  auto.
Qed.

Ltac hyps_to_with_mem := repeat match goal with
  | H: ?P ?m |- _ => apply to_with_mem in H
  end.

Ltac add_dummy_mem_def_hyp m := assert (mmap.Def m = mmap.Def m) by reflexivity.

Ltac destruct_array_0 H :=
  unfold anyval in H; destruct H as [? H]; apply array_0_is_emp in H; [ | reflexivity ];
  unfold emp in H; destruct H.

Ltac clear_array_0 := match goal with
  | H: ?m |= array _ 0 ? _ |- _ => move H at bottom; unfold anyval in H;
                                   let arlen := fresh "arlen" in
                                   let Ha := fresh "Ha" in destruct H as [arlen Ha];
                                   apply array_0_is_emp in Ha; [ | trivial ];
                                   unfold emp in Ha; fwd; subst m
end.

Lemma acbt_nonempty : forall tree c,
  acbt tree c -> c <> map.empty.
Proof.
  induction tree; steps; simpl acbt in *; steps.
  match goal with
  | IH: forall _, acbt ?sk _ -> _ <> map.empty, CH: acbt ?sk _ |- _ => apply IH in CH
  end.
  eapply map_extends_nonempty. 2: eassumption. steps.
Qed.

Lemma acbt_prefix_length : forall (tree: tree_skeleton) (c: word_map),
    acbt tree c -> match tree with
                   | Node _ _ => pfx_len (pfx_mmeet c) < 32
                   | Leaf => pfx_len (pfx_mmeet c) = 32
                   end.
Proof.
  intros. destruct tree; simpl acbt in *; steps.
  do 2 match goal with
       | H: acbt ?sk ?c |- _ => apply acbt_nonempty in H;
                                apply map_nonempty_exists_key in H
       end.
  steps. rewrite half_subcontent_get in *. steps.
  assert (k <> k0) by (intro; subst; congruence).
  eapply pfx_mmeet_nonsingle_len; [ | | eassumption ]; eassumption.
Qed.

Lemma purify_cbt' :
  forall tree c a, purify (cbt' tree c a) (a <> /[0] /\ acbt tree c).
Proof.
  unfold purify. induction tree.
  - unfold cbt', acbt. steps. instantiate (2:=k). instantiate (1:=v). steps.
  - simpl cbt'. simpl acbt. steps;
    match goal with
    | H1: _ |= cbt' ?tree _ _,
      H2: forall _ _ _, cbt' ?tree _ _ _ -> _
      |- context[ ?tree ] => apply H2 in H1
    end; tauto.
Qed.


Lemma cbt_expose_fields (tree: tree_skeleton) (c: word_map) (a: word):
  iff1 (cbt' tree c a) (EX w2 w3,
    <{ * freeable 12 a
       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
            + uintptr w2
            + uintptr w3 }> a
       * emp (a <> /[0])
       * match tree with
         | Leaf => emp (c = map.singleton w2 w3)
         | Node treeL treeR =>
                   <{ * cbt' treeL (half_subcontent c false) w2
                      * cbt' treeR (half_subcontent c true) w3 }>
         end }>).
Proof.
  unfold iff1. intro m.
  split; intros; destruct tree; simpl cbt' in *; steps.
Qed.

Fixpoint cbt_best_lookup tree c k :=
  match tree with
  | Node treeL treeR => if bit_at k (pfx_len (pfx_mmeet c))
                        then cbt_best_lookup treeR (half_subcontent c true) k
                        else cbt_best_lookup treeL (half_subcontent c false) k
  | Leaf => map_some_key c k
  end.

Lemma cbt_best_lookup_in : forall tree c k,
  acbt tree c -> map.get c (cbt_best_lookup tree c k) <> None.
Proof.
  induction tree.
  - steps. simpl in *. steps. subst. steps. rewrite map_some_key_singleton. steps.
  - steps. simpl in *. steps. destruct (bit_at k (pfx_len (pfx_mmeet c))) eqn:E;
    (eapply map_extends_get_nnone; [ eapply half_subcontent_extends | eauto ]).
Qed.

Lemma cbt_best_lookup_subcontent_in_parent : forall tree c k k' b,
  acbt tree (half_subcontent c b) ->
  cbt_best_lookup tree (half_subcontent c b) k' = k ->
  map.get c k <> None.
Proof.
  intros. subst k. apply cbt_best_lookup_in with (k:=k') in H. steps.
Qed.

Lemma node_prefix_length : forall sk1 sk2 c,
  acbt (Node sk1 sk2) c -> 0 <= pfx_len (pfx_mmeet c) < 32.
Proof.
  steps. apply acbt_prefix_length in H. pose proof (pfx_len_nneg (pfx_mmeet c)). lia.
Qed.

Lemma node_prefix_length_word_not_32 : forall sk1 sk2 c,
  acbt (Node sk1 sk2) c -> /[pfx_len (pfx_mmeet c)] <> /[32].
Proof.
  steps. apply node_prefix_length in H. hwlia.
Qed.

Ltac cbt_step :=
  match goal with
  | H: acbt (Node _ _) ?c |- 0 <= pfx_len (pfx_mmeet ?c) < 32 =>
    apply node_prefix_length in H
  | Hacbt: acbt ?sk (half_subcontent ?c ?b),
    Hlkup: cbt_best_lookup ?t (half_subcontent ?c ?b) ?k' = ?k
    |- map.get ?c ?k <> None =>
    apply (cbt_best_lookup_subcontent_in_parent t c k k' b Hacbt Hlkup)
  | Hacbt: acbt (Node _ _) ?c, Hpl: /[pfx_len (pfx_mmeet ?c)] = /[32] |- _ =>
    destruct (node_prefix_length_word_not_32 _ _ _ Hacbt Hpl)
  | |- impl1 (cbt' ?sk ?c1 ?a) (cbt' ?sk ?c2 ?a) => replace c2 with c1; [ reflexivity | ]
  | Hacbt: acbt ?sk ?c |- ?c <> map.empty => exact (acbt_nonempty sk c Hacbt)
  | Hacbt: acbt ?sk ?c |- map.get ?c (cbt_best_lookup ?sk ?c ?k) <> None =>
    exact (cbt_best_lookup_in sk c k Hacbt)

  | Hacbt: acbt _ ?c,
    Hpr: pfx_le (pfx_mmeet ?c) (pfx_emb ?k)
    |- context [ pfx_mmeet (map.put ?c ?k ?v) ] =>
      rewrite (pfx_mmeet_put_has_prefix c k v (acbt_nonempty _ _ Hacbt) Hpr)

  | Hacbt: acbt _ ?c,
    Hpfxle: pfx_le (pfx_mmeet ?c) (pfx_emb ?k),
    Hbit: bit_at ?k (pfx_len (pfx_mmeet ?c)) = ?b1
    |- context [ half_subcontent (map.put ?c ?k ?v) ?b2 ] =>
      is_constructor b1; is_constructor b2;
      rewrite (half_subcontent_put_has_prefix c k v b2 (acbt_nonempty _ _ Hacbt) Hpfxle);
      rewrite Hbit
  end.

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => bit_at_step
  | |- _ => pfx_step
  | |- _ => small_map_basic_op_simpl_step
  | |- _ => map_step
  | |- _ => custom_map_ops_pre_step
  | |- _ => custom_map_ops_step
  | |- _ => cbt_step
  end.

Lemma cbt_best_lookup_cb_not_node : forall sk c k,
  acbt sk c -> pfx_len (pfx_mmeet c) < 32 -> pfx_le (pfx_mmeet c) (pfx_emb k) ->
  pfx_len (pfx_mmeet c) <
    pfx_len (pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))).
Proof.
  intros. destruct sk.
  - simpl acbt in *. steps.
  - match goal with | |- pfx_len ?lhs < pfx_len ?rhs => assert (pfx_le lhs rhs) end.
    { apply pfx_meet_le_both; steps. apply pfx_mmeet_key_le. steps. }
    match goal with
    | |- _ < pfx_len ?rhs =>
      assert (Hlp: pfx_le (pfx_snoc (pfx_mmeet c) (bit_at k (pfx_len (pfx_mmeet c)))) rhs)
    end.
    { apply pfx_meet_le_both; apply pfx_snoc_ext_le; steps.
      - apply pfx_emb_spec. steps.
      - eapply proj2. apply pfx_meet_spec. eassumption.
      - rewrite pfx_emb_spec; steps. simpl cbt_best_lookup in *. simpl acbt in *. steps.
        destruct (bit_at k (pfx_len (pfx_mmeet c)));
        apply half_subcontent_in_bit; steps. }
    apply pfx_le_len in Hlp. rewrite pfx_snoc_len in Hlp. lia.
Qed.

(* END CBT STRUCTURES *)
(* BEGIN FRAMEWORK SETUP *)

#[local] Hint Extern 1 (cannot_purify (cbt' _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (cbt' _ _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (cbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (wand _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (nncbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (or1 _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (sep _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (uint _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify _)
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (or1 _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (nncbt _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (sep allocator))
      => constructor : suppressed_warnings.

#[local] Hint Unfold cbt : heapletwise_always_unfold.
#[local] Hint Unfold nncbt : heapletwise_always_unfold.

Hint Resolve purify_cbt' : purify.

Local Hint Extern 1 (PredicateSize (cbt' ?sk)) => exact 12 : typeclass_instances.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | cbt' ?sk2 ?c2 =>
      lazymatch hypPred with
      | cbt' ?sk1 ?c1 =>
          (* Note: address has already been checked, and if sk and/or s don't
             unify, sidecondition solving steps will make them match later,
             so here, we just need to take care of instantiating evars from conclPred *)
          try syntactic_unify_only_inst_r c1 c2;
          try syntactic_unify_only_inst_r sk1 sk2
      end
  end.

Ltac provide_new_ghosts_hook ::= manual_new_ghosts.

(* END FRAMEWORK SETUP *)
(* BEGIN CBT NODE MEM IMPL *)

#[export] Instance spec_of_cbt_raw_node_alloc: fnspec :=                        .**/

uintptr_t cbt_raw_node_alloc(uintptr_t w1, uintptr_t w2, uintptr_t w3) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     allocator_failed_below 12
                    else
                     <{ * allocator
                        * freeable 12 res
                        * <{ + uintptr w1
                             + uintptr w2
                             + uintptr w3 }> res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_raw_node_alloc SuchThat (fun_correct! cbt_raw_node_alloc)
  As cbt_raw_node_alloc_ok.                                                     .**/
{                                                                          /**. .**/
  uintptr_t p = Malloc(12);                                                /**. .**/
  if (p == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    store(p, w1);                                                          /**. .**/
    store(p + 4, w2);                                                      /**. .**/
    store(p + 8, w3);                                                      /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /*?.
  repeat clear_array_0. steps. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_raw_node_free: fnspec :=                         .**/

void cbt_raw_node_free(uintptr_t node) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * freeable 12 node
                     * (EX w1 w2 w3, <{ + uintptr w1
                                        + uintptr w2
                                        + uintptr w3 }> node)
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * allocator * R }> m' #**/                 /**.
Derive cbt_raw_node_free SuchThat (fun_correct! cbt_raw_node_free)
  As cbt_raw_node_free_ok.                                                      .**/
{                                                                          /**. .**/
  Free(node);                                                              /*?.
  instantiate (5:=/[12]). steps. .**/
}                                                                          /**.

  (* FIXME: this should probably be done more automatically *)
  unfold impl1. intro m'. steps.
  eapply cast_to_anybytes.
  replace 12 with (4 + (4 + (4 + 0))).
  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w1).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: 4 = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w2).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: 4 = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w3).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: 4 = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_nil_contiguous.

  steps. steps.
Qed.

#[export] Instance spec_of_cbt_raw_node_copy_new: fnspec :=                     .**/

uintptr_t cbt_raw_node_copy_new(uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w1 w2 w3: word);
  requires t m := <{ * allocator
                     * <{ + uintptr w1
                          + uintptr w2
                          + uintptr w3 }> src
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     allocator_failed_below 12
                    else
                     <{ * allocator
                        * freeable 12 res
                        * <{ + uintptr w1
                             + uintptr w2
                             + uintptr w3 }> res }>)
                 * <{ + uintptr w1
                      + uintptr w2
                      + uintptr w3 }> src
                 * R }> m' #**/                                            /**.
Derive cbt_raw_node_copy_new SuchThat (fun_correct! cbt_raw_node_copy_new)
  As cbt_raw_node_copy_new_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = cbt_raw_node_alloc(load(src),
                                   load(src + 4),
                                   load(src + 8));                         /**. .**/
  return p;                                                                /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_raw_node_copy_replace: fnspec :=                 .**/

void cbt_raw_node_copy_replace(uintptr_t dst, uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w1 w2 w3: word);
  requires t m := <{ * <{ + uintptr w1
                          + uintptr w2
                          + uintptr w3 }> src
                     * (EX w1' w2' w3', <{ + uintptr w1'
                                           + uintptr w2'
                                           + uintptr w3' }> dst)
                     * R }> m;
  ensures t' m' := t' = t
           /\ <{ * <{ + uintptr w1
                      + uintptr w2
                      + uintptr w3 }> src
                 * <{ + uintptr w1
                      + uintptr w2
                      + uintptr w3 }> dst
                 * R }> m' #**/                                            /**.
Derive cbt_raw_node_copy_replace SuchThat (fun_correct! cbt_raw_node_copy_replace)
  As cbt_raw_node_copy_replace_ok. .**/
{                                                                          /**. .**/
  store(dst, load(src));                                                   /**. .**/
  store(dst + 4, load(src + 4));                                           /**. .**/
  store(dst + 8, load(src + 8));                                           /**. .**/
}                                                                          /**.
Qed.

(* END CBT NODE MEM IMPL *)
(* BEGIN CBT IMPL *)

#[export] Instance spec_of_cbt_init: fnspec :=                              .**/

uintptr_t cbt_init( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' res := t' = t /\
                       <{ * cbt map.empty res
                          * R }> m' #**/                                   /**.
Derive cbt_init SuchThat (fun_correct! cbt_init) As cbt_init_ok.                .**/
{                                                                          /**. .**/
  return 0;                                                                /**. .**/
}                                                                          /**.
  unfold cbt. to_with_mem_hyps. add_dummy_mem_def_hyp m. steps.
Qed.

#[export] Instance spec_of_cbt_update_or_best: fnspec :=                        .**/

uintptr_t cbt_update_or_best(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (tree: tree_skeleton) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt' tree c tp * R }> m;
  ensures t' m' res := t' = t /\ cbt_best_lookup tree c k = res /\
                <{ * (cbt' tree (if word.eqb res k then map.put c k v else c) tp) * R }> m' #**/     /**.
Derive cbt_update_or_best SuchThat (fun_correct! cbt_update_or_best)
  As cbt_update_or_best_ok. .**/
{                                                                            /**. .**/
  uintptr_t p = tp;                                                          /**.

  (* setting up the loop precondition *)
  rewrite <- Def0 in H0.
  move t before tp.
  rewrite <- Def0. rewrite Def0 at 2.
  delete #(p = ??).
  move tree at bottom.
  move c after Scope1.
  move R after Scope1.
  loop invariant above m.
                                                                                .**/
  while (load(p) != 32) /* initial_ghosts(p, c, R); decreases tree */ {  /*?.
  subst v0.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct tree. { exfalso. steps. }
  rename w2 into aL. rename w3 into aR. .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                             /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c true,
                 <{ * R
                    * freeable 12 p'
                    * cbt' tree1 (half_subcontent c false) aL
                    * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                         + uintptr aL
                         + uintptr p }> p' }>).
  instantiate (1:=tree2). steps. simpl. steps.

  clear Error.
  assert (map.get c retv <> None) by steps.
  destruct (word.eqb retv k) eqn:E; simpl cbt'; steps; subst k; steps. idtac. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c false, <{ * R
                       * freeable 12 p'
                       * cbt' tree2 (half_subcontent c true) aR
                       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                            + uintptr p
                            + uintptr aR }> p' }>).
  instantiate (1:=tree1). steps. simpl. steps.

  clear Error.
  assert (map.get c retv <> None) by steps.
  destruct (word.eqb retv k) eqn:E; simpl cbt'; steps; subst k; steps. .**/
  }                                                                          /**.
  destruct tree; cycle 1. { exfalso. steps. } .**/
    if (load(p + 4) == k) /* split */ {                                      /**. .**/
    store(p + 8, v);                                                        /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  simpl. apply map_some_key_singleton. clear Error. simpl cbt'. steps. .**/
  else {                                                                    /**. .**/
    return load(p + 4);                                                     /**. .**/
  }                                                                         /**.
  simpl. apply map_some_key_singleton. clear Error. simpl cbt'. steps. .**/
}                                                                           /**.
Qed.

#[export] Instance spec_of_cbt_lookup_impl: fnspec :=                           .**/
uintptr_t cbt_lookup_impl(uintptr_t tp, uintptr_t k, uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map)
                (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * cbt' sk c tp
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = /[match map.get c k with | Some _ => 1 | None => 0 end])
                 * cbt' sk c tp
                 * uintptr (match map.get c k with
                            | Some v => v
                            | None => val_out_orig
                            end) val_out
                 * R }> m'         #**/                                     /**.
Derive cbt_lookup_impl SuchThat (fun_correct! cbt_lookup_impl)
  As cbt_lookup_impl_ok.                                                         .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  rewrite <- Def0 in *. rewrite Def0 at 2.
  delete #(p = ??).
  move p after Scope1.
  move R after Scope1.
  move c after Scope1.
  match goal with
  | H: _ |= R |- _ => move H at bottom
  end.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => loop invariant above H
  end.
  move sk at bottom.
  .**/
  while (load(p) != 32) /* initial_ghosts(p,c,R); decreases sk */ {           /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end. steps.
  destruct sk. { exfalso. steps. }
  rename w2 into aL. rename w3 into aR. .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                             /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c true, <{ * R
                       * freeable 12 p'
                       * cbt' sk1 (half_subcontent c false) aL
                       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                            + uintptr aL
                            + uintptr p }> p' }>).
  steps. clear Error. simpl cbt'. steps.
.**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c false, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 (half_subcontent c true) aR
                           * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                                + uintptr p
                                + uintptr aR }> p' }>).
  steps. clear Error. simpl cbt'. steps. .**/
    }                                                                          /**.
  destruct sk; cycle 1. { exfalso. steps. } simpl cbt' in *. .**/
  if (load(p + 4) == k) /* split */ {                                        /**. .**/
    store(val_out, load(p + 8));                                             /**. .**/
    return 1;                                                                /**. .**/
  }                                                                          /**. .**/
  else {                                                                     /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**. .**/
}                                                                            /**.
Qed.

#[export] Instance spec_of_cbt_lookup: fnspec :=                                .**/
uintptr_t cbt_lookup(uintptr_t tp, uintptr_t k, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = /[match map.get c k with | Some _ => 1 | None => 0 end])
                 * cbt c tp
                 * uintptr (match map.get c k with
                            | Some v => v
                            | None => val_out_orig
                            end) val_out
                 * R }> m'         #**/                                     /**.
Derive cbt_lookup SuchThat (fun_correct! cbt_lookup) As cbt_lookup_ok.           .**/
{                                                                           /**. .**/
  if (tp == 0) /* split */ {                                                /**. .**/
    return 0;                                                               /**. .**/
  }                                                                         /**. .**/
  else {                                                                    /**. .**/
    uintptr_t found = cbt_lookup_impl(tp, k, val_out);                      /**. .**/
    return found;                                                           /**. .**/
  }                                                                         /**. .**/
}                                                                           /**.
Qed.

#[export] Instance spec_of_cbt_alloc_leaf: fnspec :=                            .**/

uintptr_t cbt_alloc_leaf(uintptr_t k, uintptr_t v) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     allocator_failed_below 12
                   else
                     <{ * allocator
                        * cbt' Leaf (map.singleton k v) res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_alloc_leaf SuchThat (fun_correct! cbt_alloc_leaf) As cbt_alloc_leaf_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = cbt_raw_node_alloc(32, k, v);                              /**. .**/
  return p;                                                                /**. .**/
}                                                                          /**.
  simpl cbt'. destruct (\[p] =? 0) eqn:E; steps.
Qed.

#[export] Instance spec_of_critical_bit: fnspec :=                              .**/

uintptr_t critical_bit(uintptr_t k1, uintptr_t k2) /**#
  (* heaplet packaging doesn't work well then there's just one item in the heap
     [or I was doing something wrong] *)
  ghost_args := (R1 R2: mem -> Prop);
  requires t m := <{ * R1 * R2 }> m /\ k1 <> k2;
  ensures t' m' res := t = t' /\ <{ * R1 * R2 }> m'
                /\ 0 <= \[res] < 32
                /\ \[res] = pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)) #**/
/**.
Derive critical_bit SuchThat (fun_correct! critical_bit) As critical_bit_ok.    .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.
  prove (0 <= \[i] < 32).
  assert (forall n, 0 <= n < \[i] -> bit_at k1 n = bit_at k2 n).
  intros. hwlia.
  delete #(i = /[0]).
  loop invariant above H.
  move i at bottom. .**/
  while (i < 31 && ((k1 >> i & 1) == ((k2 >> i & 1))))
    /* decreases (32 - \[i]) */ {                                          /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /**.
  assert (Hcmp: n = \[i'] \/ n < \[i']) by lia. destruct Hcmp.
  { subst. steps. }
  { match goal with | H: forall _, _ |- _ => apply H end. lia. } .**/
  return i;                                                                /**. .**/
}                                                                          /**.
  symmetry. apply pfx_cb_charac; steps.
  { unzify. destruct_or. assert (Hui: \[i] = 31) by lia. rewrite Hui in *. intro.
  match goal with
  | H: k1 <> k2 |- _ => apply H
  end.
  apply bit_at_inj. intros. assert (Hcmp: i0 = 31 \/ i0 < 31) by lia. destruct Hcmp.
  { steps. } { match goal with | H: forall _, _ |- _ => apply H end. lia. }
  steps. }
Qed.

#[export] Instance spec_of_cbt_insert_at: fnspec :=                             .**/

uintptr_t cbt_insert_at(uintptr_t tp, uintptr_t cb, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' sk c tp
                     * R }> m
                  /\ 0 <= \[cb] < 32
                  /\ pfx_len
                       (pfx_meet
                         (pfx_emb k)
                         (pfx_emb (cbt_best_lookup sk c k)))
                      = \[cb];
  ensures t' m' res := t' = t
                       /\ if \[res] =? 0 then
                            <{ * allocator_failed_below 12
                               * cbt' sk c tp
                               * R
                               * (fun _ => True) }> m'
                          else
                            (* `id` is a hack to identify this occurrence when
                                rewriting *)
                            res = id tp /\
                            (EX sk',
                              <{ * allocator
                                 * cbt' sk' (map.put c k v) tp
                                 * R }>) m' #**/ /**.
Derive cbt_insert_at SuchThat (fun_correct! cbt_insert_at) As cbt_insert_at_ok.  .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  assert (Htpnn: tp <> /[0]).
  (* would move to the step hook, but purify_cbt' not available there yet *)
  match goal with
  | H: _ |= cbt' _ _ ?tp |- ?tp <> /[0] => apply purify_cbt' in H; tauto
  end.
  move Htpnn after Scope1.
  rewrite <- Def0 in H2.
  move t before tp.
  rewrite <- Def0. rewrite Def0 at 2. replace (id p) with tp.
  delete #(p = ??).
  move sk at bottom.
  move p before Scope1.
  loop invariant above m.
                                                                                .**/
  while (load(p) < cb)
    /* initial_ghosts(p, c, R); decreases sk */
  {                                                                        /*?.
  subst v0.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct sk. { exfalso. steps. }
  .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                            /**. .**/
      p = load(p + 8);                                                      /**. .**/
    }                                                                       /**.
  new_ghosts(p, half_subcontent c true, <{ * R
                           * freeable 12 p'
                           * cbt' sk1 (half_subcontent c false) w2
                           * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                                + uintptr w2
                                + uintptr p }> p' }>).
  remember (cbt_best_lookup (Node sk1 sk2) c k) as k'.
  assert (pfx_le (pfx_mmeet c) (pfx_emb k)).
  { apply pfx_le_trans with (p2:=pfx_meet (pfx_emb k) (pfx_emb k')).
    { apply pfx_lele_len_ord with (pfx_emb k'). apply pfx_mmeet_key_le.
      subst k'. steps. steps. steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *. steps. subst k'. steps.
  instantiate (1:=Node sk1 sk'). simpl cbt'. clear Error. steps. .**/
    else {                                                                    /**. .**/
      p = load(p + 4);                                                        /**. .**/
    }                                                                         /**.
  new_ghosts (p, half_subcontent c false,
      <{ * R
         * freeable 12 p'
         * <{ + uintptr /[pfx_len (pfx_mmeet c)]
              + uintptr p
              + uintptr w3 }> p'
         * cbt' sk2 (half_subcontent c true) w3 }>).
  remember (cbt_best_lookup (Node sk1 sk2) c k) as k'.
  assert (pfx_le (pfx_mmeet c) (pfx_emb k)).
  { apply pfx_le_trans with (p2:=pfx_meet (pfx_emb k) (pfx_emb k')).
    { apply pfx_lele_len_ord with (pfx_emb k'). apply pfx_mmeet_key_le.
      subst k'. steps. steps. steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *. steps. subst k'. steps.
  instantiate (1:=Node sk' sk2). simpl cbt'. clear Error. steps. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == 0) /* split */ {                                           /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**.
  clear Error. destruct sk; simpl cbt' in *; steps. .**/
  else {                                                                     /**. .**/
    uintptr_t new_node = cbt_raw_node_copy_new(p);                           /**. .**/
    if (new_node == 0) /* split */ {                                         /**. .**/
      return 0;                                                              /**. .**/
    }                                                                        /**.
  clear Error. destruct sk; simpl cbt' in *; steps. .**/
    else {                                                                   /**. .**/
      store(p, cb);                                                          /**. .**/
      if (((k >> cb) & 1) == 1) /* split */ {                                /**. .**/
        store(p + 4, new_node);                                              /**. .**/
        store(p + 8, new_leaf);                                              /**. .**/
        return tp;                                                           /**. .**/
      }                                                                      /**.
  clear Error. instantiate (1:=Node sk Leaf). simpl cbt'.
  assert (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) = \[cb]). {
    assert (pfx_meet (pfx_emb k) (pfx_mmeet c)
            = pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))). {
      apply pfx_le_asym. apply pfx_meet_le_meet_r. apply pfx_mmeet_key_le.
      steps. apply pfx_meet_le_both. steps.
      apply pfx_lele_len_ord with (pfx_emb (cbt_best_lookup sk c k)). steps.
      apply pfx_mmeet_key_le. steps. steps.
    }
    congruence.
  }
  assert (\[cb] < pfx_len (pfx_mmeet c)). {
    enough (pfx_len (pfx_mmeet c) <> \[cb]) by lia. intro.
    assert (cb = /[pfx_len (pfx_mmeet c)]) by hwlia. subst cb. steps.
    eassert (pfx_len (pfx_mmeet c) < _). {
      apply cbt_best_lookup_cb_not_node. eassumption. steps.
      instantiate (1:=k).
      eassert (Hpeq: pfx_mmeet c = pfx_meet (pfx_emb k) (pfx_mmeet c)). {
        apply pfx_le_asym; steps. apply pfx_lele_len_ord with (pfx_mmeet c); steps. }
      rewrite Hpeq. steps. }
    lia. }
  replace (half_subcontent (map.put c k v) false) with c. steps.
  rewrite pfx_mmeet_put. steps. steps.
  clear Error. unfold canceling. simpl seps. split; [ | apply I ]. intros.
  apply sep_comm. clear D. simpl cbt' in *. steps.
  subst. apply half_subcontent_put_excl_key. lia.
  congruence. clear Error. steps. clear Error.
  destruct sk; simpl cbt' in *; steps.  symmetry.
  apply half_subcontent_put_excl_bulk. lia. steps. congruence. .**/
      else {                                                                  /**. .**/
        store(p + 4, new_leaf);                                               /**. .**/
        store(p + 8, new_node);                                               /**. .**/
        return tp;                                                            /**. .**/
      }                                                                       /**.
  clear Error. instantiate (1:=Node Leaf sk). simpl cbt'.
  assert (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) = \[cb]). {
    assert (pfx_meet (pfx_emb k) (pfx_mmeet c)
            = pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))). {
      apply pfx_le_asym. apply pfx_meet_le_meet_r. apply pfx_mmeet_key_le. steps.
      apply pfx_meet_le_both. steps.
      apply pfx_lele_len_ord with (pfx_emb (cbt_best_lookup sk c k)). steps.
      apply pfx_mmeet_key_le. steps. steps.
    }
    congruence.
  }
  assert (\[cb] < pfx_len (pfx_mmeet c)). {
    enough (pfx_len (pfx_mmeet c) <> \[cb]) by lia. intro.
    assert (cb = /[pfx_len (pfx_mmeet c)]) by hwlia. subst cb. steps.
    eassert (pfx_len (pfx_mmeet c) < _). {
      apply cbt_best_lookup_cb_not_node. eassumption. steps.
      instantiate (1:=k).
      eassert (Hpeq: pfx_mmeet c = pfx_meet (pfx_emb k) (pfx_mmeet c)). {
        apply pfx_le_asym; steps. apply pfx_lele_len_ord with (pfx_mmeet c); steps. }
      rewrite Hpeq. steps. }
    lia. }
  replace (half_subcontent (map.put c k v) true) with c. simpl cbt' in *. steps.
  subst. rewrite pfx_mmeet_put. steps. steps. subst.
  apply half_subcontent_put_excl_key. lia. congruence.
  clear Error. destruct sk; simpl cbt' in *; steps. subst. symmetry.
  apply half_subcontent_put_excl_bulk. steps. steps. congruence. .**/
    }                                                                         /**. .**/
  }                                                                           /**. .**/
}                                                                             /**.
Qed.

#[export] Instance spec_of_cbt_insert: fnspec :=                                .**/

uintptr_t cbt_insert(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (c: word_map) (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt c tp
                     * R }> m;
  ensures t' m' res := t' = t
           /\ if \[res] =? 0 then
                 <{ * allocator_failed_below 12
                    * cbt c tp
                    * R
                    * fun _ => True }> m'
               else
                 <{ * allocator
                    * cbt (map.put c k v) res
                    * R }> m' #**/                                         /**.
Derive cbt_insert SuchThat (fun_correct! cbt_insert) As cbt_insert_ok.          .**/
{                                                                          /**. .**/
  if (tp == 0) /* split */ {                                               /**.
    (* a direct `return cbt_alloc_leaf(k, v);` gives a type error
       (the assignment_rhs type vs the expr type) *)                            .**/
    uintptr_t res = cbt_alloc_leaf(k, v);                                  /**. .**/
    return res;                                                            /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    uintptr_t best_k = cbt_update_or_best(tp, k, v);                       /**. .**/
    if (best_k == k) /* split */ {                                         /**. .**/
      return tp;                                                           /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**. .**/
      uintptr_t cb = critical_bit(k, best_k);                              /**.
  instantiate (3:=emp True). steps.
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
      uintptr_t result = cbt_insert_at(tp, cb, k, v);                      /**.
  subst. steps. unfold enable_frame_trick.enable_frame_trick. steps. .**/
      return result;                                                       /**. .**/
    }                                                                      /**.
  clear Error. unfold id in *. subst. instantiate (1:=sk'). steps. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_delete_from_nonleaf: fnspec :=                          .**/

uintptr_t cbt_delete_from_nonleaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (skL skR: tree_skeleton) (c: word_map)
                (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' (Node skL skR) c tp
                     * R }> m;
  ensures t' m' res := t' = t
                /\ res = /[match map.get c k with
                           | Some _ => 1
                           | None => 0
                           end]
                /\ <{ * allocator
                      * (EX sk', cbt' sk' (map.remove c k) tp)
                      * R }> m' #**/                                       /**.
Derive cbt_delete_from_nonleaf SuchThat
  (fun_correct! cbt_delete_from_nonleaf) As cbt_delete_from_nonelaf_ok.         .**/
{                                                                          /**. .**/
  uintptr_t cur = 0;                                                       /**. .**/
  uintptr_t sib = 0;                                                       /**. .**/
  uintptr_t par = tp;                                                      /**.
  assert (0 <= pfx_len (pfx_mmeet c) < 32) by steps.
  simpl cbt' in *. repeat heapletwise_step.
  (* context packaging fails if we don't `simpl cbt'` before the `if`
     because of variables being introduced too late *) .**/
  if (((k >> deref(par)) & 1) == 1) {                                      /**. .**/
    sib = load(par + 4);                                                   /**. .**/
    cur = load(par + 8);                                                   /**. .**/
  } else {                                                                 /**. .**/
    cur = load(par + 4);                                                   /**. .**/
    sib = load(par + 8);                                                   /**. .**/
  }                                                                        /**. merge.
  rename c0 into brc.
  loop invariant above cur.
  remember (if brc then skR else skL) as skC.
  remember (if brc then skL else skR) as skS. move skS after Scope2.
  move c before Scope2.
  move cur after Scope2. move sib after Scope2.
  move R before Scope2.

  match goal with
  | H1: ?mL' |= cbt' skL _ _,
    H2: ?mR' |= cbt' skR _ _ |- _ => rename mL' into mL; rename mR' into mR
  end.

  remember (if brc then mR else mL) as mcur.
  remember (if brc then mL else mR) as msib.
  assert (mcur |= cbt' skC (half_subcontent c brc) cur) by (destruct brc; congruence).
  assert (msib |= cbt' skS (half_subcontent c (negb brc)) sib)
     by (destruct brc; simpl negb; congruence).

  match goal with
  | H: _ |= sepapps _ ?pp |- _ =>
       replace aL with (if brc then sib else cur) in H by (destruct brc; congruence);
       replace aR with (if brc then cur else sib) in H by (destruct brc; congruence);
       replace pp with par in H by congruence
  end.
  purge aL. purge aR. purge skL. purge skR.

  (* Why we need the following manual heaplet manipulation? *)
  (* We have the local variables cur and sib which point to subtrees of our CBT.
     In the if-block above, cur/sib is initialized to point to the
     left/right or right/left subtree depending on the value of a boolean flag.
     However, after this if-block, the heaplets are organized in a way that there is
     one heaplet (mL) with the left subtree, which is the cur or the sib subtree
     depending on the value of the flag, and, similarly, there is another heaplet
     (mR) with the right subtree, which again might be both cur or sib depending
     on the flag. In such a situation, accessing the memory of the cur (or sib)
     subtree is cumbersome because the framework cannot (cannot because it's
     impossible with an indeterminate value of the flag) figure out whether that is an
     access in mL or in mR.
     So here, we just replace mL and mR with mcur and msib, where mcur is defined
     as `if flag then mR else mL` and similarly for msib *)
  rewrite mmap.du_comm in D. rewrite <- mmap.du_assoc in D.
  rewrite <- mmap.du_assoc in D.
  replace ((m2 ||| mL) ||| mR) with (m2 ||| mcur ||| msib) in D; cycle 1.
  do 2 rewrite mmap.du_assoc. f_equal. subst mcur. subst msib.
  destruct brc. apply mmap.du_comm. reflexivity.
  purge mL. purge mR.

  match goal with
  | H: par = tp |- _ => rewrite <- H in *; rewrite H at 2; clear H
  end.
  match goal with
  | H1: par <> /[0], H2: 0 <= pfx_len (pfx_mmeet c) < 32 |- _ =>
    move H1 at bottom; move H2 at bottom
  end.
  .**/
  while (load(cur) != 32) /* initial_ghosts(c, cur, skS, sib, par, R);
    decreases skC */ {  /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ cur |- _ => apply cbt_expose_fields in H
  end.
  steps.
  destruct skC; repeat heapletwise_step. { exfalso.
  match goal with
  | H: half_subcontent c brc = _ |- _ => rewrite H in *
  end. steps. } .**/
    par = cur;                                                             /**. .**/
    if (((k >> load(par)) & 1) == 1) /* split */ {                         /**. .**/
      sib = load(par + 4);                                                 /**. .**/
      cur = load(par + 8);                                                 /**. .**/
    }                                                                      /**.
  new_ghosts(half_subcontent c brc, _, _, _, _,
              <{ * R
                 * freeable 12 par'
                   (* FIXME: replacing the values of the `uintptr`s with the
                             '_' placeholder leads to incomplete shelved goals
                             at the end of this proof. Why? *)
                 * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                      + uintptr (if brc then sib' else par)
                      + uintptr (if brc then par else sib') }> par'
                 * cbt' _ _ sib' }>).
  unpurify. steps. subst. rewrite half_subcontent_get. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).
  unpurify. destruct brc eqn:E; simpl cbt'; steps.

  (* TODO: move at least some of the steps in the proof code below into step_hook *)
  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps. rewrite Hhcr.
  steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  rewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k false) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps. .**/
    else {                                                                 /**. .**/
      cur = load(par + 4);                                                 /**. .**/
      sib = load(par + 8);                                                 /**. .**/
    }                                                                      /**.
  new_ghosts(half_subcontent c brc, _, _, _, _,
                  <{ * R
                     * freeable 12 par'
                     * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                          + uintptr (if brc then sib' else par)
                          + uintptr (if brc then par else sib') }> par'
                     * cbt' _ _ sib' }>).
  unpurify. steps. subst. rewrite half_subcontent_get. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).

  destruct brc eqn:E; simpl cbt'; unpurify; steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k false) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps. .**/
  }                                                                        /**.
  destruct skC; cycle 1. { exfalso.
  repeat match goal with
  | H: acbt (Node _ _) _ |- _ => apply acbt_prefix_length in H
  end. pose proof (pfx_len_nneg (pfx_mmeet (half_subcontent c brc))). hwlia. }  .**/
  if (load(cur + 4) == k) /* split */ {                                    /**.
  match goal with
  | H: _ |= cbt' _ _ sib |- _ => apply cbt_expose_fields in H
  end. repeat heapletwise_step.
  .**/
    cbt_raw_node_free(cur);                                                /**. .**/
    cbt_raw_node_copy_replace(par, sib);                                   /**. .**/
    cbt_raw_node_free(sib);                                                /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**.
  assert (map.get c k <> None). {
  eapply map_extends_get_nnone. apply half_subcontent_extends.
  match goal with
  | H: half_subcontent _ _ = map.singleton _ _ |- _ => rewrite H
  end. steps. } destruct (map.get c k); steps.
  clear Error. instantiate (1:=skS).
  replace (map.remove c k) with (half_subcontent c (negb brc)); cycle 1.
  { eapply half_subcontent_removed_half_leaf. eassumption. }
  destruct skS; simpl cbt'; steps.
  match goal with
  | H: half_subcontent c (negb brc) = map.singleton _ _ |- _ => rewrite H
  end. steps. .**/
  else {                                                                   /**. .**/
    return 0;                                                              /**.
  assert (Hgn: map.get c k = None). {
  apply eq_None_by_false. intro HnN. apply half_subcontent_get_nNone in HnN.
  match goal with
  | H: brc = bit_at _ _ |- _ => rewrite <- H in HnN
  end.
  match goal with
  | H: half_subcontent c brc = map.singleton _ _ |- _ => rewrite H in HnN
  end. steps. } .**/
  }                                                                        /**.
  clear Error.
  replace (map.remove c k) with c by
    (symmetry; apply map.remove_not_in; assumption).
  instantiate (1:=if brc then Node skS Leaf else Node Leaf skS).
  destruct brc; simpl cbt'; steps. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_delete: fnspec :=                          .**/

uintptr_t cbt_delete(uintptr_t tpp, uintptr_t k) /**#
  ghost_args := (c: word_map) (tp: word) (R: mem -> Prop);
  requires t m := <{ * allocator
                     * uintptr tp tpp
                     * cbt c tp
                     * R }> m;
  ensures t' m' res := t' = t
                /\ res = /[match map.get c k with
                           | Some _ => 1
                           | None => 0
                           end]
                /\ <{ * allocator
                      * (EX tp', <{ * uintptr tp' tpp
                                    * cbt (map.remove c k) tp' }>)
                      * R }> m' #**/                                       /**.
Derive cbt_delete SuchThat (fun_correct! cbt_delete) As cbt_delete_ok.          .**/
{                                                                          /**. .**/
  uintptr_t tp = load(tpp);                                                /**. .**/
  if (tp == 0) /* split */ {                                               /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**.
  (* TODO: create a tactic which applies cbt_expose_fields to the
           correct hypothesis given the addr of the CBT *)
  match goal with
  | H: _ |= cbt' _ _ tp |- _ => pose proof (purify_cbt' _ _ _ _ H);
                                apply cbt_expose_fields in H
  end. repeat heapletwise_step. .**/
    if (load(tp) == 32) /* split */ {                                      /**.
  destruct tree; cycle 1. { exfalso.
  match goal with
  | H: acbt _ _ |- _ => apply acbt_prefix_length in H
  end.
  pose proof (pfx_len_nneg (pfx_mmeet c)). hwlia. } .**/
      if (load(tp + 4) == k) /* split */ {                                 /**. .**/
        cbt_raw_node_free(tp);                                             /**. .**/
        store(tpp, 0);                                                     /**. .**/
        return 1;                                                          /**. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        return 0;                                                          /**. .**/
      }                                                                    /**.
  clear Error. instantiate (1:=Leaf). simpl cbt'. steps. .**/
    }                                                                      /**. .**/
    else {                                                                 /**.
  destruct tree. { exfalso. steps. } .**/
      uintptr_t ret = cbt_delete_from_nonleaf(tp, k);                      /**.
  simpl cbt'. clear Error. steps.
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
      return ret;                                                          /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

(* END CBT IMPL *)

End LiveVerif. Comments .**/ //.
