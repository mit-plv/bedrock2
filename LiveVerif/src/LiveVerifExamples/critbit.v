(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Require Coq.Bool.Bool.
Require Import Coq.Classes.DecidableClass.

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

Lemma word_eqb_0_1_false : word.eqb /[0] /[1] = false.
Proof.
  hwlia.
Qed.

Lemma word_eqb_1_0_false : word.eqb /[1] /[0] = false.
Proof.
  hwlia.
Qed.

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
        by (symmetry; apply Z.eqb_neq; exact (not_eq_sym Hne))
  | Hne: ?n <> ?m |- context con [ ?m =? ?n ] =>
      let cnvrt := context con [ m =? n ] in change cnvrt;
      replace (m =? n) with false
        by (symmetry; apply Z.eqb_neq; exact (not_eq_sym Hne))

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
        by (symmetry; rewrite Bool.eqb_false_iff; exact (not_eq_sym Hne))
  | Hne: ?b1 <> ?b2 |- context con [ Bool.eqb ?b2 ?b1 ] =>
      let cnvrt := context con [ Bool.eqb b2 b1 ] in change cnvrt;
      replace (Bool.eqb b2 b1) with false
        by (symmetry; rewrite Bool.eqb_false_iff; exact (not_eq_sym Hne))

  | H: Bool.eqb ?b1 ?b2 = true |- _ => apply Bool.eqb_prop in H
  | H: Bool.eqb ?b1 ?b2 = false |- _ => rewrite Bool.eqb_false_iff in H

  (* word.eqb _ _ *)
  | H: context[ word.eqb ?w ?w ] |- _ => rewrite word.eqb_eq in H by reflexivity
  | |- context[ word.eqb ?w ?w ] => rewrite word.eqb_eq by reflexivity

  | H: context [ word.eqb /[0] /[1] ] |- _ => rewrite word_eqb_0_1_false in H
  | |- context [ word.eqb /[0] /[1] ] => rewrite word_eqb_0_1_false
  | H: context [ word.eqb /[1] /[0] ] |- _ => rewrite word_eqb_1_0_false in H
  | |- context [ word.eqb /[1] /[0] ] => rewrite word_eqb_1_0_false

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
        by (symmetry; apply word.eqb_ne; exact (not_eq_sym Hne))
  | Hne: ?w1 <> ?w2 |- context con [ word.eqb ?w2 ?w1 ] =>
      let cnvrt := context con [ word.eqb w2 w1 ] in change cnvrt;
      replace (word.eqb w2 w1) with false
        by (symmetry; apply word.eqb_ne; exact (not_eq_sym Hne))
end.

Lemma identical_if_branches : forall {T} (b: bool) (v: T), (if b then v else v) = v.
Proof.
  destruct b; reflexivity.
Qed.

Lemma neq_negb_eq : forall b1 b2, b1 <> negb b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2; steps.
Qed.

Ltac wsize_term := eval cbn in (sizeof uintptr).
Ltac wsize := let x := wsize_term in exact x.
Ltac is_wsize := constr_eq wsize_term.

Ltac wsize3_term := eval cbn in (3 * ltac:(wsize)).
Ltac wsize3 := let x := wsize3_term in exact x.
Ltac is_wsize3 := constr_eq wsize3_term.

Ltac bw_term := eval cbn in (8 * ltac:(wsize)).
Ltac bw := let x := bw_term in exact x.
Ltac is_bw := constr_eq bw_term.

Ltac bwm1_term := eval cbn in (ltac:(bw) - 1).
Ltac bwm1 := let x := bwm1_term in exact x.
Ltac is_bwm1 := constr_eq bwm1_term.

(* because it comes up as the size of a CBT node allocation *)
Lemma unsigned_of_Z_3words : \[/[ltac:(wsize3)]] = ltac:(wsize3).
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
  | H: context [ \[/[ ?x ]] ] |- _ => is_wsize3 x; rewrite unsigned_of_Z_3words in H
  | |- context [ \[/[ ?x ]] ] => is_wsize3 x; rewrite unsigned_of_Z_3words

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
  | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
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

(* we want:
   - in a CBT, nodes closer to the root to have lower c.b. indices
   - to be able to efficiently use the CBT to find next key w.r.t. to the ordering of
     keys interpreted as integers
  -> therefore, we choose to have bit_at _ 0 give the most significant bit
     and bit_at _ ltac:(bwm1) give the least significant bit (and not the other way around) *)
Definition bit_at (w: word) (i: Z) :=
  word.eqb (word.and (w ^>> /[ltac:(bwm1) - i]) /[1]) /[1].

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  end.

Lemma and_not_1_iff_bit_at_false : forall (w: word) (i: Z),
  word.and (w ^>> /[ltac:(bwm1) - i]) /[1] <> /[1] <-> bit_at w i = false.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_not_1_iff_bit_at_false_w : forall w i: word,
  word.and (w ^>> (/[ltac:(bwm1)] ^- i)) /[1] <> /[1] <-> bit_at w \[i] = false.
Proof.
  unfold bit_at. split; rewrite word.ring_morph_sub; steps.
Qed.

Lemma and_1_iff_bit_at_true : forall (w: word) (i: Z),
  word.and (w ^>> /[ltac:(bwm1) - i]) /[1] = /[1] <-> bit_at w i = true.
Proof.
  unfold bit_at. split; steps.
Qed.

Lemma and_1_iff_bit_at_true_w : forall w i: word,
  word.and (w ^>> (/[ltac:(bwm1)] ^- i)) /[1] = /[1] <-> bit_at w \[i] = true.
Proof.
  unfold bit_at. split; rewrite word.ring_morph_sub; steps.
Qed.

Lemma and_1_eq_bit_at : forall (w1 i1 w2 i2: word),
  word.and (w1 ^>> (/[ltac:(bwm1)] ^- i1)) /[1] =
  word.and (w2 ^>> (/[ltac:(bwm1)] ^- i2)) /[1] ->
  bit_at w1 \[i1] = bit_at w2 \[i2].
Proof.
  unfold bit_at. steps. repeat rewrite word.ring_morph_sub. steps.
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
  word.and (w1 ^>> (/[ltac:(bwm1)] ^- i1)) /[1] <>
    word.and (w2 ^>> (/[ltac:(bwm1)] ^- i2)) /[1] ->
  bit_at w1 \[i1] <> bit_at w2 \[i2].
Proof.
  unfold bit_at. steps. intro. apply_ne.
  repeat rewrite word.ring_morph_sub in *.
  match goal with
  | H: _ = word.eqb ?wa ?wb |- _ => destruct (word.eqb wa wb) eqn:E
  end; steps.
  do 2 match goal with
  | H: _ <> /[1] |- _ => apply and_1_not_1_0 in H
  end. steps.
Qed.

Lemma bit_at_expand : forall w i,
  bit_at w i = word.eqb (word.and (w ^>> (/[ltac:(bwm1)] ^- /[i])) /[1]) /[1].
Proof.
  unfold bit_at. steps. rewrite word.ring_morph_sub. reflexivity.
Qed.

Lemma bit_at_to_standard : forall k i,
  word.and (k ^>> (word.opp /[i] ^+ /[ltac:(bwm1)])) /[1] =
  word.and (k ^>> /[ltac:(bwm1) - i]) /[1].
Proof.
  intros. f_equal. f_equal. hwlia.
Qed.

Lemma bit_at_to_standard' : forall k i,
  word.and (k ^>> (word.opp i ^+ /[ltac:(bwm1)])) /[1] =
  word.and (k ^>> (/[ltac:(bwm1)] ^- i)) /[1].
Proof.
  intros. f_equal. f_equal. hwlia.
Qed.

Ltac bit_at_step :=
  match goal with
  | H: context [ word.and (_ ^>> (word.opp /[_] ^+ /[?x])) /[1] ] |- _ =>
       is_bwm1 x; rewrite bit_at_to_standard in H
  | |- context [ word.and (_ ^>> (word.opp /[_] ^+ /[?x])) /[1] ] =>
       is_bwm1 x; rewrite bit_at_to_standard
  | H: context [ word.and (_ ^>> (word.opp _ ^+ /[?x])) /[1] ] |- _ =>
       is_bwm1 x; rewrite bit_at_to_standard' in H
  | |- context [ word.and (_ ^>> (word.opp _ ^+ /[?x])) /[1] ] =>
       is_bwm1 x; rewrite bit_at_to_standard'
  | H: word.and (_ ^>> /[_]) /[1] = /[1] |- _ => apply and_1_iff_bit_at_true in H
  | H: word.and (_ ^>> _) /[1] = /[1] |- _ => apply and_1_iff_bit_at_true_w in H
  | H: word.and (_ ^>> /[_]) /[1] <> /[1] |- _ => apply and_not_1_iff_bit_at_false in H
  | H: word.and (_ ^>> _) /[1] <> /[1] |- _ => apply and_not_1_iff_bit_at_false_w in H
  | H: word.and (_ ^>> _) /[1] = word.and (_ ^>> _) /[1] |- _ =>
       apply and_1_eq_bit_at
  | H: word.and (_ ^>> _) /[1] <> word.and (_ ^>> _) /[1] |- _ =>
       apply and_1_ne_bit_at
  | H: context [ word.eqb (word.and (?w ^>> (/[?x] ^- /[?i])) /[1]) /[1] ] |- _ =>
       is_bwm1 x; rewrite <- bit_at_expand in H
  | |- context [ word.eqb (word.and (?w ^>> (/[?x] ^- /[?i])) /[1]) /[1] ] =>
       is_bwm1 x; rewrite <- bit_at_expand
  end.

Lemma Z_testbit_is_bit_at : forall w i,
  0 <= i < ltac:(bw) -> Z.testbit \[w] i = bit_at w (ltac:(bwm1) - i).
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

Lemma Z_testbit_past_word_width : forall w i,
  ~(0 <= i < ltac:(bw)) -> Z.testbit \[w] i = false.
Proof.
  intros. assert (Hcmp: i < 0 \/ 0 <= i < ltac:(bw) \/ ltac:(bw) <= i) by lia.
  destruct Hcmp as [ Hc | [ Hc | Hc ] ]; steps.
  - apply Z.testbit_neg_r. lia.
  - replace w with /[\[w]] by steps. rewrite word.unsigned_of_Z. unfold word.wrap.
    rewrite Z.mod_pow2_bits_high; steps.
Qed.

Lemma bit_at_inj : forall w1 w2,
  (forall i, 0 <= i < ltac:(bw) -> bit_at w1 i = bit_at w2 i) -> w1 = w2.
Proof.
  steps. apply word.unsigned_inj. apply Z.bits_inj. unfold Z.eqf. intros.
  assert (Hcmp: 0 <= n < ltac:(bw) \/ ~(0 <= n < ltac:(bw))) by lia. destruct Hcmp.
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
  pfx_emb_len : forall w, pfx_len (pfx_emb w) = ltac:(bw);
  pfx_emb_spec : forall w i,
    0 <= i < ltac:(bw) -> pfx_bit (pfx_emb w) i = Some (bit_at w i)
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
  | S n => cons (bit_at w (ltac:(bw) - Z.of_nat remaining)) (pfx'_emb_rec w n)
  end.

Lemma pfx'_emb_rec_bit : forall w (n: nat) i,
  0 <= i < Z.of_nat n ->
  List.get (pfx'_emb_rec w n) i = bit_at w (ltac:(bw) - Z.of_nat n + i).
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
  pfx_emb w := pfx'_emb_rec w (Z.to_nat ltac:(bw))
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
  - intros. simpl. reflexivity.
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
  w1 <> w2 -> pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2)) < ltac:(bw).
Proof.
  intros.
  match goal with
  | |- ?l < _ => assert (Hb: l <= ltac:(bw));
       [ rewrite <- (pfx_emb_len w1); apply pfx_le_len; apply pfx_meet_le_l
       | enough (l <> ltac:(bw)) by lia ]; clear Hb
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
  0 <= n < ltac:(bw) ->
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
  pfx_len (pfx_meet (pfx_emb w) p) <= ltac:(bw).
Proof.
  intros. rewrite <- (pfx_emb_len w). apply pfx_le_len. apply pfx_meet_le_l.
Qed.

Lemma pfx_meet_right_emb_len_bound : forall p w,
  pfx_len (pfx_meet p (pfx_emb w)) <= ltac:(bw).
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
  | |- pfx_len (pfx_meet (pfx_emb _) _) <= ?x =>
       is_bw x; apply pfx_meet_left_emb_len_bound
  | |- pfx_len (pfx_meet _ (pfx_emb _)) <= ?x =>
       is_bw x; apply pfx_meet_right_emb_len_bound
  | |- ?p1 = pfx_meet ?p1 ?p2 => symmetry; apply pfx_meet_le_eq
  | |- ?p1 = pfx_meet ?p2 ?p1 => symmetry; apply pfx_meet_le_eq'
  | |- pfx_meet ?p1 ?p2 = ?p1 => apply pfx_meet_le_eq
  | |- pfx_meet ?p2 ?p1 = ?p1 => apply pfx_meet_le_eq'
  | H: ?k1 <> ?k2 |- pfx_len (pfx_meet (pfx_emb ?k1) (pfx_emb ?k2)) < ?x =>
       is_bw x; exact (pfx_meet_neq_emb_len k1 k2 H)
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

Lemma pfx_mmeet_len : forall c, pfx_len (pfx_mmeet c) <= ltac:(bw).
Proof.
  intros. unfold pfx_mmeet, pfx'_mmeet.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun _ state => state = None \/
             exists p, state = Some p /\ pfx_len p <= ltac:(bw)).
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
  map.get c k0 <> None -> map.get c k1 <> None -> k0 <> k1 ->
  pfx_len (pfx_mmeet c) < ltac:(bw).
Proof.
  intros.
  enough
    (pfx_len (pfx_mmeet c) <= pfx_len (pfx_meet (pfx_emb k0) (pfx_emb k1)) < ltac:(bw))
    by lia.
  split. apply pfx_le_len. apply pfx_meet_le_both; steps.
  auto using pfx_meet_neq_emb_len.
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
      assert (0 <= pfx_len (pfx_mmeet c) < ltac:(bw)). {
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
           * freeable ltac:(wsize3) a
           * <{ + uintptr /[ltac:(bw)]
                + uintptr k
                + uintptr v }> a
           * emp (c = map.singleton k v) }>
  | Node treeL treeR => EX (aL: word) (aR: word),
          <{ * emp (a <> /[0])
             * freeable ltac:(wsize3) a
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
                   | Node _ _ => pfx_len (pfx_mmeet c) < ltac:(bw)
                   | Leaf => pfx_len (pfx_mmeet c) = ltac:(bw)
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
    <{ * freeable ltac:(wsize3) a
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
  acbt (Node sk1 sk2) c -> 0 <= pfx_len (pfx_mmeet c) < ltac:(bw).
Proof.
  steps. apply acbt_prefix_length in H. pose proof (pfx_len_nneg (pfx_mmeet c)). lia.
Qed.

Lemma node_prefix_length_word_not_bw : forall sk1 sk2 c,
  acbt (Node sk1 sk2) c -> /[pfx_len (pfx_mmeet c)] <> /[ltac:(bw)].
Proof.
  steps. apply node_prefix_length in H. hwlia.
Qed.

Ltac cbt_step :=
  match goal with
  | H: acbt (Node _ _) ?c |- 0 <= pfx_len (pfx_mmeet ?c) < ?x =>
    is_bw x; apply node_prefix_length in H
  | Hacbt: acbt ?sk (half_subcontent ?c ?b),
    Hlkup: cbt_best_lookup ?t (half_subcontent ?c ?b) ?k' = ?k
    |- map.get ?c ?k <> None =>
    apply (cbt_best_lookup_subcontent_in_parent t c k k' b Hacbt Hlkup)
  | Hacbt: acbt (Node _ _) ?c, Hpl: /[pfx_len (pfx_mmeet ?c)] = /[?x] |- _ =>
    is_bw x; destruct (node_prefix_length_word_not_bw _ _ _ Hacbt Hpl)
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
  acbt sk c -> pfx_len (pfx_mmeet c) < ltac:(bw) -> pfx_le (pfx_mmeet c) (pfx_emb k) ->
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
(* change from #[local] to #[export]? *)
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
#[local] Hint Extern 1 (PredicateSize_not_found (cbt _))
      => constructor : suppressed_warnings.

(* #[local] Hint Unfold cbt : heapletwise_always_unfold. *)
#[local] Hint Unfold nncbt : heapletwise_always_unfold.

Hint Resolve purify_cbt' : purify.

Local Hint Extern 1 (PredicateSize (cbt' ?sk)) => wsize3 : typeclass_instances.

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
                     allocator_failed_below ltac:(wsize3)
                    else
                     <{ * allocator
                        * freeable ltac:(wsize3) res
                        * <{ + uintptr w1
                             + uintptr w2
                             + uintptr w3 }> res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_raw_node_alloc SuchThat (fun_correct! cbt_raw_node_alloc)
  As cbt_raw_node_alloc_ok.                                                     .**/
{                                                                          /**. .**/
  uintptr_t p = Malloc(3 * sizeof(uintptr_t));                             /**. .**/
  if (p == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    store(p, w1);                                                          /**. .**/
    store(p + sizeof(uintptr_t), w2);                                      /**. .**/
    store(p + 2 * sizeof(uintptr_t), w3);                                  /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /*?.
  repeat clear_array_0. steps. steps. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_raw_node_free: fnspec :=                         .**/

void cbt_raw_node_free(uintptr_t node) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * freeable (ltac:(wsize3)) node
                     * (EX w1 w2 w3, <{ + uintptr w1
                                        + uintptr w2
                                        + uintptr w3 }> node)
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * allocator * R }> m' #**/                 /**.
Derive cbt_raw_node_free SuchThat (fun_correct! cbt_raw_node_free)
  As cbt_raw_node_free_ok.                                                      .**/
{                                                                          /**. .**/
  Free(node);                                                              /*?.
  instantiate (5:=/[ltac:(wsize3)]). steps. steps. .**/
}                                                                          /**.

  (* FIXME: this should probably be done more automatically *)
  unfold impl1. intro m'. steps.
  eapply cast_to_anybytes.
  change (ltac:(wsize3)) with (ltac:(wsize) + (ltac:(wsize) + (ltac:(wsize) + 0))).
  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w1).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: ltac:(wsize) = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w2).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: ltac:(wsize) = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_cons_contiguous.
  instantiate (1:=uintptr w3).
  pose proof uintptr_contiguous as Hcntg.
  eassert (Hw: ltac:(wsize) = _); cycle 1. rewrite Hw. apply Hcntg.
  compute. steps.

  eapply sepapps_nil_contiguous.

  steps.
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
                     allocator_failed_below ltac:(wsize3)
                    else
                     <{ * allocator
                        * freeable ltac:(wsize3) res
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
                                   load(src + sizeof(uintptr_t)),
                                   load(src + 2 * sizeof(uintptr_t)));     /**. .**/
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
  store(dst + sizeof(uintptr_t), load(src + sizeof(uintptr_t)));           /**. .**/
  store(dst + 2 * sizeof(uintptr_t), load(src + 2 * sizeof(uintptr_t)));   /**. .**/
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
  while (load(p) != 8 * sizeof(uintptr_t))
    /* initial_ghosts(p, c, R); decreases tree */ {  /*?.
  subst v0.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct tree. { exfalso. steps. }
  rename w2 into aL. rename w3 into aR. .**/
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(p))) & 1) == 1) /* split */ { /**. .**/
      p = load(p + 2 * sizeof(uintptr_t));                                   /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c true,
                 <{ * R
                    * freeable ltac:(wsize3) p'
                    * cbt' tree1 (half_subcontent c false) aL
                    * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                         + uintptr aL
                         + uintptr p }> p' }>).
  instantiate (1:=tree2). steps. simpl. steps.

  clear Error.
  assert (map.get c retv <> None) by steps.
  destruct (word.eqb retv k) eqn:E; simpl cbt'; steps; subst k; steps. .**/
    else {                                                                   /**. .**/
      p = load(p + sizeof(uintptr_t));                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c false, <{ * R
                       * freeable ltac:(wsize3) p'
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
    if (load(p + sizeof(uintptr_t)) == k) /* split */ {                     /**. .**/
    store(p + 2 * sizeof(uintptr_t), v);                                    /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  simpl. apply map_some_key_singleton. clear Error. simpl cbt'. steps. .**/
  else {                                                                    /**. .**/
    return load(p + sizeof(uintptr_t));                                     /**. .**/
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
  while (load(p) != 8 * sizeof(uintptr_t))
    /* initial_ghosts(p,c,R); decreases sk */ {                              /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end. steps.
  destruct sk. { exfalso. steps. }
  rename w2 into aL. rename w3 into aR. .**/
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(p))) & 1) == 1) /* split */ { /**. .**/
      p = load(p + 2 * sizeof(uintptr_t));                                   /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c true, <{ * R
                       * freeable ltac:(wsize3) p'
                       * cbt' sk1 (half_subcontent c false) aL
                       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                            + uintptr aL
                            + uintptr p }> p' }>).
  steps. clear Error. simpl cbt'. steps. .**/
    else {                                                                   /**. .**/
      p = load(p + sizeof(uintptr_t));                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c false, <{ * R
                           * freeable ltac:(wsize3) p'
                           * cbt' sk2 (half_subcontent c true) aR
                           * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                                + uintptr p
                                + uintptr aR }> p' }>).
  steps. clear Error. simpl cbt'. steps. .**/
    }                                                                          /**.
  destruct sk; cycle 1. { exfalso. steps. } simpl cbt'. .**/
  if (load(p + sizeof(uintptr_t)) == k) /* split */ {                        /**. .**/
    store(val_out, load(p + 2 * sizeof(uintptr_t)));                         /**. .**/
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
{                                                                           /**.
  unfold cbt, nncbt in *. .**/
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
                     allocator_failed_below ltac:(wsize3)
                   else
                     <{ * allocator
                        * cbt' Leaf (map.singleton k v) res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_alloc_leaf SuchThat (fun_correct! cbt_alloc_leaf) As cbt_alloc_leaf_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = cbt_raw_node_alloc(8 * sizeof(uintptr_t), k, v);           /**. .**/
  return p;                                                                /**. .**/
}                                                                          /**.
  simpl cbt'. destruct (\[p] =? 0) eqn:E; steps.
Qed.

#[export] Instance spec_of_critical_bit: fnspec :=                              .**/

uintptr_t critical_bit(uintptr_t k1, uintptr_t k2) /**#
  (* heaplet packaging doesn't work well then there's just one item in the heap
     [or I was doing something wrong] *)
  ghost_args := (R1 R2: mem -> Prop);
  requires t m := k1 <> k2 /\ <{ * R1 * R2 }> m;
  ensures t' m' res := t = t' /\ <{ * R1 * R2 }> m'
                /\ 0 <= \[res] < ltac:(bw)
                /\ \[res] = pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)) #**/
/**.
Derive critical_bit SuchThat (fun_correct! critical_bit) As critical_bit_ok.    .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.
  prove (0 <= \[i] < ltac:(bw)).
  assert (forall n, 0 <= n < \[i] -> bit_at k1 n = bit_at k2 n).
  intros. hwlia.
  delete #(i = /[0]).
  loop invariant above H.
  move i at bottom. .**/
  while (i < 8 * sizeof(uintptr_t) - 1
    && ((k1 >> (8 * sizeof(uintptr_t) - 1 - i) & 1)
          == ((k2 >> (8 * sizeof(uintptr_t) - 1 - i) & 1))))
    /* decreases (ltac:(bw) - \[i]) */ {                                   /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /**.
  assert (Hcmp: n = \[i'] \/ n < \[i']) by lia. destruct Hcmp.
  { subst. steps. }
  { match goal with | H: forall _, _ |- _ => apply H end. lia. } .**/
  return i;                                                                /**. .**/
}                                                                          /**.
  symmetry. apply pfx_cb_charac; steps.
  { unzify. destruct_or. assert (Hui: \[i] = ltac:(bwm1)) by lia.
    rewrite Hui in *. intro.
    match goal with
    | H: k1 <> k2 |- _ => apply H
    end.
    apply bit_at_inj. intros. assert (Hcmp: i0 = ltac:(bwm1) \/ i0 < ltac:(bwm1)) by lia.
    destruct Hcmp.
    { steps. } { match goal with | H: forall _, _ |- _ => apply H end. lia. }
  steps.
}
Qed.

#[export] Instance spec_of_cbt_insert_at: fnspec :=                             .**/

uintptr_t cbt_insert_at(uintptr_t tp, uintptr_t cb, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map) (R: mem -> Prop);
  requires t m := 0 <= \[cb] < ltac:(bw)
                  /\ pfx_len
                       (pfx_meet
                         (pfx_emb k)
                         (pfx_emb (cbt_best_lookup sk c k)))
                      = \[cb]
                  /\ <{ * allocator
                        * cbt' sk c tp
                        * R }> m;
  ensures t' m' res := t' = t
                       /\ if \[res] =? 0 then
                            <{ * allocator_failed_below ltac:(wsize3)
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
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(p))) & 1) == 1) /* split */ { /**. .**/
      p = load(p + 2 * sizeof(uintptr_t));                                  /**. .**/
    }                                                                       /**.
  new_ghosts(p, half_subcontent c true, <{ * R
                           * freeable ltac:(wsize3) p'
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
      p = load(p + sizeof(uintptr_t));                                        /**. .**/
    }                                                                         /**.
  new_ghosts (p, half_subcontent c false,
      <{ * R
         * freeable ltac:(wsize3) p'
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
      if (((k >> (8 * sizeof(uintptr_t) - 1 - cb)) & 1) == 1) /* split */ { /**. .**/
        store(p + sizeof(uintptr_t), new_node);                              /**. .**/
        store(p + 2 * sizeof(uintptr_t), new_leaf);                          /**. .**/
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
        store(p + sizeof(uintptr_t), new_leaf);                               /**. .**/
        store(p + 2 * sizeof(uintptr_t), new_node);                           /**. .**/
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
                 <{ * allocator_failed_below ltac:(wsize3)
                    * cbt c tp
                    * R
                    * fun _ => True }> m'
               else
                 <{ * allocator
                    * cbt (map.put c k v) res
                    * R }> m' #**/                                         /**.
Derive cbt_insert SuchThat (fun_correct! cbt_insert) As cbt_insert_ok.          .**/
{                                                                          /**.
  unfold cbt, nncbt in *. .**/
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
  instantiate (3:=emp True). steps. .**/
      uintptr_t result = cbt_insert_at(tp, cb, k, v);                      /**.
  (* TODO: figure out why instantiate_frame_evar_with_remaining_obligation
           fails here when canceling the frace ?R, and so we need to
           manually unfold enable_frame_trick *)
  (* ...maybe has something to do what the memory we are canceling in is only
     one heaplet and not a union? *)
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
  assert (0 <= pfx_len (pfx_mmeet c) < ltac:(bw)) by steps.
  simpl cbt' in *. repeat heapletwise_step.
  (* context packaging fails if we don't `simpl cbt'` before the `if`
     because of variables being introduced too late *) .**/
  if (((k >> (8 * sizeof(uintptr_t) - 1 - deref(par))) & 1) == 1) {                               /**. .**/
    sib = load(par + sizeof(uintptr_t));                                   /**. .**/
    cur = load(par + 2 * sizeof(uintptr_t));                               /**. .**/
  } else {                                                                 /**. .**/
    cur = load(par + sizeof(uintptr_t));                                   /**. .**/
    sib = load(par + 2 * sizeof(uintptr_t));                               /**. .**/
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
  | H1: par <> /[0], H2: 0 <= pfx_len (pfx_mmeet c) < _ |- _ =>
    move H1 at bottom; move H2 at bottom
  end.
  .**/
  while (load(cur) != 8 * sizeof(uintptr_t))
    /* initial_ghosts(c, cur, skS, sib, par, R); decreases skC */ {  /*?.
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
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(par))) & 1) == 1) /* split */
    {                                                                      /**. .**/
      sib = load(par + sizeof(uintptr_t));                                 /**. .**/
      cur = load(par + 2 * sizeof(uintptr_t));                             /**. .**/
    }                                                                      /**.
  new_ghosts(half_subcontent c brc, _, _, _, _,
              <{ * R
                 * freeable ltac:(wsize3) par'
                   (* FIXME: replacing the values of the `uintptr`s with the
                             '_' placeholder leads to incomplete shelved goals
                             at the end of this proof. Why? *)
                 * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                      + uintptr (if brc then sib' else par)
                      + uintptr (if brc then par else sib') }> par'
                 * cbt' _ _ sib' }>).
  unpurify. steps.
  1-4:
  match goal with
  | |- context [ word.eqb ?a ?b ] => replace (word.eqb a b) with true; reflexivity
  end.
  rewrite half_subcontent_get. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).
  unpurify. destruct brc eqn:E; simpl cbt'; steps.

  (* TODO: move at least some of the steps in the proof code below into step_hook *)
  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps. rewrite Hhcr.
  steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  rewrite half_subcontent_remove_same. steps. steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k false) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps. .**/
    else {                                                                 /**. .**/
      cur = load(par + sizeof(uintptr_t));                                 /**. .**/
      sib = load(par + 2 * sizeof(uintptr_t));                             /**. .**/
    }                                                                      /**.
  new_ghosts(half_subcontent c brc, _, _, _, _,
                  <{ * R
                     * freeable ltac:(wsize3) par'
                     * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                          + uintptr (if brc then sib' else par)
                          + uintptr (if brc then par else sib') }> par'
                     * cbt' _ _ sib' }>).
  unpurify. steps.
  1-4:
  match goal with
  | |- context [ word.eqb ?a ?b ] => replace (word.eqb a b) with false; reflexivity
  end.
  rewrite half_subcontent_get. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).

  destruct brc eqn:E; simpl cbt'; unpurify; steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). steps.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in. steps.
  rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. steps.
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
  if (load(cur + sizeof(uintptr_t)) == k) /* split */ {                    /**.
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
  | H: brc = word.eqb _ _ |- _ =>
       rewrite word.ring_morph_sub in H; rewrite <- bit_at_expand in H;
       rewrite <- H in HnN
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
{                                                                          /**.
  unfold cbt, nncbt in *. .**/
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
    if (load(tp) == 8 * sizeof(uintptr_t)) /* split */ {                   /**.
  destruct tree; cycle 1. { exfalso.
  match goal with
  | H: acbt _ _ |- _ => apply acbt_prefix_length in H
  end.
  pose proof (pfx_len_nneg (pfx_mmeet c)). hwlia. } .**/
      if (load(tp + sizeof(uintptr_t)) == k) /* split */ {                 /**. .**/
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
  simpl cbt'. clear Error. steps. .**/
      return ret;                                                          /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

(* TODO: hoist *)
Lemma half_subcontent_get_some : forall c b k v,
  map.get (half_subcontent c b) k = Some v -> map.get c k = Some v.
Proof.
  intros. rewrite half_subcontent_get in *.
  match goal with
  | H: context [ if ?cond then _ else _ ] |- _ => destruct cond
  end; steps.
Qed.

Lemma Z_land_0_land_ldiff : forall c a b,
  Z.land (Z.ldiff a c) (Z.land b c) = 0.
Proof.
  intros. apply Z.bits_inj'. intros. repeat rewrite Z.land_spec. rewrite Z.ldiff_spec.
  rewrite Z.bits_0. destruct (Z.testbit c n); lia.
Qed.

Lemma Z_land_le : forall a b,
  0 <= b -> Z.land a b <= b.
Proof.
  intros.
  pose proof (bitblast.Z.or_to_plus _ _ (Z_land_0_land_ldiff a b b)).
  rewrite Z.lor_ldiff_and in *.
  assert (0 <= Z.ldiff b a). { rewrite Z.ldiff_nonneg. lia. } rewrite Z.land_comm. lia.
Qed.

Lemma Z_ones_nonneg : forall i, 0 <= i -> 0 <= Z.ones i.
Proof.
  intros. unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma Z_testbit_lt : forall n1 n2 i,
  Z.testbit n1 i = false -> Z.testbit n2 i = true ->
  (forall j, i < j -> Z.testbit n1 j = Z.testbit n2 j) ->
  n1 < n2.
Proof.
  intros. assert (0 <= i). { enough (Hni: ~(i < 0)) by lia. intro.
    match goal with
    | H: Z.testbit _ _ = true |- _ => rewrite Z.testbit_neg_r in H by lia
    end. discriminate. }
  remember (Z.ldiff n1 (Z.ones (i + 1))) as nc.
  assert (n1 = Z.lor nc (Z.land n1 (Z.ones (i + 1)))).
  { subst. symmetry. apply Z.lor_ldiff_and. }
  assert (n2 = Z.lor nc (Z.land n2 (Z.ones (i + 1)))).
  { subst. replace (Z.ldiff n1 (Z.ones (i + 1))) with (Z.ldiff n2 (Z.ones (i + 1))).
    symmetry. apply Z.lor_ldiff_and. apply Z.bits_inj'. intros.
    do 2 rewrite Z.ldiff_spec. assert (Hcmp: n <= i \/ i < n) by lia.
    rewrite Z.testbit_ones_nonneg by lia.
    destruct Hcmp; steps. replace (n <? i + 1) with false by lia. steps.
    symmetry. eauto. }
  do 2 match goal with
       | H: _ = Z.lor _ _ |- _ =>
            rewrite bitblast.Z.or_to_plus in H by (subst; apply Z_land_0_land_ldiff)
       end.
  do 2 match goal with
       | H: _ = nc + _ |- _ => rewrite H; clear H
       end.
  apply Zplus_lt_compat_l.
  enough (Hb: Z.land n1 (Z.ones (i + 1)) <= Z.ones i /\
              Z.shiftl 1 i <= Z.land n2 (Z.ones (i + 1))).
  { assert (1 <= Z.shiftl 1 (i + 1)). { rewrite Z.shiftl_1_l. lia. }
    destruct Hb. unfold Z.ones in *. lia. }
  split.
  - replace (Z.land n1 (Z.ones (i + 1))) with (Z.land n1 (Z.ones i)).
    { apply Z_land_le. auto using Z_ones_nonneg. }
    apply Z.bits_inj'. intros. do 2 rewrite Z.land_spec.
    do 2 rewrite bitblast.Z.testbit_ones_nonneg by lia.
    eq_neq_cases n i. { subst.  match goal with | H: _ = false |- _ => rewrite H end.
      steps. }
    f_equal. lia.
  - eassert (Hsub: _).
    { apply (Z.sub_nocarry_ldiff (Z.land n2 (Z.ones (i + 1))) (Z.shiftl 1 i)).
      apply Z.bits_inj'. intros. rewrite Z.bits_0. rewrite Z.ldiff_spec.
      rewrite Z.shiftl_spec by lia. rewrite Z_bits_1. rewrite Z.land_spec.
      rewrite Z.testbit_ones_nonneg by lia. destruct (Z.testbit n2 n) eqn:E; steps.
      enough (n <> i) by lia. intro. subst. congruence. }
    match type of Hsub with
    | _ = ?r => assert (0 <= r)
    end.
    { rewrite Z.ldiff_nonneg. left. rewrite Z.land_nonneg.
      right. apply Z_ones_nonneg. lia. }
    lia.
Qed.

Lemma bit_at_lt : forall w1 w2 i, 0 <= i < ltac:(bw) ->
  (forall j, 0 <= j < i -> bit_at w1 j = bit_at w2 j) ->
  bit_at w1 i = false -> bit_at w2 i = true ->
  \[w1] < \[w2].
Proof.
  intros. eapply (Z_testbit_lt _ _ (ltac:(bwm1) - i)).
  - rewrite Z_testbit_is_bit_at; steps.
  - rewrite Z_testbit_is_bit_at; steps.
  - intros. assert (Hcmp: 0 <= j < ltac:(bw) \/ ~(0 <= j < ltac:(bw))) by lia. destruct Hcmp.
    + do 2 rewrite Z_testbit_is_bit_at by lia. apply_forall. lia.
    + do 2 rewrite Z_testbit_past_word_width by assumption. reflexivity.
Qed.

Lemma bit_at_le : forall w1 w2 i, 0 <= i < ltac:(bw) ->
  (forall j, 0 <= j < i -> bit_at w1 j = bit_at w2 j) ->
  bit_at w1 i = false -> bit_at w2 i = true ->
  \[w1] <= \[w2].
Proof.
  intros. enough (\[w1] < \[w2]) by lia. eauto using bit_at_lt.
Qed.

Lemma pfx_le_bit_at_wlt : forall p w1 w2,
  pfx_le p (pfx_emb w1) -> pfx_le p (pfx_emb w2) -> pfx_len p < ltac:(bw) ->
  bit_at w1 (pfx_len p) = false -> bit_at w2 (pfx_len p) = true -> \[w1] < \[w2].
Proof.
  intros. eapply bit_at_lt; try eassumption.
  - pose proof (pfx_len_nneg p). lia.
  - intros. rewrite <- pfx_le_spec in *.
    do 2 match goal with
         | Hfa: forall _, _, Hrng: _ <= _ < _ |- _ => specialize (Hfa _ Hrng)
         end.
    rewrite pfx_emb_spec in * by lia. congruence.
Qed.

(* TODO: hoist *)
Lemma half_subcontent_in_false_true_lt : forall c k k',
  map.get (half_subcontent c false) k <> None ->
  map.get (half_subcontent c true) k' <> None ->
  \[k] < \[k'].
Proof.
  intros. eapply pfx_le_bit_at_wlt with (p:=pfx_mmeet c);
  eauto using half_subcontent_get_nnone, pfx_mmeet_key_le, half_subcontent_in_bit.
  apply (pfx_mmeet_nonsingle_len _ k k'); eauto using half_subcontent_get_nnone.
  intro. subst k'.
  do 2 match goal with
       | H: map.get _ _ <> None |- _ => apply half_subcontent_in_bit in H
       end.
  congruence.
Qed.

(* TODO: hoist *)
(* actually, even `_lt` holds *)
Lemma half_subcontent_in_false_true_le : forall c k k',
  map.get (half_subcontent c false) k <> None ->
  map.get (half_subcontent c true) k' <> None ->
  \[k] <= \[k'].
Proof.
  intros. enough (\[k] < \[k']) by lia. eauto using half_subcontent_in_false_true_lt.
Qed.

#[export] Instance spec_of_cbt_get_min_impl: fnspec :=                          .**/
void cbt_get_min_impl(uintptr_t tp, uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map)
                (key_out_orig: word) (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * cbt' sk c tp
                     * uintptr key_out_orig key_out
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' := t' = t
           /\ <{ * cbt' sk c tp
                 * (EX k v,
                      <{ * emp (map.get c k = Some v)
                         * emp (forall k', map.get c k' <> None -> \[k] <= \[k'])
                         * uintptr k key_out
                         * uintptr v val_out }>)
                 * R }> m'         #**/                                    /**.
Derive cbt_get_min_impl SuchThat (fun_correct! cbt_get_min_impl)
  As cbt_get_min_impl_ok.                                                       .**/
{                                                                          /**.
  move sk at bottom.
  loop invariant above m. .**/
  while (load(tp) != 8 * sizeof(uintptr_t)) /* initial_ghosts(tp,c,R); decreases sk */ {      /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ tp |- _ => pose proof (purify_cbt' _ _ _ _ H);
                                apply cbt_expose_fields in H
  end. steps. destruct sk. { exfalso; steps. } .**/
      tp = load(tp + sizeof(uintptr_t));                                   /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c false,
      <{ * cbt' sk2 (half_subcontent c true) w3
         * freeable ltac:(wsize3) tp'
         * <{ + uintptr /[pfx_len (pfx_mmeet c)]
              + uintptr tp
              + uintptr w3 }> tp'
         * R }>).
  steps. clear Error. simpl cbt'. steps.
  eapply half_subcontent_get_some. eassumption.
  match goal with
  | H: map.get _ _ <> None |- _ => apply half_subcontent_get_nNone in H
  end.
  { match goal with
    | H: context [ map.get (half_subcontent _ ?b) _ <> None ] |- _ => destruct b
    end.
    - eapply half_subcontent_in_false_true_le; [ | eassumption ]. steps.
    - apply_forall. steps. }
  destruct sk; [ | exfalso; steps ]. .**/
  store(key_out, load(tp + sizeof(uintptr_t)));                            /**.
  (* TODO: figure out why enable_frame_trick appears here *)
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
  store(val_out, load(tp + 2 * sizeof(uintptr_t)));                        /**. .**/
}                                                                          /**.
simpl cbt'. clear Error. steps. subst. steps.
Qed.

#[export] Instance spec_of_cbt_get_min: fnspec :=                                .**/
uintptr_t cbt_get_min(uintptr_t tp, uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (key_out_orig: word) (val_out_orig: word)
                (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr key_out_orig key_out
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = if word.eqb tp /[0] then /[0] else /[1])
                 * cbt c tp
                 * (if word.eqb tp /[0] then
                      <{ * uintptr key_out_orig key_out
                         * uintptr val_out_orig val_out }>
                    else
                      (EX k v,
                        <{ * emp (map.get c k = Some v)
                           * emp (forall k', map.get c k' <> None -> \[k] <= \[k'])
                           * uintptr k key_out
                           * uintptr v val_out }>))
                 * R }> m'         #**/                                    /**.
Derive cbt_get_min SuchThat (fun_correct! cbt_get_min) As cbt_get_min_ok.       .**/
{                                                                          /**.
  unfold cbt, nncbt in *. .**/
  if (tp == 0) /* split */ {                                               /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    cbt_get_min_impl(tp, key_out, val_out);                                /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**.
  apply_forall; steps. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_get_max: fnspec :=                                .**/
uintptr_t cbt_get_max(uintptr_t tp, uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (key_out_orig: word) (val_out_orig: word)
                (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr key_out_orig key_out
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = if word.eqb tp /[0] then /[0] else /[1])
                 * cbt c tp
                 * (if word.eqb tp /[0] then
                      <{ * uintptr key_out_orig key_out
                         * uintptr val_out_orig val_out }>
                    else
                      (EX k v,
                        <{ * emp (map.get c k = Some v)
                           * emp (forall k', map.get c k' <> None -> \[k'] <= \[k])
                           * uintptr k key_out
                           * uintptr v val_out }>))
                 * R }> m'         #**/                                    /**.
Derive cbt_get_max SuchThat (fun_correct! cbt_get_max) As cbt_get_max_ok.       .**/
{                                                                          /**.
  unfold cbt, nncbt in *. .**/
  if (tp == 0) /* split */ {                                               /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**.
  move tree at bottom.
  loop invariant above m. .**/
    while (load(tp) != 8 * sizeof(uintptr_t))
      /* initial_ghosts(tp,c,R); decreases tree */ {   /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ tp |- _ => pose proof (purify_cbt' _ _ _ _ H);
                                apply cbt_expose_fields in H
  end. steps. destruct tree. { exfalso; steps. } .**/
      tp = load(tp + 2 * sizeof(uintptr_t));                               /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c true,
      <{ * cbt' tree1 (half_subcontent c false) w2
         * freeable ltac:(wsize3) tp'
         * <{ + uintptr /[pfx_len (pfx_mmeet c)]
              + uintptr w2
              + uintptr tp }> tp'
         * R }>).
  steps. instantiate (1:=Node tree1 tree). clear Error. simpl cbt'. steps.
  eapply half_subcontent_get_some. eassumption.
  match goal with
  | H: map.get _ _ <> None |- _ => apply half_subcontent_get_nNone in H
  end.
  { match goal with
    | H: context [ map.get (half_subcontent _ ?b) _ <> None ] |- _ => destruct b
    end.
    - apply_forall. steps.
    - eapply half_subcontent_in_false_true_le; [ eassumption | steps ]. }
  destruct tree; [ | exfalso; steps ]. .**/
    store(key_out, load(tp + sizeof(uintptr_t)));                          /**.
  (* TODO: (analogous to one in cbt_get_min) figure out why
           enable_frame_trick left here *)
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
    store(val_out, load(tp + 2 * sizeof(uintptr_t)));                      /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**.
  instantiate (1:=Leaf). simpl cbt'. clear Error. steps. subst. steps. .**/
}                                                                          /**.
Qed.

Definition set_bit_at (w: word) (i: Z) := word.or w (/[1] ^<< /[ltac:(bwm1) - i]).

Fixpoint cbt_lookup_trace sk c k :=
  match sk with
  | Node skL skR => set_bit_at
            (if bit_at k (pfx_len (pfx_mmeet c))
            then cbt_lookup_trace skR (half_subcontent c true) k
            else cbt_lookup_trace skL (half_subcontent c false) k)
            (pfx_len (pfx_mmeet c))
  | Leaf => /[0]
  end.

Lemma word_or_0_l : forall w, word.or /[0] w = w.
Proof.
  intros. apply word.unsigned_inj. rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_of_Z_0. apply Z.lor_0_l.
Qed.

Lemma word_or_0_r : forall w, word.or w /[0] = w.
Proof.
  intros. apply word.unsigned_inj. rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_of_Z_0. apply Z.lor_0_r.
Qed.

Lemma word_or_assoc : forall w1 w2 w3,
  word.or w1 (word.or w2 w3) = word.or (word.or w1 w2) w3.
Proof.
  intros. apply word.unsigned_inj. repeat rewrite word.unsigned_or_nowrap.
  apply Z.lor_assoc.
Qed.

#[export] Instance spec_of_cbt_best_with_trace: fnspec :=                       .**/
uintptr_t cbt_best_with_trace(uintptr_t tp, uintptr_t k, uintptr_t trace_out,
                              uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map)
                (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * (EX old_val, uintptr old_val trace_out)
                     * cbt' sk c tp
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t /\ cbt_best_lookup sk c k = res /\
                  <{ * uintptr (cbt_lookup_trace sk c k) trace_out
                     * cbt' sk c tp
                     * (if word.eqb k res then
                         (EX v, <{ * uintptr v val_out
                                   * emp (map.get c k = Some v) }>)
                       else
                         uintptr val_out_orig val_out)
                     * R }> m' #**/                                        /**.
Derive cbt_best_with_trace SuchThat (fun_correct! cbt_best_with_trace)
  As cbt_best_with_trace_ok.       .**/
{                                                                          /**. .**/
  uintptr_t trace = 0;                                                     /**.
  move sk at bottom.
  loop invariant above m.
  move Def0 after t.
  (* introducing `trace` into the postcondition *)
  replace (cbt_lookup_trace sk c k) with (word.or trace (cbt_lookup_trace sk c k))
   by (subst; apply word_or_0_l). .**/
  while (load(tp) != 8 * sizeof(uintptr_t)) /* initial_ghosts(tp,c,trace,R); decreases sk */ {      /*?.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ tp |- _ => pose proof (purify_cbt' _ _ _ _ H);
                                apply cbt_expose_fields in H
  end. steps. destruct sk. { exfalso; steps. } .**/
    trace = trace | (1 << (8 * sizeof(uintptr_t) - 1 - load(tp)));         /**. .**/
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(tp))) & 1) == 1) /* split */ { /**. .**/
      tp = load(tp + 2 * sizeof(uintptr_t));                               /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c true, trace,
      <{ * cbt' sk1 (half_subcontent c false) w2
         * freeable ltac:(wsize3) tp'
         * <{ + uintptr /[pfx_len (pfx_mmeet c)]
              + uintptr w2
              + uintptr tp }> tp'
         * R }>).
  steps.
  { simpl cbt_best_lookup. steps. }
  { simpl cbt_lookup_trace. steps. subst trace. rewrite <- word_or_assoc.
    unfold set_bit_at. f_equal. rewrite word.or_comm. steps.
    rewrite word.ring_morph_sub. f_equal. f_equal. hwlia. }
  { simpl cbt'. clear Error. steps. } .**/
    else {                                                                 /**. .**/
      tp = load(tp + sizeof(uintptr_t));                                   /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c false, trace,
      <{ * cbt' sk2 (half_subcontent c true) w3
         * freeable ltac:(wsize3) tp'
         * <{ + uintptr /[pfx_len (pfx_mmeet c)]
              + uintptr tp
              + uintptr w3 }> tp'
         * R }>).
  steps.
  { simpl cbt_best_lookup. steps. }
  { simpl cbt_lookup_trace. steps. subst trace. rewrite <- word_or_assoc.
    unfold set_bit_at. f_equal. rewrite word.or_comm. steps.
    rewrite word.ring_morph_sub. f_equal. f_equal. hwlia. }
  { simpl cbt'. clear Error. steps. } .**/
  }                                                                        /**.
  destruct sk; [ | exfalso; steps ]. .**/
  store(trace_out, trace);                                                 /**. .**/
  uintptr_t best_k = load(tp + sizeof(uintptr_t));                         /**. .**/
  if (best_k == k) /* split */ {                                           /**. .**/
    store(val_out, load(tp + 2 * sizeof(uintptr_t)));                      /**. .**/
    return best_k;                                                         /**. .**/
  }                                                                        /**.
  { simpl cbt_best_lookup. apply map_some_key_singleton. }
  { simpl cbt_lookup_trace. rewrite word_or_0_r. steps. }
  { simpl cbt'. clear Error. steps. } .**/
  else {                                                                   /**. .**/
    return best_k;                                                         /**. .**/
  }                                                                        /**.
  { simpl cbt_best_lookup. apply map_some_key_singleton. }
  { simpl cbt_lookup_trace. rewrite word_or_0_r. steps. }
  { simpl cbt'. clear Error. steps. } .**/
}                                                                          /**.
Qed.

Fixpoint cbt_max_key sk c :=
  match sk with
  | Leaf => map_some_key c /[0]
  | Node skL skR => cbt_max_key skR (half_subcontent c true)
  end.

Lemma cbt_max_key_in : forall sk c, acbt sk c -> map.get c (cbt_max_key sk c) <> None.
Proof.
  induction sk; cbn; steps.
  - rewrite map_some_key_singleton. steps.
  - eauto using half_subcontent_get_nnone.
Qed.

Lemma cbt_max_key_max : forall sk c k,
  acbt sk c -> map.get c k <> None -> \[k] <= \[cbt_max_key sk c].
Proof.
  induction sk.
  - intros. cbn in *. steps. subst. rewrite map_some_key_singleton. reflexivity.
  - intros.
    match goal with
    | H: map.get _ _ <> None |- _ => apply half_subcontent_get_nNone in H
    end.
    cbn in *. steps. destruct (bit_at k (pfx_len (pfx_mmeet c)));
    eauto using cbt_max_key_in, half_subcontent_in_false_true_le.
Qed.

Lemma Z_testbit_is_bit_at' : forall w i,
  0 <= i < ltac:(bw) -> Z.testbit \[w] (ltac:(bwm1) - i) = bit_at w i.
Proof.
  intros. rewrite Z_testbit_is_bit_at; steps.
Qed.

Lemma bit_at_0 : forall i, 0 <= i < ltac:(bw) -> bit_at /[0] i = false.
Proof.
  intros. rewrite <- Z_testbit_is_bit_at' by lia. steps. apply Z.bits_0.
Qed.

Lemma set_bit_at_bit_at : forall w i i',
  0 <= i < ltac:(bw) -> 0 <= i' < ltac:(bw) ->
  bit_at (set_bit_at w i) i' = bit_at w i' || (i =? i').
Proof.
  intros. do 2 rewrite <- Z_testbit_is_bit_at' by lia. unfold set_bit_at.
  rewrite word.unsigned_or_nowrap. rewrite Z.lor_spec. f_equal.
  rewrite word.unsigned_slu by hwlia. steps. unfold word.wrap.
  rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec by lia. rewrite Z_bits_1.
  lia.
Qed.

Lemma set_bit_at_bit_at' : forall w i i',
  0 <= i < ltac:(bw) -> 0 <= i' < ltac:(bw) ->
  bit_at (set_bit_at w i) i' = if i =? i' then true else bit_at w i'.
Proof.
  intros. rewrite set_bit_at_bit_at by assumption. destruct (i =? i'); steps.
  apply Bool.orb_false_r.
Qed.

Lemma set_bit_at_true : forall w i i',
  0 <= i < ltac:(bw) -> 0 <= i' < ltac:(bw) -> bit_at w i = true ->
  bit_at (set_bit_at w i') i = true.
Proof.
  intros ? ? ? ? ? Hba. rewrite set_bit_at_bit_at by assumption. rewrite Hba.
  apply Bool.orb_true_l.
Qed.

Lemma set_bit_at_bit_at_diff_ix : forall w i i',
  0 <= i < ltac:(bw) -> 0 <= i' < ltac:(bw) -> i' <> i -> bit_at (set_bit_at w i) i' = bit_at w i'.
Proof.
  intros. rewrite set_bit_at_bit_at' by assumption. steps.
Qed.

Lemma set_bit_at_bit_at_same_ix : forall w i,
  0 <= i < ltac:(bw) -> bit_at (set_bit_at w i) i = true.
Proof.
  intros. rewrite set_bit_at_bit_at'; steps.
Qed.

Lemma bit_at_set_true_invert : forall w i i',
  0 <= i < ltac:(bw) -> 0 <= i' < ltac:(bw) ->
  bit_at (set_bit_at w i') i = true -> i = i' \/ bit_at w i = true.
Proof.
  intros ? ? ? ? ? Hba. rewrite set_bit_at_bit_at' in Hba by lia. steps.
  destruct Hba; auto.
Qed.

Lemma cbt_max_key_trace_bits : forall sk c i,
  acbt sk c -> 0 <= i < ltac:(bw) ->
  bit_at (cbt_lookup_trace sk c (cbt_max_key sk c)) i = true ->
  bit_at (cbt_max_key sk c) i = true.
Proof.
  induction sk.
  - steps. cbn in *.
    match goal with
    | H: bit_at _ _ = _ |- _ => rewrite bit_at_0 in H by lia; discriminate
    end.
  - steps. assert (0 <= pfx_len (pfx_mmeet c) < ltac:(bw)) by steps. cbn in *. steps.
    erewrite half_subcontent_in_bit in * by (eauto using cbt_max_key_in). steps.
    match goal with
    | H: bit_at _ _ = _ |- _ => apply bit_at_set_true_invert in H; steps; destruct H
    end.
    + subst. auto using half_subcontent_in_bit, cbt_max_key_in.
    + auto.
Qed.

Lemma cbt_trace_fixes_prefix : forall sk c i k1 k2 bts,
  acbt sk c -> 0 <= i < ltac:(bw) ->
  map.get c k1 <> None ->
  (forall j, 0 <= j <= i -> bit_at (cbt_lookup_trace sk c k1) j = true ->
    bit_at k1 j = bts j) ->
  map.get c k2 <> None ->
  (forall j, 0 <= j <= i -> bit_at (cbt_lookup_trace sk c k2) j = true ->
    bit_at k2 j = bts j) ->
  (forall j, 0 <= j <= i -> bit_at k1 j = bit_at k2 j).
Proof.
  induction sk.
  - steps. cbn in *. steps.
  - intros ? ? ? ? ? ? ? ? Htm1 ? Htm2 ?.
    steps. assert (0 <= pfx_len (pfx_mmeet c) < ltac:(bw)) by steps. cbn in *.
    destruct (Bool.eqb (bit_at k1 (pfx_len (pfx_mmeet c)))
                       (bit_at k2 (pfx_len (pfx_mmeet c)))) eqn:E; steps.
    + destruct (bit_at k1 (pfx_len (pfx_mmeet c))) eqn:E2; symmetry in E.
      * eapply IHsk2 with (bts:=bts) (i:=i); steps.
       -- eassumption.
       -- steps.
       -- apply Htm1; steps. apply set_bit_at_true; steps.
       -- steps.
       -- apply Htm2; steps. apply set_bit_at_true; steps.
      * eapply IHsk1 with (bts:=bts) (i:=i); steps.
       -- eassumption.
       -- steps.
       -- apply Htm1; steps. apply set_bit_at_true; steps.
       -- steps.
       -- apply Htm2; steps. apply set_bit_at_true; steps.
    + assert (i < pfx_len (pfx_mmeet c)).
      { enough (~(pfx_len (pfx_mmeet c) <= i)) by lia.
        intro.
        do 2 match goal with
             | H: forall _, 0 <= _ <= _ -> _ |- _ =>
                  specialize (H (pfx_len (pfx_mmeet c))); prove_ante H; [ lia | ];
                  prove_ante H; [ apply set_bit_at_bit_at_same_ix; lia | ]
             end.
        congruence. }
      assert (Hle1: pfx_le (pfx_mmeet c) (pfx_emb k1)) by steps.
      assert (Hle2: pfx_le (pfx_mmeet c) (pfx_emb k2)) by steps.
      rewrite <- pfx_le_spec in *.
      specialize (Hle1 j). prove_ante Hle1. { lia. }
      specialize (Hle2 j). prove_ante Hle2. { lia. }
      rewrite pfx_emb_spec in * by lia.
      congruence.
Qed.

Lemma cbt_best_lookup_matches_on_trace : forall sk c k i,
  acbt sk c -> 0 <= i < ltac:(bw) -> bit_at (cbt_lookup_trace sk c k) i = true ->
  bit_at (cbt_best_lookup sk c k) i = bit_at k i.
Proof.
  induction sk.
  - cbn in *. steps.
    match goal with
    | H: bit_at _ _ = true |- _ => rewrite bit_at_0 in H; steps
    end.
  - cbn [ cbt_lookup_trace cbt_best_lookup ]. steps.
    destruct (bit_at k (pfx_len (pfx_mmeet c))) eqn:E;
    match goal with
    | H: bit_at (set_bit_at _ _) _ = _ |- _ =>
         apply bit_at_set_true_invert in H; steps; destruct H
    end;
    subst; cbn [ acbt ] in *; steps; auto; rewrite E;
    auto using half_subcontent_in_bit, cbt_best_lookup_in.
Qed.

Lemma cbt_lookup_trace_best : forall sk c k,
  acbt sk c -> cbt_lookup_trace sk c (cbt_best_lookup sk c k) = cbt_lookup_trace sk c k.
Proof.
  induction sk.
  - intros. cbn in *. steps.
  - steps. cbn in *. destruct (bit_at k (pfx_len (pfx_mmeet c))) eqn:E.
    + match goal with
      | |- context [ if ?cond then _ else _ ] => replace cond with true
      end.
      * f_equal. steps. eauto.
      * symmetry. steps. auto using half_subcontent_in_bit, cbt_best_lookup_in.
    + match goal with
      | |- context [ if ?cond then _ else _ ] => replace cond with false
      end.
      * f_equal. steps. eauto.
      * symmetry. steps. auto using half_subcontent_in_bit, cbt_best_lookup_in.
Qed.

Lemma pfx_mmeet_snoc_le_node : forall sk1 sk2 c b,
  acbt (Node sk1 sk2) c ->
  pfx_le (pfx_snoc (pfx_mmeet c) b) (pfx_mmeet (half_subcontent c b)).
Proof.
  intros. apply pfx_mmeet_all_le. { cbn in *. destruct b; steps. }
  intros ? Hget. apply pfx_snoc_ext_le. { apply pfx_mmeet_key_le. steps. }
  apply half_subcontent_in_bit in Hget. rewrite <- Hget. apply pfx_emb_spec. steps.
Qed.

Lemma pfx_mmeet_len_lt_node : forall sk1 sk2 c b,
  acbt (Node sk1 sk2) c ->
  pfx_len (pfx_mmeet c) < pfx_len (pfx_mmeet (half_subcontent c b)).
Proof.
  intros. eassert (Hle: _). { eapply pfx_mmeet_snoc_le_node with (b:=b). eassumption. }
  apply pfx_le_len in Hle. rewrite pfx_snoc_len in Hle. lia.
Qed.

Lemma trace_bit_after_root : forall sk c k i,
  0 <= i < ltac:(bw) -> acbt sk c -> bit_at (cbt_lookup_trace sk c k) i = true ->
  pfx_len (pfx_mmeet c) <= i.
Proof.
  induction sk.
  - cbn in *. steps. exfalso. eassert _. { apply bit_at_0. eassumption. } congruence.
  -  cbn [ cbt_lookup_trace ]. steps.
    match goal with
    | H: bit_at _ _ = true |- _ => apply bit_at_set_true_invert in H; steps;
                                   destruct H as [ ? | Hbt ]
    end.
    + subst. reflexivity.
    + destruct (bit_at k (pfx_len (pfx_mmeet c))).
      * apply IHsk2 in Hbt; steps.
        eassert _. { eapply pfx_mmeet_len_lt_node with (b:=true). eassumption. } lia.
        cbn in *. steps.
      * apply IHsk1 in Hbt; steps.
        eassert _. { eapply pfx_mmeet_len_lt_node with (b:=false). eassumption. } lia.
        cbn in *. steps.
Qed.

Lemma pfx_le_emb_bit_same_prefix : forall p w1 w2 i,
  pfx_le p (pfx_emb w1) -> pfx_le p (pfx_emb w2) -> 0 <= i < pfx_len p ->
  bit_at w1 i = bit_at w2 i.
Proof.
  intros ? ? ? ? Hle1 Hle2 Hrng.
  assert (pfx_len p <= ltac:(bw)). { apply pfx_le_len in Hle1. steps. }
  enough (pfx_bit (pfx_emb w1) i = pfx_bit (pfx_emb w2) i).
  { do 2 rewrite pfx_emb_spec in * by lia. steps. }
  rewrite <- pfx_le_spec in *.
  specialize (Hle1 i). specialize (Hle2 i). steps. congruence.
Qed.

Lemma pfx_meet_emb_bit_at_eq : forall w1 w2 i,
  0 <= i < pfx_len (pfx_meet (pfx_emb w1) (pfx_emb w2)) ->
  bit_at w1 i = bit_at w2 i.
Proof.
  intros. eapply pfx_le_emb_bit_same_prefix; try eassumption; steps.
Qed.

Lemma map_filter_empty : forall f, map_filter map.empty f = map.empty.
Proof.
  unfold map_filter. auto using map.fold_empty.
Qed.

Lemma map_filter_get_pred_true : forall c f k,
  f k = true -> map.get (map_filter c f) k = map.get c k.
Proof.
  intros ? ? ? Hpred. rewrite map_filter_get. rewrite Hpred. reflexivity.
Qed.

Lemma map_filter_get_pred_false : forall c f k,
  f k = false -> map.get (map_filter c f) k = None.
Proof.
  intros ? ? ? Hpred. rewrite map_filter_get. rewrite Hpred. reflexivity.
Qed.

Lemma map_filter_get_none : forall c f k,
  map.get c k = None -> map.get (map_filter c f) k = None.
Proof.
  intros. rewrite map_filter_get. destruct (f k); steps.
Qed.

Definition map_take_ge c k := map_filter c (fun k' => \[k] <=? \[k']).
Definition map_take_gt c k := map_filter c (fun k' => \[k] <? \[k']).

Lemma map_take_ge_empty : forall k, map_take_ge map.empty k = map.empty.
Proof.
  intros. apply map_filter_empty.
Qed.

Lemma map_take_ge_get_ge : forall c k k',
  \[k] <= \[k'] -> map.get (map_take_ge c k) k' = map.get c k'.
Proof.
  intros. unfold map_take_ge. rewrite map_filter_get_pred_true; steps.
Qed.

Definition map_all_get_none_empty : forall c : word_map,
  (forall k, map.get c k = None) -> c = map.empty.
Proof.
  intros. apply map.map_ext. steps. auto.
Qed.

Lemma map_filter_eq_empty : forall c f,
  (forall k, map.get c k <> None -> f k = false) -> map_filter c f = map.empty.
Proof.
  intros. apply map_all_get_none_empty. intros.
  none_nnone_cases (map.get c k).
  - apply map_filter_get_none. assumption.
  - auto using map_filter_get_pred_false.
Qed.

Lemma map_take_ge_eq_empty : forall c k,
  (forall k', map.get c k' <> None -> \[k'] < \[k]) -> map_take_ge c k = map.empty.
Proof.
  intros ? ? Hsm. unfold map_take_ge. apply map_filter_eq_empty. intros k'' Hnn.
  specialize (Hsm k'' Hnn). lia.
Qed.

Lemma map_filter_get_nnone_ftrue : forall c f k,
  map.get (map_filter c f) k <> None -> f k = true.
Proof.
  intros. rewrite map_filter_get in *. destruct (f k); steps.
Qed.

Lemma map_take_ge_get_nnone : forall c k k',
  map.get (map_take_ge c k) k' <> None -> \[k] <= \[k'].
Proof.
  unfold map_take_ge. intros ? ? ? Hnn. apply map_filter_get_nnone_ftrue in Hnn. lia.
Qed.

Lemma map_take_ge_get_nnone' : forall c k k',
  \[k] <= \[k'] -> map.get c k' <> None -> map.get (map_take_ge c k) k' <> None.
Proof.
  intros. rewrite map_take_ge_get_ge; assumption.
Qed.

Lemma map_filter_monotone : forall c c' f,
  map.extends c c' -> map.extends (map_filter c f) (map_filter c' f).
Proof.
  intros ? ? ? Hext. unfold map.extends. intros k v Hsm. rewrite map_filter_get in *.
  destruct (f k); [ | discriminate ]. eauto using map.extends_get.
Qed.

Lemma map_take_ge_monotone : forall c c' k,
  map.extends c c' -> map.extends (map_take_ge c k) (map_take_ge c' k).
Proof.
  unfold map_take_ge. auto using map_filter_monotone.
Qed.

Lemma map_take_ge_extends : forall c k,
  map.extends c (map_take_ge c k).
Proof.
  unfold map_take_ge. auto using map_filter_extends.
Qed.

Definition map_size (c: word_map) := map.fold (fun n _ _ => n + 1) 0 c.

Lemma map_size_empty1 : map_size map.empty = 0.
Proof.
  apply map.fold_empty.
Qed.

Lemma map_size_empty1_eq : forall c, c = map.empty -> map_size c = 0.
Proof.
  intros. subst. apply map_size_empty1.
Qed.

Lemma map_size_empty2 : forall c, map_size c = 0 -> c = map.empty.
Proof.
  intros c.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m n => n >= 0 /\ (n = 0 -> m = map.empty)) (m:=c).
  3: exact (proj2 HP).
  { split; [ lia | trivial ]. }
  steps.
Qed.

Lemma map_size_nonneg : forall c, map_size c >= 0.
Proof.
  intros c.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m n => n >= 0) (m:=c).
  3: exact HP.
  all: steps.
Qed.

Definition map_is_emptyb c := map_size c =? 0.

Lemma map_is_emptyb_reflects : forall c, map_is_emptyb c = true <-> c = map.empty.
Proof.
  intros. unfold map_is_emptyb. rewrite Z.eqb_eq.
  split; auto using map_size_empty1_eq, map_size_empty2.
Qed.


Instance map_empty_dec (c : word_map) : Decidable (c = map.empty) := {
  Decidable_spec := map_is_emptyb_reflects c
}.

Definition map_min_key_value (c: word_map) : option (word * word) := map.fold
  (fun cur k v => match cur with
                  | Some (k', _) => if \[k] <? \[k'] then Some (k, v) else cur
                  | None => Some (k, v)
                  end) None c.

Lemma map_min_key_value_in : forall c k v,
  map_min_key_value c = Some (k, v) ->
  map.get c k = Some v.
Proof.
  intros ? ? ? Heq.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => forall k v, state = Some (k, v) -> map.get m k = Some v).
  all: cycle 2. { eauto. } all: purge c; purge k; purge v; steps.
  cbn in *. destruct r as [ [ rk rv ] | ].
  - destruct (\[k] <? \[rk]) eqn:E; steps; subst.
    match goal with
    | H: forall _, _ |- _ => specialize (H k0 v0); prove_ante H; steps
    end.
    rewrite map.get_put_diff; [ assumption | ]. intro; congruence.
  - steps.
Qed.

Lemma map_min_key_value_none_empty : forall c,
  map_min_key_value c = None -> c = map.empty.
Proof.
  intros ?.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => state = None -> m = map.empty).
  all: cycle 2. { eassumption. }
  all: steps. cbn in *. destruct r; steps; destruct (\[k] <? \[r]); steps.
Qed.

Lemma map_min_key_value_key_le : forall c k v k',
  map_min_key_value c = Some (k, v) ->
  map.get c k' <> None ->
  \[k] <= \[k'].
Proof.
  intros ? ? ? ? Heq Hget'.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => (state = None -> m = map.empty) /\
      (forall k v k', state = Some (k, v) -> map.get m k' <> None -> \[k] <= \[k'])).
  all: cycle 2. { apply proj2 in HP. eauto. }
  all: purge c; purge k; purge v; purge k'; steps.
  { match goal with
    | H: context [ if ?cond then _ else _ ] |- _ => destruct cond; steps
    end. }
  destruct r as [ [ rk rv ] | ].
  - match goal with
    | H: forall _, _ |- _ => specialize (H rk rv); rename H into IH
    end.
    eq_neq_cases k k';
    [ subst k' | specialize (IH k'); prove_ante IH; [ reflexivity | ] ];
    destruct (\[k] <? \[rk]) eqn:E; steps; subst; steps.
  - steps. subst. steps.
Qed.

Lemma map_min_key_value_eq : forall c k v,
  map.get c k = Some v ->
  (forall k', map.get c k' <> None -> \[k] <= \[k']) ->
  map_min_key_value c = Some (k, v).
Proof.
  intros ? ? ? Hget Hleast. destruct (map_min_key_value c) as [ [ mnk mnv ] | ] eqn:E.
  - specialize (Hleast mnk).
    pose proof E as Hmnin. apply map_min_key_value_in in Hmnin.
    prove_ante Hleast. { steps. }
    eapply map_min_key_value_key_le in E; [ | rewrite Hget ]; steps.
    assert (mnk = k); steps. subst. congruence.
  - apply map_min_key_value_none_empty in E. steps.
Qed.

Lemma map_min_key_value_take_ge_has_min : forall c k v,
  map.get c k = Some v -> map_min_key_value (map_take_ge c k) = Some (k, v).
Proof.
  intros c k v Hin.
  apply map_min_key_value_eq.
  - rewrite map_take_ge_get_ge; steps.
  - intros k' Hink'. eauto using map_take_ge_get_nnone.
Qed.

Lemma some_not_none : forall (X : Type) (x : X) o, o = Some x -> o <> None.
Proof.
  intros. destruct o; [ intro | ]; discriminate.
Qed.

#[export] Instance spec_of_cbt_next_ge_impl_uptrace: fnspec :=                .**/
void cbt_next_ge_impl_uptrace(uintptr_t tp, uintptr_t k, uintptr_t i,
                                 uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map) (cb: Z) (R: mem -> Prop);
  requires t m :=
    cb = pfx_len (pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k)))
    /\ 0 <= cb < ltac:(bw)
    /\ 0 <= \[i] < cb
    /\ k <> cbt_best_lookup sk c k
    /\ (forall j, \[i] + 1 <= j < pfx_len
                                   (pfx_meet
                                     (pfx_emb k)
                                     (pfx_emb (cbt_best_lookup sk c k))) ->
          bit_at (cbt_lookup_trace sk c k) j = true ->
          bit_at k j = true)
    /\ bit_at (cbt_lookup_trace sk c k) \[i] = true
    /\ bit_at k \[i] = false
    /\ bit_at (cbt_best_lookup sk c k) cb = false
    /\ bit_at k cb = true
    /\ <{ * cbt' sk c tp
          * (EX k0, uintptr k0 key_out)
          * (EX v0, uintptr v0 val_out)
          * R }> m;
  ensures t' m' := t' = t
           /\ <{ * cbt' sk c tp
                 * (EX k_res v_res,
                    <{ * emp (map_min_key_value (map_take_ge c k) = Some (k_res, v_res))
                       * uintptr k_res key_out
                       * uintptr v_res val_out }>)
                 * R }> m' #**/                                            /**.
Derive cbt_next_ge_impl_uptrace SuchThat (fun_correct! cbt_next_ge_impl_uptrace)
  As cbt_next_ge_impl_uptrace_ok.                                                .**/
{                                                                          /**.
  loop invariant above m.
  move sk at bottom.
  prove (pfx_len (pfx_mmeet c) <= \[i]).
  { eapply trace_bit_after_root; steps; eassumption. }
  assert (bit_at (cbt_lookup_trace sk c k) \[i] = true) by steps. .**/
  while (load(tp) < i) /* initial_ghosts(tp,c,R); decreases sk */ { /*?.
  repeat heapletwise_step.
  subst v.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct sk. { exfalso. steps. } repeat heapletwise_step. .**/
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(tp))) & 1) == 1) /* split */ { /**. .**/
      tp = load(tp + 2 * sizeof(uintptr_t));                               /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c true,
    <{ * cbt' sk1 (half_subcontent c false) w2
       * freeable ltac:(wsize3) tp'
       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
            + uintptr w2
            + uintptr tp }> tp'
       * R }>). steps; simpl cbt_best_lookup in *; try steps.
  { apply_forall. steps. simpl cbt_lookup_trace. steps.
    rewrite set_bit_at_bit_at_diff_ix by steps. steps. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps.
    eapply trace_bit_after_root; steps; eassumption. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps. }
  simpl cbt'. clear Error. steps.
  { apply map_min_key_value_eq.
    - match goal with
      | H: map_min_key_value _ = Some _ |- _ => apply map_min_key_value_in in H
      end.
      eauto using map_take_ge_monotone, map.extends_get, half_subcontent_extends.
    - intros k' Hink'. destruct (bit_at k' (pfx_len (pfx_mmeet c))) eqn:E.
      + eapply map_min_key_value_key_le; [ eassumption | ].
        apply map_take_ge_get_nnone'.
        * eauto using map_take_ge_get_nnone.
        * rewrite <- E. apply half_subcontent_get_nNone.
          eauto using map_extends_get_nnone, map_take_ge_extends.
      + exfalso. enough (\[k'] < \[k]) by (apply map_take_ge_get_nnone in Hink'; lia).
        eapply bit_at_lt with (i:=pfx_len (pfx_mmeet c)); steps.
        transitivity (bit_at (cbt_best_lookup sk2 (half_subcontent c true) k) j).
        * assert (pfx_len (pfx_mmeet c)
           <= pfx_len (pfx_meet
                        (pfx_emb k')
                        (pfx_emb (cbt_best_lookup sk2 (half_subcontent c true) k)))).
          { apply pfx_le_len. apply pfx_meet_le_both.
            - eauto using pfx_mmeet_key_le, map_extends_get_nnone, map_take_ge_extends.
            - eauto using pfx_mmeet_key_le, map_extends_get_nnone,
                          half_subcontent_extends, cbt_best_lookup_in. }
          apply pfx_meet_emb_bit_at_eq. lia.
        * apply pfx_meet_emb_bit_at_eq. rewrite pfx_meet_comm. lia. } .**/
     else {                                                                /**. .**/
       tp = load(tp + sizeof(uintptr_t));                                  /**. .**/
     }                                                                     /**.
  new_ghosts(tp, half_subcontent c false,
    <{ * cbt' sk2 (half_subcontent c true) w3
       * freeable ltac:(wsize3) tp'
       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
            + uintptr tp
            + uintptr w3 }> tp'
       * R }>). steps; simpl cbt_best_lookup in *; try steps.
  { apply_forall. steps. simpl cbt_lookup_trace. steps.
    rewrite set_bit_at_bit_at_diff_ix by steps. steps. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps.
    eapply trace_bit_after_root; steps; eassumption. }
  { simpl cbt_lookup_trace in *. steps.
    rewrite set_bit_at_bit_at_diff_ix in * by steps. steps. }
  simpl cbt'. clear Error. steps.
  { apply map_min_key_value_eq.
    - eauto using map_take_ge_monotone, map_min_key_value_in, map.extends_get,
                  half_subcontent_extends.
    - intros k' Hink'. destruct (bit_at k' (pfx_len (pfx_mmeet c))) eqn:E.
      + eapply bit_at_le with (i:=pfx_len (pfx_mmeet c)); steps.
        assert (pfx_len (pfx_mmeet c) <=
                  pfx_len (pfx_meet (pfx_emb k_res) (pfx_emb k'))).
        { apply pfx_le_len. apply pfx_meet_le_both. apply pfx_mmeet_key_le.
          eapply map_extends_get_nnone. apply (half_subcontent_extends _ false).
          eapply map_extends_get_nnone. apply map_take_ge_extends.
          erewrite map_min_key_value_in; [ | eassumption ]. steps.
          eauto using pfx_mmeet_key_le, map_extends_get_nnone, map_take_ge_extends. }
        apply pfx_meet_emb_bit_at_eq. lia.
        match goal with
        | H: map_min_key_value _ = Some _ |- _ => apply map_min_key_value_in in H
        end.
        apply half_subcontent_in_bit. eapply some_not_none.
        eauto using map_take_ge_extends, map.extends_get.
      + eapply map_min_key_value_key_le; [ eassumption | ]. apply map_take_ge_get_nnone'.
        eauto using map_take_ge_get_nnone.
        rewrite <- E. apply half_subcontent_get_nNone.
        eauto using map_extends_get_nnone, map_take_ge_extends. } .**/
  }                                                                        /**.
  assert (Hieq: pfx_len (pfx_mmeet c) = \[i]) by lia. rewrite <- Hieq in *.
  destruct sk. { exfalso; steps. } .**/
  tp = load(tp + 2 * sizeof(uintptr_t));                                   /**. .**/
  cbt_get_min_impl(tp, key_out, val_out);                                  /**. .**/
}                                                                          /**.
  simpl cbt'. clear Error. steps.
  { apply map_min_key_value_eq. rewrite map_take_ge_get_ge.
    - eauto using map.extends_get, half_subcontent_extends.
    - apply bit_at_le with (i:=pfx_len (pfx_mmeet c)); steps.
      + transitivity (bit_at (cbt_best_lookup (Node sk1 sk2) c k) j).
        * apply pfx_meet_emb_bit_at_eq. lia.
        * apply pfx_meet_emb_bit_at_eq.
          assert (Hpfxle: pfx_le
                            (pfx_mmeet c)
                            (pfx_meet
                              (pfx_emb (cbt_best_lookup (Node sk1 sk2) c k))
                              (pfx_emb k1))).
          { apply pfx_meet_le_both. apply pfx_mmeet_key_le. steps.
            apply pfx_mmeet_key_le. eapply map_extends_get_nnone.
            apply (half_subcontent_extends _ true). steps. }
          apply pfx_le_len in Hpfxle. steps.
      + rewrite half_subcontent_get in *. steps.
    - intros k' Hink'. destruct (bit_at k' (pfx_len (pfx_mmeet c))) eqn:E.
      + apply_forall. rewrite <- E.
        eauto using half_subcontent_get_nNone, map_extends_get_nnone,
                    map_take_ge_extends.
      + exfalso. enough (\[cbt_max_key sk1 (half_subcontent c false)] < \[k]).
        * assert (\[k'] <= \[cbt_max_key sk1 (half_subcontent c false)]).
          { apply cbt_max_key_max; steps.
            eauto using half_subcontent_get_nNone, map_extends_get_nnone,
                    map_take_ge_extends. }
          match goal with
          | H: map.get (map_take_ge _ _) _ <> None |- _ =>
               apply map_take_ge_get_nnone in H
          end. lia.
        * apply bit_at_lt with (i:=cb). { steps. } steps.
          transitivity (bit_at (cbt_best_lookup sk1 (half_subcontent c false) k) j).
          { eapply cbt_trace_fixes_prefix with
              (bts:=fun _ => true) (sk:=sk1) (c:=half_subcontent c false) (i:=cb); steps.
            - apply cbt_max_key_in. steps.
            - apply cbt_max_key_trace_bits; steps.
            - destruct (j0 =? cb) eqn:E2; steps. { exfalso. subst j0.
              rewrite cbt_lookup_trace_best in * by steps.
              pose proof (pfx_meet_emb_bit_at_len
                           k
                           (cbt_best_lookup sk1 (half_subcontent c false) k)) as Hbneq.
              prove_ante Hbneq. simpl cbt_best_lookup in *. steps.
              apply_ne. symmetry. apply cbt_best_lookup_matches_on_trace; steps.
              simpl cbt_best_lookup in *. steps. simpl cbt_best_lookup in *. steps.
              congruence. }
              transitivity (bit_at k j0).
              apply pfx_meet_emb_bit_at_eq. simpl cbt_best_lookup in *. steps.
              subst cb. rewrite pfx_meet_comm. steps.
              simpl cbt_best_lookup in *. steps.
              match goal with
              | H: forall _, _ -> _ -> bit_at _ _ = true |- _ => apply H
              end.
              enough (pfx_len (pfx_mmeet c) + 1 <= j0). {
                subst cb. simpl cbt_best_lookup in *. steps. }
              rewrite cbt_lookup_trace_best in * by steps.
              match goal with
              | H: bit_at (cbt_lookup_trace _ _ _) _ = true |- _ =>
                   apply trace_bit_after_root in H; steps
              end.
              enough (pfx_len (pfx_mmeet c) <
                        pfx_len (pfx_mmeet (half_subcontent c false))) by lia.
              apply pfx_mmeet_len_lt_node with (sk1:=sk1) (sk2:=sk2). simpl. steps.
              rewrite cbt_lookup_trace_best in * by steps.
              simpl cbt_lookup_trace. steps. apply set_bit_at_true; steps. }
          { apply pfx_meet_emb_bit_at_eq. simpl cbt_best_lookup in *. steps.
            rewrite pfx_meet_comm. steps. }
          { steps. simpl cbt_best_lookup in *. steps.
            match goal with
            | H: bit_at (cbt_best_lookup _ _ _) _ = false |- _ => rewrite <- H at 2
            end.
            eapply cbt_trace_fixes_prefix with
              (bts:=fun _ => true) (sk:=sk1) (c:=half_subcontent c false) (i:=cb); steps.
            { apply cbt_max_key_in; steps. }
            { apply cbt_max_key_trace_bits; steps. }
            { destruct (j =? cb) eqn:E2; steps. { exfalso. subst j.
                rewrite cbt_lookup_trace_best in * by steps.
                pose proof (pfx_meet_emb_bit_at_len
                             k
                             (cbt_best_lookup sk1 (half_subcontent c false) k)) as Hbneq.
                prove_ante Hbneq. simpl cbt_best_lookup in *. steps.
                apply_ne. symmetry. apply cbt_best_lookup_matches_on_trace; steps.
                simpl cbt_best_lookup in *. steps. congruence. }
                transitivity (bit_at k j).
                apply pfx_meet_emb_bit_at_eq.
                subst cb. rewrite pfx_meet_comm. steps.
                match goal with
                | H: forall _, _ -> _ -> bit_at _ _ = true |- _ => apply H
                end.
                enough (pfx_len (pfx_mmeet c) + 1 <= j) by steps.
                rewrite cbt_lookup_trace_best in * by steps.
                match goal with
                | H: bit_at (cbt_lookup_trace _ _ _) _ = true |- _ =>
                     apply trace_bit_after_root in H; steps
                end.
                enough (pfx_len (pfx_mmeet c) <
                          pfx_len (pfx_mmeet (half_subcontent c false))) by lia.
                apply pfx_mmeet_len_lt_node with (sk1:=sk1) (sk2:=sk2). simpl. steps.
                rewrite cbt_lookup_trace_best in * by steps.
                simpl cbt_lookup_trace. steps. apply set_bit_at_true; steps. } }
          { steps. } }
Qed.

Create HintDb content_maps.

Hint Resolve map_take_ge_get_nnone map_take_ge_get_nnone'
             map_take_ge_monotone map_take_ge_extends
             half_subcontent_extends
             map.extends_get map_extends_get_nnone
             half_subcontent_get_nNone
             map_min_key_value_in
             some_not_none
  : content_maps.

#[export] Instance spec_of_cbt_next_ge_impl_at_cb: fnspec :=                    .**/
void cbt_next_ge_impl_at_cb(uintptr_t tp, uintptr_t k, uintptr_t cb,
                                 uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (c: word_map) (R: mem -> Prop);
  requires t m :=
    \[cb] = pfx_len (pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k)))
    /\ 0 <= \[cb] < ltac:(bw)
    /\ k <> cbt_best_lookup sk c k
    /\ bit_at (cbt_best_lookup sk c k) \[cb] = true
    /\ bit_at k \[cb] = false
    /\ <{ * cbt' sk c tp
          * (EX k0, uintptr k0 key_out)
          * (EX v0, uintptr v0 val_out)
          * R }> m;
  ensures t' m' := t' = t
           /\ <{ * cbt' sk c tp
                 * (EX k_res v_res,
                    <{ * emp (map_min_key_value (map_take_ge c k) = Some (k_res, v_res))
                       * uintptr k_res key_out
                       * uintptr v_res val_out }>)
                 * R }> m' #**/                                            /**.
Derive cbt_next_ge_impl_at_cb SuchThat (fun_correct! cbt_next_ge_impl_at_cb)
  As cbt_next_ge_impl_at_cb_ok.                                                 .**/
{                                                                          /**.
  loop invariant above m.
  move sk at bottom. .**/
  while (load(tp) < cb) /* initial_ghosts(tp,c,R); decreases sk */ { /*?.
  repeat heapletwise_step.
  subst v.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct sk. { exfalso. steps. } repeat heapletwise_step. .**/
    if (((k >> (8 * sizeof(uintptr_t) - 1 - load(tp))) & 1) == 1) /* split */ { /**. .**/
      tp = load(tp + 2 * sizeof(uintptr_t));                               /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c true,
    <{ * cbt' sk1 (half_subcontent c false) w2
       * freeable ltac:(wsize3) tp'
       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
            + uintptr w2
            + uintptr tp }> tp'
       * R }>).
  steps; simpl cbt_best_lookup in *; try steps.
  { clear Error. simpl cbt'. steps. apply map_min_key_value_eq.
    - eauto with content_maps.
    - intros k' Hink'. destruct (bit_at k' (pfx_len (pfx_mmeet c))) eqn:E.
      + eapply map_min_key_value_key_le; [ eassumption | ].
        apply map_take_ge_get_nnone'.
        * eauto with content_maps.
        * rewrite <- E. eauto with content_maps.
      + exfalso. enough (\[k'] < \[k]) by (apply map_take_ge_get_nnone in Hink'; lia).
        apply bit_at_lt with (pfx_len (pfx_mmeet c)); steps.
        transitivity (bit_at (cbt_best_lookup (Node sk1 sk2) c k) j).
        * apply pfx_le_emb_bit_same_prefix with (pfx_mmeet c); steps.
          apply pfx_mmeet_key_le. eauto with content_maps.
          apply pfx_mmeet_key_le. steps.
        * simpl cbt_best_lookup. steps. apply pfx_meet_emb_bit_at_eq.
        rewrite pfx_meet_comm. lia. } .**/
    else {                                                                 /**. .**/
      tp = load(tp + sizeof(uintptr_t));                                   /**. .**/
    }                                                                      /**.
  new_ghosts(tp, half_subcontent c false,
    <{ * cbt' sk2 (half_subcontent c true) w3
       * freeable ltac:(wsize3) tp'
       * <{ + uintptr /[pfx_len (pfx_mmeet c)]
            + uintptr tp
            + uintptr w3 }> tp'
       * R }>). steps; simpl cbt_best_lookup in *; try steps.
  { clear Error. simpl cbt'. steps.
    apply map_min_key_value_eq.
    - eauto with content_maps.
    - intros k' Hink'. destruct (bit_at k' (pfx_len (pfx_mmeet c))) eqn:E.
      + apply half_subcontent_in_false_true_le with (c:=c); steps;
        eauto with content_maps.
      + eapply map_min_key_value_key_le; [ eassumption | ]. rewrite <- E.
        eauto with content_maps. } .**/
  }                                                                        /**. .**/
  cbt_get_min_impl(tp, key_out, val_out);                                  /**.
  clear Error. instantiate (3:=c). instantiate (3:=sk).
  unfold canceling. steps. unfold seps. destruct sk; simpl cbt'; steps.
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
}                                                                          /**.
  destruct (\[cb] =? pfx_len (pfx_mmeet c)) eqn:E. {
    exfalso. destruct sk; steps. simpl cbt_best_lookup in *.
    match goal with
    | H: \[cb] = _ |- _ => rewrite H in *
    end. steps.
    assert (Hwrh: map.get (half_subcontent c false)
                    (cbt_best_lookup sk1 (half_subcontent c false) k) <> None) by steps.
    rewrite half_subcontent_get in Hwrh. steps. }
  steps.
  { apply map_min_key_value_eq.
    - rewrite map_take_ge_get_ge. { eauto with content_maps. }
      apply bit_at_le with \[cb]; steps.
      + transitivity (bit_at (cbt_best_lookup sk c k) j).
        * apply pfx_meet_emb_bit_at_eq. steps.
        * apply pfx_le_emb_bit_same_prefix with (pfx_mmeet c); steps.
          apply pfx_mmeet_key_le. steps.
      + transitivity (bit_at (cbt_best_lookup sk c k) \[cb]).
        * apply pfx_le_emb_bit_same_prefix with (pfx_mmeet c); steps.
          apply pfx_mmeet_key_le. steps.
        * destruct (bit_at (cbt_best_lookup sk c k) \[cb]) eqn:E2; steps.
    - intros k' Hink'. apply_forall. eauto with content_maps. }
Qed.


#[export] Instance spec_of_cbt_next_ge: fnspec :=                                .**/
uintptr_t cbt_next_ge(uintptr_t tp, uintptr_t k,
                      uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (key_out_orig: word) (val_out_orig: word)
                (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr key_out_orig key_out
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
        /\ <{ * cbt c tp
              * (if decide (map_take_ge c k = map.empty) then
                   <{ * uintptr key_out_orig key_out
                      * uintptr val_out_orig val_out
                      * emp (res = /[0]) }>
                 else
                   (EX k_res v_res,
                     <{ * emp (map_min_key_value (map_take_ge c k) = Some (k_res, v_res))
                        * uintptr k_res key_out
                        * uintptr v_res val_out
                        * emp (res = /[1]) }>))
                 * R }> m'         #**/                                    /**.
Derive cbt_next_ge SuchThat (fun_correct! cbt_next_ge) As cbt_next_ge_ok.       .**/
{                                                                          /**.
  unfold cbt, nncbt in *. .**/
  if (tp == 0) /* split */ {                                               /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
  rewrite map_take_ge_empty. rewrite Decidable_complete by reflexivity. steps. .**/
  else {                                                                   /**. .**/
    uintptr_t orig_in_key_out = load(key_out);                             /**. .**/
    uintptr_t best_k = cbt_best_with_trace(tp, k, key_out, val_out);       /**.
  (* FIXME: removing orphaned heaplet from before the function call
            (it should've been removed automatically) *)
  match goal with
  | H: ?m |= uintptr val_out_orig val_out |- _ => purge m
  end. .**/
    if (best_k == k) /* split */ {                                         /**. .**/
      store(key_out, k);                                                   /**. .**/
      return 1;                                                            /**. .**/
    }                                                                      /**.
  rewrite Decidable_sound_alt; steps.
  auto using map_min_key_value_take_ge_has_min.
  apply map_get_nnone_nonempty with (k:=k).
  rewrite map_take_ge_get_ge; subst; steps. .**/
    else {                                                                 /**. .**/
      uintptr_t trace = load(key_out);                                     /**. .**/
      uintptr_t cb = critical_bit(best_k, k);                              /**.
  instantiate (3:=emp True). steps. .**/
      if (((k >> (8 * sizeof(uintptr_t) - 1 - cb)) & 1) == 1) /* split */ { /**. .**/
        uintptr_t i = cb - 1;                                              /**.
  prove (forall j,
    (\[i ^+ /[1]] <= j < \[cb]) -> bit_at trace j = true -> bit_at k j = true).
  prove (\[cb] <= \[i] -> i = /[-1]).
  delete #(i = cb ^- ??).
  loop invariant above i. .**/
        while (i != -1 &&
          (((trace >> (8 * sizeof(uintptr_t) - 1 - i)) & 1) != 1
             || ((k >> (8 * sizeof(uintptr_t) - 1 - i)) & 1) == 1))
          /* decreases (i ^+ /[1]) */ {                                    /**. .**/
          i = i - 1;                                                       /**. .**/
        }                                                                  /**.
  assert (Hor: j = \[i'] \/ \[i'] + 1 <= j) by hwlia. destruct Hor.
  { match goal with
    | H: word.and _ _ <> _ \/ word.and _ _ = _ |- _ => destruct H
    end; steps. congruence. }
  apply_forall; steps.
  (* FIXME: again, shouldn't be clearing this *)
  purge m'. purge m0. purge m2. purge m3. purge m4.
  (* FIXME: should this v still be around in the first place? *)
  purge v.
  .**/
        if (i == -1) /* split */ {                                         /**. .**/
          store(key_out, orig_in_key_out);                                 /**. .**/
          return 0;                                                        /**. .**/
        }                                                                  /**.
  rewrite Decidable_complete; cycle 1. apply map_take_ge_eq_empty.
  steps.
  assert (\[k'] <= \[cbt_max_key tree c]) by (apply cbt_max_key_max; steps).
  enough (\[cbt_max_key tree c] < \[k]) by lia. purge k'.
  assert (forall j, 0 <= j <= \[cb] ->
    bit_at (cbt_max_key tree c) j = bit_at best_k j).
  { symmetry. eapply cbt_trace_fixes_prefix with (bts:=(fun _ => true)).
    - eassumption.
    - eassumption.
    - subst; steps.
    - steps. subst.
      match goal with
      | H: context [ cbt_lookup_trace _ _ (cbt_best_lookup _ _ _) ] |- _ =>
           rewrite cbt_lookup_trace_best in H
      end.
      assert (Hor: j0 = \[cb] \/ j0 < \[cb]) by lia. destruct Hor.
      + subst.
        match goal with
        | H: \[cb] = _ |- _ => rewrite H in *
        end.
        match goal with
        | H: bit_at (cbt_lookup_trace _ _ _) _ = true |- _ => rename H into Hbt
        end.
        apply cbt_best_lookup_matches_on_trace in Hbt; steps.
        apply pfx_meet_emb_bit_at_len in Hbt; steps.
      + replace (bit_at (cbt_best_lookup tree c k) j0) with (bit_at k j0).
        apply_forall; steps. symmetry. apply cbt_best_lookup_matches_on_trace; steps.
      + steps.
    - apply cbt_max_key_in; steps.
    - steps. apply cbt_max_key_trace_bits; steps.
    - steps. }
  apply bit_at_lt with (i:=\[cb]); steps.
  { match goal with
    | H: forall _, _ |- _ => rewrite H; clear H
    end.
    apply pfx_meet_emb_bit_at_eq. steps. steps. }
  { match goal with
    | H: forall _, _ -> bit_at _ _ = bit_at _ _ |- _ => rewrite H; clear H
    end.
    subst. pose proof (pfx_meet_emb_bit_at_len (cbt_best_lookup tree c k) k) as Hb.
    prove_ante Hb. steps.
    match goal with
    | H: \[cb] = _ |- _ => rewrite H in *
    end.
    match goal with
    | |- ?v = false => destruct v eqn:E
    end; steps.
    - congruence.
    - steps. } steps. .**/
        else {                                                             /**.
  destruct_or. congruence. fwd. .**/
          cbt_next_ge_impl_uptrace(tp, k, i, key_out, val_out);            /**.
  { rewrite pfx_meet_comm. subst. steps. }
  { rewrite pfx_meet_comm. subst. steps. }
  { apply_forall. subst. steps.
    match goal with
    | H: \[i] + 1 <= j < pfx_len _ |- _ => rewrite pfx_meet_comm in H
    end. steps. subst. steps. }
  { subst. steps. }
  { subst. steps. rewrite pfx_meet_comm.
    pose proof (pfx_meet_emb_bit_at_len (cbt_best_lookup tree c k) k) as Hbneq.
    prove_ante Hbneq. steps.
    match goal with
    | |- ?v = false => destruct v eqn:E; steps; congruence
    end. }
  { rewrite pfx_meet_comm. congruence. } .**/
          return 1;                                                        /**. .**/
        }                                                                  /**.
  rewrite Decidable_sound_alt. steps.
  eauto using map_get_nnone_nonempty with content_maps. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        cbt_next_ge_impl_at_cb(tp, k, cb, key_out, val_out);               /**.
  { subst. rewrite pfx_meet_comm. steps. }
  { match goal with
    | |- ?v = true => destruct v eqn:E; steps
    end.
    exfalso. apply (pfx_meet_emb_bit_at_len (cbt_best_lookup tree c k) k); steps.
    congruence. } .**/
        return 1;                                                           /**. .**/
      }                                                                     /**.
  rewrite Decidable_sound_alt. steps.
  eauto using map_get_nnone_nonempty with content_maps. .**/
    }                                                                       /**. .**/
  }                                                                         /**. .**/
}                                                                           /**.
Qed.

Lemma map_filter_impossible : forall c f,
  (forall k, f k = false) -> map_filter c f = map.empty.
Proof.
  auto using map_filter_eq_empty.
Qed.

Lemma map_take_gt_max : forall c, map_take_gt c (word.opp /[1]) = map.empty.
Proof.
  intros. apply map_filter_impossible. intros. hwlia.
Qed.

Lemma map_take_gt_get_gt : forall (c : word_map) (k k' : word),
  \[k] < \[k'] -> map.get (map_take_gt c k) k' = map.get c k'.
Proof.
  intros. apply map_filter_get_pred_true. lia.
Qed.

Lemma map_take_gt_extends : forall (c : word_map) (k : word),
  map.extends c (map_take_gt c k).
Proof.
  eauto using map_filter_extends.
Qed.

Lemma map_take_gt_get_nnone : forall (c : word_map) (k k' : word),
  map.get (map_take_gt c k) k' <> None -> \[k] < \[k'].
Proof.
  intros ? ? ? Hnn. apply map_filter_get_nnone_ftrue in Hnn. lia.
Qed.

Lemma map_filter_ext : forall c f1 f2,
  (forall k, f1 k = f2 k) -> map_filter c f1 = map_filter c f2.
Proof.
  intros ? ? ? Hfeqv. apply map.map_ext. intros k'. do 2 rewrite map_filter_get.
  rewrite Hfeqv. reflexivity.
Qed.

#[export] Instance spec_of_cbt_next_gt: fnspec :=                                .**/
uintptr_t cbt_next_gt(uintptr_t tp, uintptr_t k,
                      uintptr_t key_out, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (key_out_orig: word) (val_out_orig: word)
                (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr key_out_orig key_out
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
        /\ <{ * cbt c tp
              * (if decide (map_take_gt c k = map.empty) then
                   <{ * uintptr key_out_orig key_out
                      * uintptr val_out_orig val_out
                      * emp (res = /[0]) }>
                 else
                   (EX k_res v_res,
                     <{ * emp (map_min_key_value (map_take_gt c k) = Some (k_res, v_res))
                        * uintptr k_res key_out
                        * uintptr v_res val_out
                        * emp (res = /[1]) }>))
                 * R }> m'         #**/                                    /**.
Derive cbt_next_gt SuchThat (fun_correct! cbt_next_gt) As cbt_next_gt_ok.       .**/
{                                                                          /**. .**/
  if (k == -1) /* split */ {                                               /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
  rewrite Decidable_complete. steps. subst. apply map_take_gt_max. .**/
  else {                                                                   /**. .**/
    uintptr_t res = cbt_next_ge(tp, k + 1, key_out, val_out);              /**.
  instantiate (7:=c). steps. .**/
    return res;                                                            /**. .**/
  }                                                                        /**.
  match goal with
  | H: context [ if ?condH then _ else _ ] |- context [ if ?condG then _ else _ ] =>
       replace (condH) with (condG) in H; [ destruct condG eqn:E | ]
  end. steps. steps.
  { apply map_min_key_value_eq. rewrite map_take_gt_get_gt. eauto with content_maps.
    enough (\[k ^+ /[1]] <= \[k_res]) by hwlia. eauto with content_maps.
    intros k' Hink'. eapply map_min_key_value_key_le; [ eassumption | ].
    rewrite map_take_ge_get_ge.
    eauto using map_take_gt_extends with content_maps.
    enough (\[k] < \[k']) by hwlia. eauto using map_take_gt_get_nnone. }
  { unfold map_take_gt, map_take_ge. erewrite map_filter_ext. reflexivity.
    intros. cbv beta. hwlia. } .**/
}                                                                          /**.
Qed.

Lemma list_len_0_nil : forall [A: Type] (l: list A), len l = 0 -> l = nil.
Proof.
  steps. destruct l.
  - steps.
  - simpl len in *. lia.
Qed.

Lemma array_len_1 : forall v a, impl1 (uintptr v a) (array uintptr 1 [|v|] a).
Proof.
  steps. unfold impl1, array, Array.array. intro m'. steps.
  assert (mmap.Def m' = mmap.Def m') by steps. steps. clear Error.
  unfold find_hyp_for_range, canceling, seps. steps.
  apply sep_comm. assert (mmap.Def m = mmap.Def m) by steps. steps. clear Error.
  unfold find_hyp_for_range, canceling, seps. steps.
Qed.

Lemma no_shared_byte : forall b1 b2 a (m : mem),
  ~<{ * (fun m => m = map.singleton a b1)
      * (fun m => m = map.singleton a b2)
      * (fun _ => True) }> m.
Proof.
  intros. intro. steps.
  match goal with
  | H1: context [ b1 ], H2: context [ b2 ] |- _ =>
    match type of H1 with
    | ?tma |= _ => rename tma into ma; rename H1 into Ha
    end;
    match type of H2 with
    | ?tmb |= _ => rename tmb into mb; rename H2 into Hb
    end
  end.
  assert (Hdsj: map.disjoint ma mb).
  { rewrite <- mmap.du_assoc in D.
    destruct (ma ||| mb) as [ mcm | ] eqn:E; try discriminate.
    rewrite <- split_du in E. unfold map.split in E. tauto. }
  unfold "|=" in Ha. unfold "|=" in Hb. subst. unfold map.disjoint in *.
  eapply Hdsj with (k:=a); unfold map.singleton; apply map.get_put_same.
Qed.

Lemma no_shared_uintptr : forall a m,
  ~<{ * (EX v, uintptr v a) * (EX v, uintptr v a) * (fun _ => True) }> m.
Proof.
  intros. intro. steps.
  unfold uintptr, scalar, truncated_word, truncated_scalar, littleendian, ptsto_bytes,
         ptsto in *.
  do 2 match goal with
       | H: context [ Array.array ] |- _ => simpl in H
       end.
  match goal with
  | H1: context [ byte.of_Z \[ ?v1 ] ], H2: context [ byte.of_Z \[ ?v2 ] ] |- _ =>
        apply (no_shared_byte (byte.of_Z \[v1]) (byte.of_Z \[v2]) a m)
  end.
  steps.
Qed.

Lemma array_max_len : forall n l a m,
  array uintptr n l a m -> n <= 2 ^ ltac:(bw) / ltac:(wsize).
Proof.
  intros ? ? ? ? Har.
  enough (~(2 ^ ltac:(bw) / ltac:(wsize) < n)) by lia. intro. purify_hyp Har.
  eapply split_array with (i := 2^ltac:(bw) / ltac:(wsize)) in Har. 2: steps.
  replace (a ^+ /[ltac:(wsize) * (2 ^ ltac:(bw) / ltac:(wsize))]) with a in * by hwlia.
  (* hack/fixme:
           when processing `heapletwise_step` here,
           somewhere down the ltac callstack, `typeclasses eauto with purify` is run
           to solve the goal
           `purify (array uintptr (2 ^ 32 / 4) l[:2 ^ 32 / 4] a) _`
           and that takes something on the order of a minutes to finish; it runs quicker
           when 2^32 is replaced with a smaller number, so it seems the tactic
           at some point computes the big number (2^32/4)
           -> workaround: hide the big number using `remember` *)
  remember (2 ^ 32 / 4) as ec. repeat heapletwise_step. subst.
  do 2
    match goal with
    | H: _ |= array _ _ _ a |- _ =>
         eapply split_off_elem_from_array with (i := 0) (a' := a) in H; steps
    end.
  apply (no_shared_uintptr a m). steps.
Qed.

Fixpoint sorted_word_word_insert (p : word * word) (l : list (word * word)) :=
  match l with
  | cons (k', v') l' => if \[fst p] <=? \[k']
                          then cons p l
                          else cons (k', v') (sorted_word_word_insert p l')
  | nil => cons p nil
  end.

Lemma sorted_ww_insert_len : forall p l,
  len (sorted_word_word_insert p l) = len l + 1.
Proof.
  induction l as [ | hd l ].
  - reflexivity.
  - destruct p as [ pk pv ]. destruct hd as [ hk hv ].
    cbn [ sorted_word_word_insert fst ].
    destruct (\[pk] <=? \[hk]); cbn [ List.length ]; lia.
Qed.

Lemma sorted_ww_insert_in : forall p p' l,
  List.In p' (sorted_word_word_insert p l) -> p' = p \/ List.In p' l.
Proof.
  induction l as [ | hd l ]; cbn.
  - steps. auto.
  - destruct p as [ pk pv ]. destruct hd as [ hk hv ]. cbn [ fst ].
    destruct (\[pk] <=? \[hk]); cbn; steps; repeat destruct_or; try tauto; auto.
Qed.

Lemma sorted_ww_insert_in' : forall p l,
  List.In p (sorted_word_word_insert p l).
Proof.
  induction l as [ | hd l ]; cbn.
  - auto.
  - destruct p as [ pk pv ]. destruct hd as [ hk hv ]. cbn [ fst ].
    destruct (\[pk] <=? \[hk]); cbn; tauto.
Qed.

Lemma sorted_ww_insert_in'' : forall p l,
  List.incl l (sorted_word_word_insert p l).
Proof.
  induction l as [ | hd l ]; cbn.
  - apply List.incl_nil_l.
  - destruct p as [ pk pv ]. destruct hd as [ hk hv ]. cbn [ fst ].
    destruct (\[pk] <=? \[hk]);
    auto using List.incl_cons, List.incl_tl, List.in_eq, List.incl_refl.
Qed.

Instance product_inhabited X1 X2 `{ inhabited X1, inhabited X2 }
  : inhabited (X1 * X2) := { default := (default, default) }.

Definition ww_list_sorted (l : list (word * word)) : Prop :=
  forall i j, 0 <= i < len l -> 0 <= j < len l -> i <= j ->
  forall ki vi kj vj, l[i] = (ki, vi) -> l[j] = (kj, vj) -> \[ki] <= \[kj].

Definition ww_list_unique_keys (l : list (word * word)) : Prop :=
  forall i1 i2, 0 <= i1 < len l -> 0 <= i2 < len l -> fst l[i1] = fst l[i2] -> i1 = i2.

Lemma ww_list_sorted_nil : ww_list_sorted nil.
Proof.
  unfold ww_list_sorted. cbn. steps.
Qed.

Lemma ww_list_sorted_singleton : forall p, ww_list_sorted [|p|].
Proof.
  unfold ww_list_sorted. cbn. intros. assert (i = 0) by lia. assert (j = 0) by lia.
  subst. cbn in *. assert (ki = kj) by congruence. subst. reflexivity.
Qed.

Lemma ww_list_sorted_tail : forall p l, ww_list_sorted (p :: l) -> ww_list_sorted l.
Proof.
  intros ? ? Hsrt. intros i j ? ? ?. specialize (Hsrt (i + 1) (j + 1)).
  do 3 (prove_ante Hsrt; [ cbn [ List.length ] in *; lia | ]).
  intros ? ? ? ?. specialize (Hsrt ki vi kj vj). intros Hgeti Hgetj.
  do 2 (prove_ante Hsrt ; [ steps | ]). assumption.
Qed.

Lemma ww_list_unique_keys_tail : forall p l,
  ww_list_unique_keys (p :: l) -> ww_list_unique_keys l.
Proof.
  intros ? ? Huqk. intros i1 i2 ? ? ?. specialize (Huqk (i1 + 1) (i2 + 1)).
  do 2 (prove_ante Huqk; [ cbn [ List.length ] in *; lia | ]).
  prove_ante Huqk. { steps. } lia.
Qed.

Lemma ww_list_unique_keys_nil : ww_list_unique_keys nil.
Proof.
  unfold ww_list_unique_keys. cbn. steps.
Qed.

Lemma ww_list_unique_keys_singleton : forall p, ww_list_unique_keys [|p|].
Proof.
  unfold ww_list_unique_keys. cbn. intros. lia.
Qed.

Lemma list_get_cons_tail [A : Type] {inh : inhabited A} : forall n (a : A) l,
  0 < n -> (a :: l)[n] = l[n - 1].
Proof.
  auto using push_down_get_tail.
Qed.

Lemma list_get_in1 [A : Type] {inh : inhabited A} : forall n (l : list A),
  0 <= n < len l -> List.In (l[n]) l.
Proof.
  intros ? ? Hnr. unfold List.get. replace (n <? 0) with false by lia.
  apply List.nth_In. lia.
Qed.

Lemma list_get_in1' [A : Type] {inh : inhabited A} : forall n (a : A) l,
  0 <= n < len l -> l[n] = a -> List.In a l.
Proof.
  intros. subst. auto using list_get_in1.
Qed.

Lemma list_get_in2 [A : Type] {inh : inhabited A} : forall a (l : list A),
  List.In a l -> exists n, 0 <= n < len l /\ l[n] = a.
Proof.
  intros ? ? Hlin. eapply List.In_nth in Hlin. destruct Hlin as [ nn [ Hrng Hlnth ] ].
  exists (Z.of_nat nn). split. { lia. } unfold List.get.
  replace (Z.of_nat nn <? 0) with false by lia. rewrite Nat2Z.id. eassumption.
Qed.

Lemma ww_list_sorted_prepend : forall kn vn k v l,
  \[kn] <= \[k] -> ww_list_sorted ((k, v) :: l) ->
  ww_list_sorted ((kn, vn) :: (k, v) :: l).
Proof.
  intros ? ? ? ? ? Hkcmp Hsrt. unfold ww_list_sorted. intros i j Hirng Hjrng Hijcmp.
  assert (Hiv: i = 0 \/ i >= 1) by lia; destruct Hiv;
  assert (Hjv: j = 0 \/ j >= 1) by lia; destruct Hjv;
  subst; cbn; intros ? ? ? ? Hgeti Hgetj; steps; subst; steps;
  [ specialize (Hsrt 0 (j - 1)) | specialize (Hsrt (i - 1) (j - 1)) ];
  do 3 (prove_ante Hsrt; [ cbn [ List.length ] in *; lia | ]).
  - specialize (Hsrt k v kj vj).
    prove_ante Hsrt. { cbn. reflexivity. }
    prove_ante Hsrt. { rewrite list_get_cons_tail in Hgetj by lia. assumption. }
    lia.
  - specialize (Hsrt ki vi kj vj).
    apply Hsrt; erewrite <- list_get_cons_tail by lia; eassumption.
Qed.

Lemma sorted_ww_insert_sorted : forall p l,
  ww_list_sorted l -> ww_list_sorted (sorted_word_word_insert p l).
Proof.
  induction l as [ | hd l ]; cbn.
  - intros. apply ww_list_sorted_singleton.
  - destruct p as [ pk pv ]. destruct hd as [ hk hv ]. cbn [ fst ]. intros Hsrt.
    destruct (\[pk] <=? \[hk]) eqn:E.
    + steps. auto using ww_list_sorted_prepend.
    + prove_ante IHl. { eauto using ww_list_sorted_tail. }
      destruct (sorted_word_word_insert (pk, pv) l) as [ | [ sk sv ] l' ] eqn:E2.
      { apply ww_list_sorted_singleton. }
      steps. apply ww_list_sorted_prepend; try assumption.
      enough (Hin: List.In (sk, sv) (sorted_word_word_insert (pk, pv) l)).
      * apply sorted_ww_insert_in in Hin. destruct Hin as [ ? | Hin ].
        { steps. subst. steps. }
        eapply list_get_in2 in Hin. destruct Hin as [ n [ Hnrng Hnget ] ].
        specialize (Hsrt 0 (n + 1)).
        do 3 (prove_ante Hsrt; [ cbn [ List.length ] in *; lia | ]).
        specialize (Hsrt hk hv sk sv).
        prove_ante Hsrt. { steps. } prove_ante Hsrt. { steps. eassumption. }
        assumption.
      * rewrite E2. cbn. tauto.
Qed.

Lemma ww_list_unique_keys_cons : forall k v l,
  (forall v', ~List.In (k, v') l) -> ww_list_unique_keys l ->
  ww_list_unique_keys ((k, v) :: l).
Proof.
  intros ? ? ? Hnin Huqk. intros i1 i2 Hrng1 Hrng2 Hkeq.
  assert (Hcmp: i1 = 0 \/ i1 >= 1) by lia; destruct Hcmp;
  assert (Hcmp: i2 = 0 \/ i2 >= 1) by lia; destruct Hcmp;
  steps; subst; cbn [ List.length ] in *;
  repeat match goal with
         | Hi: ?i >= 1, Hl: context [ (?a :: ?l)[?i] ] |- _ =>
               replace ((a :: l)[i]) with (l[i - 1]) in Hl by steps
         end.
  1-2:
  exfalso; cbn in Hkeq;
  match type of Hkeq with
  | context [ ?l [?i - 1] ] => destruct (l[i - 1]) as [ fk fv] eqn:E
  end;
  cbn in Hkeq; subst fk; specialize (Hnin fv); apply Hnin;
  eapply list_get_in1'; [ | eassumption ]; lia.
  specialize (Huqk (i1 - 1) (i2 - 1)). do 2 (prove_ante Huqk; [ lia | ]). steps.
Qed.

Lemma ww_list_unique_keys_cons_in : forall k v v' l,
  ww_list_unique_keys ((k, v) :: l) -> ~List.In (k, v') l.
Proof.
  intros ? ? ? ? Huqk Hin. eapply list_get_in2 in Hin.
  destruct Hin as [ n [ Hrng Hget ] ]. specialize (Huqk 0 (n + 1)).
  do 2 (prove_ante Huqk; [ cbn [ List.length ] in *; lia | ]).
  prove_ante Huqk. { steps. rewrite Hget. steps. } lia.
Qed.

Lemma ww_list_unique_keys_cons_in' : forall a l,
  ww_list_unique_keys (a :: l) -> ~List.In a l.
Proof.
  intros. destruct a. eauto using ww_list_unique_keys_cons_in.
Qed.

Lemma sorted_ww_insert_unique_keys : forall k v l,
  (forall v', ~List.In (k, v') l) ->
  ww_list_unique_keys l -> ww_list_unique_keys (sorted_word_word_insert (k, v) l).
Proof.
  induction l as [ | hd l ]; cbn.
  - intros. apply ww_list_unique_keys_singleton.
  - destruct hd as [ hk hv ]. intros Hninu Huqk. destruct (\[k] <=? \[hk]) eqn:E.
    + steps.
      apply ww_list_unique_keys_cons; [ | assumption ].
      intros v' Hin. specialize (Hninu v'). apply Hninu. apply List.in_inv in Hin.
      assumption.
    + apply ww_list_unique_keys_cons.
      * intros v' Hin. apply sorted_ww_insert_in in Hin.
        destruct Hin. { steps. subst. steps. }
        eapply ww_list_unique_keys_cons_in; eauto.
      * apply IHl; [ | eauto using ww_list_unique_keys_tail ].
        intros v' Hin. eapply Hninu. eauto.
Qed.

Lemma ww_list_sorted_head : forall k v l,
  ww_list_sorted ((k, v) :: l) -> forall i, 0 <= i < len l -> \[k] <= \[fst l[i]].
Proof.
  intros ? ? ? Hsrt ? ?.
  specialize (Hsrt 0 (i + 1)).
  do 3 (prove_ante Hsrt; [ cbn [ List.length ] in *; lia | ]).
  eapply Hsrt with (vi:=v) (vj:=snd l[i]); steps. destruct l[i]; steps.
Qed.

Lemma ww_list_sorted_head' : forall k v l,
  ww_list_sorted ((k, v) :: l) -> forall k' v', List.In (k', v') l -> \[k] <= \[k'].
Proof.
  intros ? ? ? Hsrt ? ? Hlin.
  eapply list_get_in2 in Hlin. destruct Hlin as [ n [ Hnrng Hlin ] ].
  replace k' with (fst l[n]) by (rewrite Hlin; reflexivity).
  eapply ww_list_sorted_head. { eassumption. } lia.
Qed.

Lemma ww_list_unique_keys_values : forall l, ww_list_unique_keys l ->
  forall k v1 v2, List.In (k, v1) l -> List.In (k, v2) l -> v1 = v2.
Proof.
  intros ? Huqk ? ? ? Hin1 Hin2.
  eapply list_get_in2 in Hin1. destruct Hin1 as [ n1 [ Hrng1 Hget1 ] ].
  eapply list_get_in2 in Hin2. destruct Hin2 as [ n2 [ Hrng2 Hget2 ] ].
  specialize (Huqk n1 n2). steps. rewrite Hget1 in Huqk. rewrite Hget2 in Huqk.
  cbn [ fst ] in *. steps. congruence.
Qed.

Lemma list_incl_l_cons_tail [A : Type] {inh : inhabited A} :
  forall (a : A) l l', List.incl (a :: l) l' -> List.incl l l'.
Proof.
  intros ? ? ? Hincl. apply List.incl_cons_inv in Hincl. tauto.
Qed.

Lemma list_incl_r_cons_tail [A : Type] {inh : inhabited A } :
  forall (a : A) l l', ~List.In a l -> List.incl l (a :: l') -> List.incl l l'.
Proof.
  intros ? ? ? Hnin Hincl. intros a' Hin. specialize (Hincl a'). steps.
  apply List.in_inv in Hincl. destruct_or; subst; tauto.
Qed.

Lemma ww_list_unique_sorted : forall l1 l2,
  List.incl l1 l2 -> List.incl l2 l1 ->
  ww_list_sorted l1 -> ww_list_sorted l2 ->
  ww_list_unique_keys l1 -> ww_list_unique_keys l2 ->
  l1 = l2.
Proof.
  intros. generalize dependent l2. induction l1 as [ | a1 l1 ]; intros.
  - match goal with
    | H: List.incl _ nil |- _ => apply List.incl_l_nil in H; subst; reflexivity
    end.
  - prove_ante IHl1. { eauto using ww_list_sorted_tail. }
    prove_ante IHl1. { eauto using ww_list_unique_keys_tail. }
    destruct l2 as [ | a2 l2 ].
    { match goal with
      | H: List.incl _ nil |- _ => apply List.incl_l_nil in H; discriminate
      end. }
    destruct a1 as [ k1 v1 ]. destruct a2 as [ k2 v2 ].
    assert (\[k1] <= \[k2] /\ \[k2] <= \[k1]).
    { split;
      [ assert (Hlin: List.In (k2, v2) ((k1, v1) :: l1)) by (auto using List.in_eq)
      | assert (Hlin: List.In (k1, v1) ((k2, v2) :: l2)) by (auto using List.in_eq) ];
      apply List.in_inv in Hlin;
      (destruct Hlin as [ Heq | Hlin ];
       [ steps; subst; steps | eauto using ww_list_sorted_head' ]). }
    assert (k1 = k2) by hwlia. subst k2. rename k1 into k.
    assert (Hlin1: List.In (k, v1) ((k, v1) :: l1)) by (auto using List.in_eq).
    assert (Hlin2: List.In (k, v2) ((k, v1) :: l1)) by (auto using List.in_eq).
    match goal with
    | H: ww_list_unique_keys (_ :: l1) |- _ => rename H into Huqk1
    end.
    epose proof (ww_list_unique_keys_values _ Huqk1 k v1 v2 Hlin1 Hlin2).
    subst v2. rename v1 into v. f_equal. apply IHl1.
    1-2: (eapply list_incl_r_cons_tail;
      [ apply product_inhabited; apply word_inhabited
      | eapply ww_list_unique_keys_cons_in'; eassumption
      | eapply list_incl_l_cons_tail; try eassumption;
        apply product_inhabited; apply word_inhabited ]).
    eauto using ww_list_sorted_tail. eauto using ww_list_unique_keys_tail.
Qed.

Definition map_to_sorted_list : word_map -> list (word * word)
  := map.fold (fun l k v => sorted_word_word_insert (k, v) l) nil.

Lemma map_to_sorted_list_length : forall c, len (map_to_sorted_list c) = map_size c.
Proof.
  intros.
  unfold map_to_sorted_list, map_size.
  eassert (HP: _). eapply map.fold_two_spec
    with (P:=fun m s1 s2 => len s1 = s2) (m:=c).
  all: cycle 2. { eassumption. }
  - steps.
  - steps. subst. apply sorted_ww_insert_len.
Qed.

Lemma map_to_sorted_list_empty : map_to_sorted_list map.empty = nil.
Proof.
  apply map.fold_empty.
Qed.

Lemma map_to_sorted_list_empty' : forall c, map_to_sorted_list c = nil -> c = map.empty.
Proof.
  intros ? Hnil. f_apply (fun l : list (word * word) => len l) Hnil. cbn in Hnil.
  rewrite map_to_sorted_list_length in Hnil. auto using map_size_empty2.
Qed.

Lemma map_to_sorted_list_in : forall c k v,
  List.In (k, v) (map_to_sorted_list c) <-> map.get c k = Some v.
Proof.
  intros ?.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state =>
      forall k v, List.In (k, v) state <-> map.get m k = Some v).
  all: cycle 2. { eassumption. }
  - steps. split; steps. exfalso. eauto using List.in_nil.
  - cbn. steps. split; steps.
    + match goal with
      | H: List.In _ _ |- _ => apply sorted_ww_insert_in in H; destruct_or; steps
      end.
      rewrite map.get_put_diff. { apply_forall. assumption. } intro. subst.
      match goal with
      | Hu: forall _, _, Hlin: List.In _ _ |- _ => apply Hu in Hlin
      end.
      congruence.
    + eq_neq_cases k k0.
      * subst. rewrite map.get_put_same in *. steps. subst. apply sorted_ww_insert_in'.
      * rewrite map.get_put_diff in * by (symmetry; assumption).
        apply sorted_ww_insert_in''. apply_forall. assumption.
Qed.

Lemma map_to_sorted_list_sorted : forall c,
  ww_list_sorted (map_to_sorted_list c).
Proof.
  intros. unfold map_to_sorted_list.
  eapply map.fold_spec; eauto using ww_list_sorted_nil, sorted_ww_insert_sorted.
Qed.

Lemma map_to_sorted_list_unique_keys : forall c,
  ww_list_unique_keys (map_to_sorted_list c).
Proof.
  intros.
  eassert (HP: _). eapply map.fold_spec
    with (P:=fun m state => (forall k v, List.In (k, v) state -> map.get m k = Some v)
                            /\ ww_list_unique_keys state).
  all: cycle 2. { eapply proj2 in HP. eassumption. }
  - split.
    + intros. exfalso. eapply List.in_nil. eassumption.
    + apply ww_list_unique_keys_nil.
  - intros. cbn beta. steps.
    + match goal with
      | H: List.In _ _ |- _ => apply sorted_ww_insert_in in H; destruct H; steps
      end.
      eq_neq_cases k k0.
      * exfalso. subst k0. eapply some_not_none; [ | eassumption ]. eauto.
      * steps. auto.
    + apply sorted_ww_insert_unique_keys; [ | assumption ]. intros v' Hin.
      eapply some_not_none; [ | eassumption ]. eauto.
Qed.

Lemma map_size_empty'' : forall c,
  c <> map.empty -> map_size c > 0.
Proof.
  intros c Hnem. enough (map_size c <> 0) by (pose proof map_size_nonneg c; lia).
  intro Hsz0. apply_ne. auto using map_size_empty2.
Qed.

Lemma map_to_sorted_list_first : forall c,
  c <> map.empty -> map_min_key_value c = Some ((map_to_sorted_list c)[0]).
Proof.
  intros. destruct ((map_to_sorted_list c)[0]) as [ k0 v0 ] eqn:E.
  assert (map_size c > 0) by (auto using map_size_empty'').
  apply map_min_key_value_eq.
  - eapply map_to_sorted_list_in; try eassumption.
    eapply list_get_in1'; [ | eassumption ]. rewrite map_to_sorted_list_length. lia.
  - intros. destruct (map.get c k') as [ v' | ] eqn:E2; steps.
    rewrite <- map_to_sorted_list_in in E2. eapply list_get_in2 in E2.
    destruct E2 as [ n [ Hnrng Hnget ] ].
    eapply map_to_sorted_list_sorted with (i:=0) (j:=n); try eassumption; lia.
Qed.

Lemma list_map_get (X Y : Type) { _ : inhabited X } { _ : inhabited Y }
  : forall (l : list X) (f : X -> Y) i,
  0 <= i < len l -> (List.map f l)[i] = f l[i].
Proof.
  intros. unfold List.get. replace (i <? 0) with false by lia.
  rewrite <- List.map_nth with (f:=f).
  apply List.nth_indep. rewrite List.map_length. lia.
Qed.

Lemma list_from_get (X : Type) { _ : inhabited X }
  : forall (l : list X) i1 i2, i1 >= 0 -> i2 >= 0 -> l[i1:][i2] = l[i1 + i2].
Proof.
  intros. unfold List.from. unfold List.get.
  replace (i2 <? 0) with false by lia. replace (i1 + i2 <? 0) with false by lia.
  rewrite List.nth_skipn. f_equal. lia.
Qed.

Lemma map_filter_some : forall c f k v,
  map.get (map_filter c f) k = Some v -> map.get c k = Some v.
Proof.
  intros. rewrite map_filter_get in *. destruct (f k); congruence.
Qed.

Lemma map_take_gt_some : forall c k1 k2 v,
  map.get (map_take_gt c k1) k2 = Some v -> map.get c k2 = Some v.
Proof.
  intros. unfold map_take_gt in *. eauto using map_filter_some.
Qed.

Lemma ww_list_sorted_from : forall n l, ww_list_sorted l -> ww_list_sorted (l[n:]).
Proof.
  intros ? ? Hsrt.
  assert (Hcmp: n < 0 \/ n >= 0) by lia.
  destruct Hcmp. { rewrite List.from_beginning; steps. }
  assert (Hcmp: n >= len l \/ n < len l) by lia.
  destruct Hcmp. { rewrite List.from_pastend by lia. apply ww_list_sorted_nil. }
  unfold ww_list_sorted. intros. rewrite list_from_get in * by lia.
  rewrite List.len_from in * by lia.
  eapply (Hsrt (n + i) (n + j)); try eassumption; lia.
Qed.

Lemma ww_list_unique_keys_from : forall n l,
  ww_list_unique_keys l -> ww_list_unique_keys (l[n:]).
Proof.
  intros ? ? Huqk.
  assert (Hcmp: n < 0 \/ n >= 0) by lia.
  destruct Hcmp. { rewrite List.from_beginning; steps. }
  assert (Hcmp: n >= len l \/ n < len l) by lia.
  destruct Hcmp. { rewrite List.from_pastend by lia. apply ww_list_unique_keys_nil. }
  unfold ww_list_unique_keys. intros. repeat rewrite list_from_get in * by lia.
  rewrite List.len_from in * by lia.
  enough (n + i1 = n + i2) by lia. eapply Huqk; steps.
Qed.

Lemma map_to_sorted_list_take_gt : forall c i k,
  0 <= i < map_size c ->
  fst ((map_to_sorted_list c)[i]) = k ->
  map_to_sorted_list (map_take_gt c k) = (map_to_sorted_list c)[i + 1:].
Proof.
  intros. apply ww_list_unique_sorted;
  try apply ww_list_sorted_from; try apply map_to_sorted_list_sorted;
  try apply ww_list_unique_keys_from; try apply map_to_sorted_list_unique_keys.
  - intros [ k' v' ] Hin. rewrite map_to_sorted_list_in in Hin.
    assert (\[k] < \[k']) by (eauto using map_take_gt_get_nnone, some_not_none).
    apply map_take_gt_some in Hin. rewrite <- map_to_sorted_list_in in Hin.
    eapply list_get_in2 in Hin. destruct Hin as [ i' [ Hrng Hget ] ].
    pose proof (map_to_sorted_list_sorted c) as Hsrt.
    assert (~(i' <= i)).
    { intro. enough (\[k'] <= \[k]) by hwlia.
      destruct ((map_to_sorted_list c)[i]) as [ kk v ] eqn:E. cbn [ fst ] in *. subst kk.
      specialize (Hsrt i' i). rewrite <- map_to_sorted_list_length in *. steps.
      specialize (Hsrt k' v' k v). eauto. }
    eapply list_get_in1' with (n:=i' - (i + 1)); steps.
  - intros [ k' v' ] Hin. rewrite map_to_sorted_list_in.
    eapply list_get_in2 in Hin. destruct Hin as [ io [ Hrng Hget ] ].
    rewrite <- map_to_sorted_list_length in *.
    rewrite list_from_get in Hget by lia. rewrite List.len_from in Hrng by lia.
    remember (i + 1 + io) as i'. assert (io = i' - i - 1) by lia. subst io. clear Heqi'.
    rewrite map_take_gt_get_gt.
    + rewrite <- map_to_sorted_list_in. eapply list_get_in1'; [ | eassumption ]. lia.
    + pose proof (map_to_sorted_list_sorted c) as Hsrt.
      destruct (map_to_sorted_list c)[i] as [ kk v ] eqn:E. cbn in *. subst kk.
      assert (\[k] <= \[k']). { eapply (Hsrt i i'); try lia; eassumption. }
      enough (k <> k') by hwlia. intro. subst k'.
      enough (i = i') by steps.
      pose proof (map_to_sorted_list_unique_keys c) as Huqk.
      apply Huqk; steps. rewrite E. rewrite Hget. reflexivity.
Qed.

Lemma map_to_sorted_list_key_gt_size : forall c i k,
  0 <= i < map_size c ->
  fst ((map_to_sorted_list c)[i]) = k ->
  map_size (map_take_gt c k) = map_size c - 1 - i.
Proof.
  intros ? ? ? Hirng Hel. pose proof (map_to_sorted_list_take_gt c i k Hirng Hel) as Heq.
  f_apply (fun (l : list (word * word)) => len l) Heq.
  rewrite <- (map_to_sorted_list_length c) in *.
  rewrite map_to_sorted_list_length in Heq.
  rewrite List.len_from in Heq; lia.
Qed.

Lemma map_to_sorted_list_in'' : forall c i k,
  0 <= i < map_size c ->
  fst ((map_to_sorted_list c)[i]) = k ->
  map.get c k <> None.
Proof.
  intros. destruct ((map_to_sorted_list c)[i]) as [ kk v ] eqn:E. cbn in *. subst kk.
  rewrite <- map_to_sorted_list_length in *. apply list_get_in1' in E; [ | assumption ].
  rewrite map_to_sorted_list_in in E. steps.
Qed.

Lemma map_filter_strengthen : forall c f_weak f_strong,
  (forall k, f_strong k = true -> f_weak k = true) ->
  map_filter (map_filter c f_weak) f_strong = map_filter c f_strong.
Proof.
  intros ? ? ? Hst. apply map.map_ext. intros. repeat rewrite map_filter_get.
  destruct (f_strong k) eqn:E; [ | reflexivity ].
  apply Hst in E. rewrite E. reflexivity.
Qed.

Lemma map_take_gt_take_ge : forall c k1 k2,
  \[k1] <= \[k2] -> map_take_gt (map_take_ge c k1) k2 = map_take_gt c k2.
Proof.
  intros. apply map_filter_strengthen. intros. hwlia.
Qed.

#[export] Instance spec_of_page_from_cbt: fnspec :=                         .**/
uintptr_t page_from_cbt(uintptr_t tp, uintptr_t k, uintptr_t n,
                        uintptr_t keys_out, uintptr_t vals_out) /**#
  ghost_args := (c: word_map) (keys_out_orig: list word) (vals_out_orig: list word)
                (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * array uintptr \[n] keys_out_orig keys_out
                     * array uintptr \[n] vals_out_orig vals_out
                     * R }> m;
  ensures t' m' res := t' = t /\
     let sl := map_to_sorted_list (map_take_ge c k) in
     let skeys := List.map fst sl in
     let svals := List.map snd sl in
       res = /[Z.min (len sl) \[n]] /\
       <{ * cbt c tp
          * array uintptr \[n] (skeys[:\[res]] ++ keys_out_orig[\[res]:]) keys_out
          * array uintptr \[n] (svals[:\[res]] ++ vals_out_orig[\[res]:]) vals_out
          * R }> m' #**/                                                     /**.
Derive page_from_cbt SuchThat (fun_correct! page_from_cbt) As page_from_cbt_ok.   .**/
{                                                                            /**.
  assert (\[n] <= 2 ^ ltac:(bw) / ltac:(wsize)) by (eauto using array_max_len). .**/
  if (n == 0) /* split */  {                                                 /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**. .**/
  else {                                                                     /**.
  assert (len keys_out_orig = \[n]) by steps.
  assert (len vals_out_orig = \[n]) by steps. .**/
    uintptr_t next_res = cbt_next_ge(tp, k, keys_out, vals_out);             /**.
  instantiate (7:=c). steps. .**/
    if (next_res == 0) /* split */ {                                         /**. .**/
      return 0;                                                              /**. .**/
    }                                                                        /*?.
  match goal with
  | H: context [ if ?cond then _ else _ ] |- _ =>
       destruct cond eqn:E; [ | exfalso; steps ]
  end.
  apply Decidable_sound in E. rewrite E. rewrite map_to_sorted_list_empty. cbn.
  repeat heapletwise_step.
  replace (\[keys_out ^- keys_out] / ltac:(wsize)) with 0 in * by steps.
  replace (\[vals_out ^- vals_out] / ltac:(wsize)) with 0 in * by steps.
  replace (\[n] - 0 - 1) with (\[n] - 1) in * by steps.
  merge_step. merge_step. steps. .**/
    else {                                                                   /**.
  match goal with
  | H: context [ if ?cond then _ else _ ] |- _ =>
       destruct cond eqn:E; [ exfalso; steps | ]
  end.
  apply Decidable_complete_alt in E.
  repeat heapletwise_step. .**/
      uintptr_t k_it = load(keys_out);                                       /**. .**/
      uintptr_t finished = 0;                                                /**. .**/
      uintptr_t i = 1;                                                       /**.
  loop invariant above m'. move Scope6 at bottom.
  do 10 match reverse goal with
  | H: _ |= _ |- _ => move H at bottom
  end.
  (* TODO: investitage/document why this this has to be done manually *)
  replace (\[keys_out ^- keys_out] / ltac:(wsize)) with 0 in * by steps.
  replace (\[vals_out ^- vals_out] / ltac:(wsize)) with 0 in * by steps.
  replace (\[n] - 0 - 1) with (\[n] - 1) in * by steps.
  merge_step. merge_step.
  remember (map_to_sorted_list (map_take_ge c k)) as sl.
  remember (List.map fst sl) as skeys.
  remember (List.map snd sl) as svals.
  assert (Hszg0: 0 < map_size (map_take_ge c k)).
  { enough (map_size (map_take_ge c k) <> 0).
    { pose proof (map_size_nonneg (map_take_ge c k)). lia. }
    intro Hsz0. apply map_size_empty2 in Hsz0. tauto. }
  assert (skeys[\[i] - 1] = k_it).
  { pose proof (map_to_sorted_list_first (map_take_ge c k)) as Hfrst.
    prove_ante Hfrst. { assumption. }
    match goal with
    | H: map_min_key_value _ = Some (_, _) |- _ => rewrite H in Hfrst
    end.
    injection Hfrst. intros Hff. subst. steps.
    erewrite list_map_get by (rewrite map_to_sorted_list_length; lia).
    rewrite <- Hff. reflexivity. }
  replace (nil ++ [|k_it|] ++ keys_out_orig[1:])
    with (skeys[:\[i]] ++ keys_out_orig[\[i]:]) in *; cycle 1.
  { steps.
    - enough (len skeys <> 0) by steps. intros Hlen0. apply list_len_0_nil in Hlen0.
      rewrite Hlen0 in *. symmetry in Heqskeys. apply List.map_eq_nil in Heqskeys.
      rewrite Heqskeys in *. symmetry in Heqsl. apply map_to_sorted_list_empty' in Heqsl.
      tauto. }
   replace (nil ++ [|v_res|] ++ vals_out_orig[1:])
     with (svals[:\[i]] ++ vals_out_orig[\[i]:]) in *; cycle 1.
   { steps.
    - enough (len svals <> 0) by steps. intros Hlen0. apply list_len_0_nil in Hlen0.
      rewrite Hlen0 in *. symmetry in Heqsvals. apply List.map_eq_nil in Heqsvals.
      rewrite Heqsvals in *. symmetry in Heqsl. apply map_to_sorted_list_empty' in Heqsl.
      tauto.
    - pose proof (map_to_sorted_list_first (map_take_ge c k)) as Hfrst.
      prove_ante Hfrst. { assumption. }
      match goal with
      | H: map_min_key_value _ = Some (_, _) |- _ => rewrite H in Hfrst
      end.
      injection Hfrst. intros Hff. subst.
      erewrite list_map_get by (rewrite map_to_sorted_list_length; lia).
      rewrite <- Hff. reflexivity. }
  assert (finished <> /[0] -> map_take_gt c k_it = map.empty) by steps.
  assert (\[i] <= map_size (map_take_ge c k)) by steps.
  clear Hszg0.
  prove (\[i] >= 1).
  match goal with
  | H1: finished = /[0], H2: i = /[1] |- _ => clear H1 H2
  end.
  move finished at bottom.
  move i at bottom.
  move k_it at bottom.
  move Heqsl after Scope6.
  move Heqskeys after Scope6.
  move Heqsvals after Scope6.
  purge v_res. .**/
      while (i < n && !finished)
        /* decreases (\[n] + 1 - \[i] - \[finished]) */ {                  /**. .**/
        uintptr_t next_res_loop =
          cbt_next_gt(tp, k_it,
            keys_out + sizeof(uintptr_t) * i,
            vals_out + sizeof(uintptr_t) * i);                             /**.
  instantiate (3:=c). steps. .**/
        if (next_res_loop == 1) /* split */ {                              /**.
  match goal with
  | H: context [ if ?cond then _ else _ ] |- _ =>
       destruct cond eqn:E2; [ solve [ exfalso; steps ] | ]
  end.
  repeat heapletwise_step.
  replace (keys_out ^+ /[ltac:(wsize)] ^* i ^- keys_out)
    with (/[ltac:(wsize)] ^* i) in * by hwlia.
  replace (vals_out ^+ /[ltac:(wsize)] ^* i ^- vals_out)
    with (/[ltac:(wsize)] ^* i) in * by hwlia.
  replace (\[/[ltac:(wsize)] ^* i] / ltac:(wsize)) with \[i] in * by hwlia.
  merge_step. merge_step. .**/
          k_it = load(keys_out + sizeof(uintptr_t) * i);                   /**. .**/
          i = i + 1;                                                       /**. .**/
        }                                                                  /*?.
  assert (\[k] <= \[k_it']).
  { pose proof (map_to_sorted_list_in'' (map_take_ge c k) (\[i'] - 1) k_it') as Hkitin.
    prove_ante Hkitin. lia. prove_ante Hkitin. subst skeys sl.
    match goal with
    | H: _ = k_it' |- _ => erewrite list_map_get in H
        by (rewrite map_to_sorted_list_length; lia)
    end. assumption. eauto using map_take_ge_get_nnone. }
  assert (\[i'] < map_size (map_take_ge c k)).
  { pose proof (map_to_sorted_list_key_gt_size (map_take_ge c k) (\[i'] - 1) k_it')
      as Hnsz. prove_ante Hnsz. lia. prove_ante Hnsz. subst skeys sl.
    match goal with
    | H: _ = k_it' |- _ => erewrite list_map_get in H
        by (rewrite map_to_sorted_list_length; lia)
    end.
    assumption. rewrite map_take_gt_take_ge in Hnsz by assumption.
    enough (map_size (map_take_gt c k_it') > 0) by lia.
    apply map_size_empty''. eapply map_get_nnone_nonempty. eapply some_not_none.
    eauto using map_min_key_value_in. }
  assert (\[i'] < len sl).
  { subst sl. rewrite map_to_sorted_list_length. assumption. }
  assert (\[i'] < len svals).
  { subst svals. rewrite List.map_length. assumption. }
  assert (\[i'] < len skeys).
  { subst skeys. rewrite List.map_length. assumption. }
  assert (Hsli': sl[\[i']] = (k_it, v_res)).
  { pose proof (map_to_sorted_list_first (map_take_gt c k_it')) as Hshfr.
    prove_ante Hshfr. eapply map_get_nnone_nonempty. eapply some_not_none.
    eauto using map_min_key_value_in. rewrite Hshfr in *.
    match goal with
    | H: Some _ = Some _ |- _ => injection H; intros Hili; clear H
    end.
    rewrite <- map_take_gt_take_ge with (k1:=k) in Hili by assumption.
    erewrite map_to_sorted_list_take_gt in Hili; cycle 2.
    subst skeys sl.
    match goal with
    | H: _ = k_it' |- _ => erewrite list_map_get in H
    end. eassumption. rewrite map_to_sorted_list_length. lia. 2: lia.
    assert (\[i'] < len (map_to_sorted_list (map_take_ge c k))).
    { rewrite map_to_sorted_list_length. lia. }
    replace ((map_to_sorted_list (map_take_ge c k))[\[i'] - 1 + 1:][0])
      with ((map_to_sorted_list (map_take_ge c k))[\[i']]) in Hili by steps.
    subst sl. assumption. }
  steps.
  { subst svals. erewrite list_map_get by lia. rewrite Hsli'. reflexivity. }
  { subst skeys. erewrite list_map_get by lia. rewrite Hsli'. reflexivity. }
  { subst skeys. erewrite list_map_get by lia. subst i. steps.
    rewrite Hsli'. reflexivity. } .**/
        else {                                                             /**.
  match goal with
  | H: context [ if ?cond then _ else _ ] |- _ =>
       destruct cond eqn:E2; [ | solve [ exfalso; steps ] ]
  end.
  repeat heapletwise_step.
  replace (keys_out ^+ /[ltac:(wsize)] ^* i ^- keys_out)
    with (/[ltac:(wsize)] ^* i) in * by hwlia.
  replace (vals_out ^+ /[ltac:(wsize)] ^* i ^- vals_out)
    with (/[ltac:(wsize)] ^* i) in * by hwlia.
  replace (\[/[ltac:(wsize)] ^* i] / ltac:(wsize)) with \[i] in * by hwlia.
  merge_step. merge_step.
  apply Decidable_sound in E2. .**/
          finished = 1;                                                    /**. .**/
        }                                                                  /*?.
  steps. .**/
      }                                                                    /**. .**/
      return i;                                                            /**. .**/
    }                                                                      /*?.
  step. step. steps. step.
  assert (\[i] <= len sl). { subst sl. rewrite map_to_sorted_list_length. assumption. }
  assert (\[i] <= \[n]).
  { assert (\[i] <= len skeys). { subst skeys. rewrite List.map_length. assumption. }
    steps. }
  match goal with
  | H: _ \/ finished <> /[0] |- _ => destruct H
  end.
  { assert (i = n) by hwlia. subst i. hwlia. }
  { enough (\[i] = len sl) by hwlia. subst sl. rewrite map_to_sorted_list_length.
    pose proof (map_to_sorted_list_key_gt_size (map_take_ge c k) (\[i] - 1) k_it) as Hsz.
    prove_ante Hsz. lia. prove_ante Hsz. subst skeys.
    match goal with
    | H: _ = k_it |- _ => erewrite list_map_get in H; steps
    end.
    rewrite map_take_gt_take_ge in Hsz.
    assert (map_size (map_take_gt c k_it) = 0).
    { assert (Htem: map_take_gt c k_it = map.empty) by auto. rewrite Htem.
      apply map_size_empty1. }
    lia.
    eapply map_take_ge_get_nnone. subst skeys. eapply map_to_sorted_list_in''; cycle 1.
    match goal with
    | H: _ = k_it |- _ => erewrite list_map_get in H by steps
    end.
    eassumption. lia. }
  steps. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

(* END CBT IMPL *)

End LiveVerif. Comments .**/ //.
