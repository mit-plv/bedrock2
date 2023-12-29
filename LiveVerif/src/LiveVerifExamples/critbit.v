(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Require Coq.Bool.Bool.

Load LiveVerif.

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Ltac apply_ne :=
  match goal with
  | H: _ <> _ |- False => apply H
  end.

(* an obvious finishing step that `steps` doesn't do *)
Ltac simple_finish_step :=
  solve [match goal with
  | H: ?P |- ?P => exact H
  | |- ?P <-> ?P => reflexivity
  | H1: ?P, H2: ~?P |- _ => apply H2 in H1; destruct H1
  | H: ?x <> ?x |- _ => exfalso; apply (H (eq_refl x))
  (* | H: ?a = ?b |- ?b = ?a => symmetry; exact H *) (* <- we want this,
  but it seems to cause the Coq unification algorithm to go into an infinite loop
  at at least one place in this file *)
  | H: Some _ = None |- _ => discriminate H
  | H: None = Some _ |- _ => discriminate H
  | |- Some _ <> None => let H := fresh "H" in intro H; discriminate H
  | |- None <> Some _ => let H := fresh "H" in intro H; discriminate H
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

  (* Bool.eqb _ _ *)
  | H: context[ Bool.eqb ?b ?b ] |- _ => rewrite Bool.eqb_reflx in H
  | |- context[ Bool.eqb ?b ?b ] => rewrite Bool.eqb_reflx

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

Ltac misc_simpl_step :=
  match goal with
  | H: context [ negb ?c ] |- _ => is_constructor c; simpl negb in H
  | |- context [ negb ?c ] => is_constructor c; simpl negb

  | H: context [ /[\[ _ ]] ] |- _ => rewrite word.of_Z_unsigned in H
  | |- context [ /[\[ _ ]] ] => rewrite word.of_Z_unsigned
  | H: context [ \[/[0]] ] |- _ => rewrite word.unsigned_of_Z_0 in H
  | |- context [ \[/[0]] ] => rewrite word.unsigned_of_Z_0
  | H: context [ \[/[1]] ] |- _ => rewrite word.unsigned_of_Z_1 in H
  | |- context [ \[/[1]] ] => rewrite word.unsigned_of_Z_1
  end.

(* substitute a variable if it is equal to one of several selected expressions *)
Ltac subst_step :=
  match goal with
  | H: ?c = map.empty |- _ => is_var c; subst c
  | H: ?c = map.singleton _ _ |- _ => is_var c; subst c

  (* TODO: consider (try) enabling this --> problematic when we assign
           .**/ a = b; /**. *)
  (* | H: ?x = ?y |- _ => is_var x; is_var y; subst y *)
  end.

(* needed because the other notation contains a closing C comment *)
Notation "a ||| b" := (mmap.du a b) (at level 34, no associativity).

(* sometimes used in a heuristic to differentiate between maps
   - representing memory
   - representing the content of a CBT *)
Require Import coqutil.Tactics.ident_ops.

Inductive tree_skeleton: Type :=
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

Definition prefix := list bool.

Fixpoint pfx_le (p1 p2: prefix) :=
  match p1 with
  | nil => True
  | cons b1 p1' => match p2 with
                   | nil => False
                   | cons b2 p2' => if Bool.eqb b1 b2 then pfx_le p1' p2' else False
                   end
  end.

Definition pfx_len (p: prefix) := len p.

Lemma pfx_len_nneg : forall (p: prefix), 0 <= pfx_len p.
Proof.
  intros.
  unfold pfx_len. lia.
Qed.

Lemma pfx_le_reflx : forall (p: prefix), pfx_le p p.
Proof.
  induction p.
  - simpl. apply I.
  - simpl. rewrite Bool.eqb_reflx. assumption.
Qed.

Lemma pfx'_nil_nil : forall (p: prefix), pfx_le p nil -> p = nil.
Proof.
  induction p; intros.
  - reflexivity.
  - simpl in *. tauto.
Qed.

Lemma pfx_le_asym : forall (p1 p2: prefix), pfx_le p1 p2 -> pfx_le p2 p1 -> p1 = p2.
Proof.
  induction p1; intros.
  - destruct p2.
    + reflexivity.
    + simpl in *. tauto.
  - destruct p2; simpl in *.
    + tauto.
    + destruct (Bool.eqb a b) eqn:E.
      * apply Bool.eqb_prop in E. subst. f_equal. rewrite Bool.eqb_reflx in *.
        match goal with
        | H: context[_ -> _ = _] |- _ => apply H
        end; assumption.
      * tauto.
Qed.

Lemma pfx_le_trans : forall (p1 p2 p3: prefix),
                  pfx_le p1 p2 -> pfx_le p2 p3 -> pfx_le p1 p3.
Proof.
  induction p1; intros; simpl.
  - apply I.
  - destruct p3.
    + destruct p2; simpl in *; tauto.
    + destruct (Bool.eqb a b) eqn:E.
      * apply Bool.eqb_prop in E. subst. destruct p2; simpl in *.
        -- tauto.
        -- destruct (Bool.eqb b b0) eqn:E.
          ++ apply Bool.eqb_prop in E. subst. rewrite Bool.eqb_reflx in *.
             match goal with
             | H: context[_ -> pfx_le _ _] |- _ => apply H with (p2:=p2)
             end; assumption.
          ++ assert (E': Bool.eqb b0 b = false) by tauto. rewrite E' in *. tauto.
      * destruct p2; simpl in *.
        -- tauto.
        -- destruct a; destruct b; destruct b0; simpl in *; congruence.
Qed.

Lemma pfx_le_len : forall (p1 p2: prefix), pfx_le p1 p2 -> pfx_len p1 <= pfx_len p2.
Proof.
  induction p1; intros; unfold pfx_len in *.
  - simpl. lia.
  - match goal with
    | H1: pfx_le _ _, H2: forall _, _ |- _ => rename H1 into HH; rename H2 into IH
    end.
    simpl len. destruct p2; simpl pfx_le in *; simpl len in *.
    + tauto.
    + destruct (Bool.eqb a b); [ apply IH in HH | ]; lia.
Qed.

Lemma pfx_lele_tot : forall (p1 p2 p: prefix),
                     pfx_le p1 p -> pfx_le p2 p -> pfx_le p1 p2 \/ pfx_le p2 p1.
Proof.
Admitted.

Lemma pfx_lele_len_ord : forall (p1 p2 p: prefix),
  pfx_le p1 p -> pfx_le p2 p -> pfx_len p1 <= pfx_len p2 -> pfx_le p1 p2.
Admitted.

Definition bit_at (w: word) (i: Z) := word.eqb (word.and (w ^>> /[i]) /[1]) /[1].
  (* Z.testbit \[w] i. *)

(*
Lemma bit_at_raw : forall w i, 0 <= i < 32 -> bit_at w i = word.eqb (word.and (w ^>> /[i]) /[1]) /[1].
Admitted.
*)

Lemma bit_at_inj : forall w1 w2,
  (forall i, 0 <= i < 32 -> bit_at w1 i = bit_at w2 i) -> w1 = w2.
Admitted.

Fixpoint pfx'_emb_rec (w: word) (remaining: nat) :=
  match remaining with
  | O => nil
  | S n => cons (bit_at w (32 - Z.of_nat remaining)) (pfx'_emb_rec w n)
  end.

Definition pfx_emb (w: word) := pfx'_emb_rec w 32.

Lemma pfx_emb_len : forall (w: word), pfx_len (pfx_emb w) = 32.
Admitted.

Definition pfx_bit (p: prefix) (i: Z) (b: bool) :=
  0 <= i < len p /\ List.get p i = b.

Lemma pfx_bit_excl : forall (p: prefix) (i: Z), ~pfx_bit p i false \/ ~pfx_bit p i true.
Admitted.

Lemma pfx_bit_not_both :
  forall (p: prefix) (i: Z), pfx_bit p i false -> pfx_bit p i true -> False.
Admitted.

Lemma pfx_bit_diff_le_len : forall (p p1 p2: prefix) (i: Z) (b1 b2: bool),
  pfx_le p p1 -> pfx_le p p2 -> pfx_bit p1 i b1 -> pfx_bit p2 i b2 -> b1 <> b2 ->
  pfx_len p <= i.
Admitted.

Lemma pfx_bit_or : forall (p: prefix) (i: Z),
                   0 <= i < pfx_len p -> pfx_bit p i false \/ pfx_bit p i true.
Admitted.

Lemma pfx_bit_len : forall (p: prefix) (i: Z) (b: bool),
                   pfx_bit p i b -> 0 <= i < pfx_len p.
Admitted.

Lemma pfx_bit_le : forall (p1 p2: prefix) (i: Z) (b: bool),
                   pfx_le p1 p2 -> pfx_bit p1 i b -> pfx_bit p2 i b.
Admitted.

(* rename to pfx_snoc *)
Definition pfx_app (p: prefix) (b: bool) := p ++ cons b nil.

Lemma pfx_app_le : forall (p1 p2: prefix) (b: bool),
                   pfx_le p1 p2 -> pfx_bit p2 (pfx_len p1) b ->
                   pfx_le (pfx_app p1 b) p2.
Admitted.

Lemma pfx_app_bit : forall (p: prefix) (b: bool), pfx_bit (pfx_app p b) (pfx_len p) b.
Admitted.

Lemma pfx_app_len : forall (p: prefix) (b: bool), pfx_len (pfx_app p b) = pfx_len p + 1.
Admitted.

Lemma pfx_app_le_self : forall (p: prefix) (b: bool), ~pfx_le (pfx_app p b) p.
Admitted.

Fixpoint pfx_meet (p1 p2: prefix) :=
  match p1 with
  | nil => nil
  | cons b1 p1' => match p2 with
                   | nil => nil
                   | cons b2 p2' => if Bool.eqb b1 b2 then
                                      cons b1 (pfx_meet p1' p2')
                                    else nil
                   end
  end.

Lemma pfx_meet_id : forall (p: prefix), pfx_meet p p = p.
Admitted.

Lemma pfx_meet_comm : forall (p1 p2: prefix), pfx_meet p1 p2 = pfx_meet p2 p1.
Admitted.

Lemma pfx_meet_assoc : forall (p1 p2 p3: prefix),
                  pfx_meet (pfx_meet p1 p2) p3 = pfx_meet p1 (pfx_meet p2 p3).
Admitted.

Lemma pfx_meet_le_l : forall (p1 p2: prefix), pfx_le (pfx_meet p1 p2) p1.
Admitted.

Lemma pfx_meet_le_meet_l : forall (p1 p2 p: prefix),
  pfx_le p1 p2 -> pfx_le (pfx_meet p1 p) (pfx_meet p2 p).
Admitted.

Lemma pfx_meet_le_meet_r : forall (p1 p2 p: prefix),
  pfx_le p1 p2 -> pfx_le (pfx_meet p p1) (pfx_meet p p2).
Admitted.

Lemma pfx_meet_le_r : forall (p1 p2: prefix), pfx_le (pfx_meet p1 p2) p2.
Admitted.

Lemma pfx_meet_le_both : forall (p p1 p2: prefix),
                         pfx_le p p1 -> pfx_le p p2 -> pfx_le p (pfx_meet p1 p2).
Admitted.

Lemma pfx_meet_bit_diff_len : forall (p1 p2: prefix) (i: Z) (b1 b2: bool),
  pfx_bit p1 i b1 -> pfx_bit p2 i b2 -> b1 <> b2 -> pfx_len (pfx_meet p1 p2) <= i.
Admitted.

Lemma pfx_meet_len_same_bit_false : forall (p1 p2: prefix) (l: Z) (b: bool),
  pfx_len (pfx_meet p1 p2) = l -> pfx_bit p1 l b -> pfx_bit p2 l b -> False.
Admitted.

Lemma pfx_meet_le_eq : forall (p1 p2: prefix),
  pfx_le p1 p2 -> pfx_meet p1 p2 = p1.
Admitted.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

(* lemmas about map operations on singletons *)

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

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step
  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => small_map_basic_op_simpl_step
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
  - rewrite Z.bits_0. tauto.
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

Definition pfx_mmeet (c: word_map) :=
  let r := map.fold (fun state k v => match state with
                                      | Some p => Some (pfx_meet (pfx_emb k) p)
                                      | None => Some (pfx_emb k)
                                      end)
                    None c in match r with
                              | Some p => p
                              | None => nil
                              end.

Lemma pfx_mmeet_singleton : forall (k v: word),
  pfx_mmeet (map.singleton k v) = pfx_emb k.
Proof.
  intros. unfold pfx_mmeet, map.singleton. rewrite map.fold_singleton. reflexivity.
Qed.

Lemma pfx_mmeet_len : forall c, pfx_len (pfx_mmeet c) <= 32.
Proof.
Admitted.

Lemma pfx_mmeet_len_unsigned_word : forall c,
  \[/[pfx_len (pfx_mmeet c)]] = pfx_len (pfx_mmeet c).
Proof.
  intros. apply word.unsigned_of_Z_nowrap.
  pose proof (pfx_mmeet_len c).
  pose proof (pfx_len_nneg (pfx_mmeet c)).
  lia.
Qed.

Ltac pfx_simpl_step :=
  match goal with
  | H: context [ \[/[ pfx_len (pfx_mmeet _) ]] ] |- _ =>
      rewrite pfx_mmeet_len_unsigned_word in H
  | |- context [ \[/[ pfx_len (pfx_mmeet _) ]] ] =>
      rewrite pfx_mmeet_len_unsigned_word
  end.

Lemma pfx_cb_charac : forall (p1 p2: prefix) (n: Z),
  (forall i, 0 <= i < n ->
     exists b, pfx_bit p1 i b /\ pfx_bit p2 i b) ->
  (exists b1 b2, b1 <> b2 /\ pfx_bit p1 n b1 /\ pfx_bit p2 n b2) ->
  pfx_len (pfx_meet p1 p2) = n.
Admitted.

Lemma pfx_emb_inj : forall (k1 k2: word), pfx_emb k1 = pfx_emb k2 -> k1 = k2.
Admitted.

Lemma pfx_bit_inj : forall (p1 p2: prefix),
  pfx_len p1 = pfx_len p2 ->
  (forall i, 0 <= i < pfx_len p1 ->
     exists b, pfx_bit p1 i b /\ pfx_bit p2 i b) ->
  p1 = p2.
Admitted.

Lemma and_1_not_not_1 : forall w1 w2,
  word.and w1 /[1] <> /[1] -> word.and w1 /[1] <> word.and w2 /[1] ->
  word.and w2 /[1] = /[1].
Admitted.

Definition map_filter (c: word_map) (f: word -> bool) :=
  map.fold (fun state k v => if f k then map.put state k v else state)
           map.empty
           c.

Ltac f_apply f H :=
  match type of H with
  | ?lhs = ?rhs =>
      let h := fresh "H" in assert (h: f lhs = f rhs); [ rewrite H; reflexivity | ];
                            cbv beta in h; clear H; rename h into H
  end.

Definition half_subcontent c b :=
  map_filter c (fun k => Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b).

Lemma eq_refl_iff: forall {A : Type} (x : A), (x = x) <-> True.
Proof.
  intros. tauto.
Qed.

Ltac eq_neq_cases k1 k2 :=
  let H := fresh "H" in assert (H: k1 = k2 \/ k1 <> k2) by solve [ steps ]; destruct H.

Ltac none_nnone_cases opt :=
  let H := fresh "H" in assert (H: opt = None \/ opt <> None) by
    solve [ destruct opt; [ right | left ]; congruence ];
  destruct H.

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

Lemma map_get_putmany_not_None_iff: forall (m1 m2: word_map) (k: word),
  map.get (map.putmany m1 m2) k <> None <->
  (map.get m1 k <> None \/ map.get m2 k <> None).
Proof.
  intros. destruct (map.get m2 k) eqn:E.
  - erewrite map.get_putmany_right. 2: eassumption. split. right. tauto. congruence.
  - erewrite map.get_putmany_left. 2: eassumption. tauto.
Qed.

Lemma map_put_putmany_right : forall (m1 m2: word_map) (k v: word),
  map.put (map.putmany m1 m2) k v = map.putmany m1 (map.put m2 k v).
Proof. intros. eapply map.put_putmany_commute. Qed.

Lemma map_put_putmany_left : forall (m1 m2: word_map) (k v: word),
  map.get m2 k = None ->
  map.put (map.putmany m1 m2) k v = map.putmany (map.put m1 k v) m2.
Proof.
  intros. eapply map.map_ext. intros.
  rewrite ?map.get_put_dec, ?map.get_putmany_dec.
  destruct_one_match.
  - rewrite H. rewrite map.get_put_same. reflexivity.
  - destruct_one_match. 1: reflexivity.
    rewrite map.get_put_diff by congruence.
    reflexivity.
Qed.

Lemma pfx_bit_bit_at_emb : forall w i, 0 <= i < 32 -> pfx_bit (pfx_emb w) i (bit_at w i).
Admitted.

Lemma pfx_bit_emb_bit_at : forall w i b, pfx_bit (pfx_emb w) i b -> bit_at w i = b.
Admitted.

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

Ltac my_simpl_step :=
  match goal with
  | H: ?w <> /[0] |- context[ \[?w] =? 0 ] => replace (\[w] =? 0) with false by hwlia
  | H1: ?w <> /[0], H2: context[ \[?w] =? 0 ] |- _ =>
        replace (\[w] =? 0) with false in H2 by hwlia
  | H: map.get (map.singleton ?k ?v) ?k' <> None |- _ =>
        apply map_get_singleton_not_None in H
  | H: map.singleton ?k1 ?v1 = map.singleton ?k2 ?v2 |- _ =>
        apply map_singleton_inj in H
  end.

Ltac my_simpl := cbn; repeat (my_simpl_step; cbn).

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

Ltac add_dummy_mem_def_hyp m := assert (mmap.Def m = mmap.Def m) by reflexivity.

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
  unfold cbt. to_with_mem_hyps. add_dummy_mem_def_hyp m. my_simpl. steps.
Qed.

(*
Lemma and_1_not_1_0: forall w, word.and w /[1] <> /[1] -> word.and w /[1] = /[0].
Proof.
  intros.
  (* zify: *)
  eapply word.unsigned_inj. rewrite word.unsigned_and_nowrap.
  bottom_up_simpl_in_goal.
  eapply word.unsigned_inj' in H.
  rewrite word.unsigned_and_nowrap in H.
  bottom_up_simpl_in_hyp H.
  (* proof purely on Z: *)
  eapply Z.bits_inj'.
  intros.
  rewrite Z.testbit_0_l.
  rewrite Z.land_spec.
  rewrite testbit_1.
  destr (Z.eqb n 0).
  2: eapply Bool.andb_false_r.
  eapply Bool.andb_false_intro1.
  destr (Z.testbit \[w] 0). 2: reflexivity.
  exfalso. apply H. clear H H0.
  eapply Z.bits_inj'.
  intros.
  rewrite Z.land_spec.
  rewrite testbit_1.
  destr (Z.eqb n 0).
  2: eapply Bool.andb_false_r.
  rewrite E. reflexivity.
Qed.
*)

Lemma map_get_putmany_not_left : forall (m1 m2 : word_map) (k : word),
    map.get m1 k = None -> map.get (map.putmany m1 m2) k = map.get m2 k.
Proof.
  intros. destruct (map.get m2 k) eqn:E. erewrite map.get_putmany_right. reflexivity.
  assumption. erewrite map.get_putmany_left; assumption.
Qed.

Lemma map_disjoint_singleton_l: forall (m: word_map) k v,
  map.get m k = None -> map.disjoint (map.singleton k v) m.
Proof.
  intros. unfold map.singleton. apply map.disjoint_put_l. assumption.
  apply map.disjoint_empty_l.
Qed.

Lemma map_disjoint_singleton_r: forall (m: word_map) k v,
  map.get m k = None -> map.disjoint m (map.singleton k v).
Proof.
  intros. unfold map.singleton. apply map.disjoint_put_r. assumption.
  apply map.disjoint_empty_r.
Qed.

Lemma map_putmany_singleton_l: forall (m: word_map) k v,
  map.get m k = None -> map.putmany (map.singleton k v) m = map.put m k v.
Proof.
  intros. unfold map.singleton. rewrite <- map_put_putmany_left.
  rewrite map.putmany_empty_l. reflexivity. assumption.
Qed.

Lemma map_putmany_singleton_r: forall (m: word_map) k v,
  map.putmany m (map.singleton k v) = map.put m k v.
Proof.
  intros. unfold map.singleton. rewrite <- map_put_putmany_right.
  rewrite map.putmany_empty_r. reflexivity.
Qed.

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

Lemma map_filter_extends : forall c f,
  map.extends c (map_filter c f).
Proof.
Admitted.

Lemma half_subcontent_extends : forall c b,
  map.extends c (half_subcontent c b).
Proof.
  intros. apply map_filter_extends.
Qed.

Lemma map_get_extends_nNone : forall (c1 c2: word_map) k,
  map.extends c1 c2 -> map.get c2 k <> None -> map.get c1 k <> None.
Proof.
  intros. unfold map.extends in *. intro. destruct (map.get c2 k) eqn:E; [ | congruence ].
  match goal with
  | Hext: forall _ _, _ -> _ |- _ => apply Hext in E
  end.
  congruence.
Qed.

Lemma half_subcontent_get : forall c b k,
  map.get (half_subcontent c b) k = if Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b
                                    then map.get c k
                                    else None.
Admitted.

Lemma half_subcontent_get_nNone : forall c k,
  map.get c k <> None ->
  map.get (half_subcontent c (bit_at k (pfx_len (pfx_mmeet c)))) k <> None.
Admitted.

Lemma pfx_mmeet_key_le : forall c k,
  map.get c k <> None -> pfx_le (pfx_mmeet c) (pfx_emb k).
Admitted.

Lemma half_subcontent_put_incl : forall c k v b,
  pfx_le (pfx_mmeet c) (pfx_emb k) -> pfx_bit (pfx_emb k) (pfx_len (pfx_mmeet c)) b ->
  half_subcontent (map.put c k v) b = map.put (half_subcontent c b) k v.
Admitted.

Lemma half_subcontent_put_excl_key : forall c k v b,
  pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) < pfx_len (pfx_mmeet c) ->
  bit_at k (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c))) = b ->
  half_subcontent (map.put c k v) b = map.singleton k v.
Admitted.

Lemma half_subcontent_put_excl_bulk : forall c k v b,
  pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) < pfx_len (pfx_mmeet c) ->
  bit_at k (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c))) = negb b ->
  half_subcontent (map.put c k v) b = c.
Admitted.

(*
Lemma half_subcontent_put_excl : forall c k v b1 b2,
  pfx_bit (pfx_emb k) (pfx_len (pfx_mmeet c)) b1 -> b1 <> b2 ->
  half_subcontent (map.put c k v) b2 = half_subcontent c b2.
Admitted.
*)

Lemma half_subcontent_put : forall c k v b,
  half_subcontent (map.put c k v) b =
    if Bool.eqb (bit_at k (pfx_len (pfx_mmeet c))) b then
       map.put (half_subcontent c b) k v
    else
       half_subcontent c b.
Admitted.

Lemma half_subcontent_in_bit : forall c k b,
  map.get (half_subcontent c b) k <> None -> bit_at k (pfx_len (pfx_mmeet c)) = b.
Admitted.

Lemma pfx_mmeet_put : forall c k v,
  c <> map.empty -> pfx_mmeet (map.put c k v) = pfx_meet (pfx_emb k) (pfx_mmeet c).
Admitted.

Lemma pfx_mmeet_put_incl : forall c k v,
  map.get c k <> None -> pfx_mmeet (map.put c k v) = pfx_mmeet c.
Admitted.

Lemma acbt_prefix_length : forall (tree: tree_skeleton) (c: word_map),
    acbt tree c -> match tree with
                   | Node _ _ => pfx_len (pfx_mmeet c) < 32
                   | Leaf => pfx_len (pfx_mmeet c) = 32
                   end.
Proof.
Admitted.

Lemma acbt_nonempty : forall tree c,
  acbt tree c -> c <> map.empty.
Proof.
Admitted.

(*
Ltac raw_bit_to_pfx_impl Hresult :=
  match goal with
  | H: word.and (?k ^>> /[?n]) /[1] = /[1] |- _ => apply pfx_emb_bitop1 in H as Hresult
  | H: word.and (?k ^>> ?w) /[1] = /[1] |- _ =>
    replace w with /[\[w]] in H by hwlia; apply pfx_emb_bitop1 in H as Hresult
  | H: word.and (?k ^>> /[?n]) /[1] <> /[1] |- _ => apply pfx_emb_bitop0 in H as Hresult
  | H: word.and (?k ^>> ?w) /[1] <> /[1] |- _ =>
    replace w with /[\[w]] in H by hwlia; apply pfx_emb_bitop0 in H as Hresult
  end.

Ltac raw_bit_to_pfx :=
  let Hresult := fresh "H" in raw_bit_to_pfx_impl Hresult.

Ltac raw_bit_to_bit_at :=
  let Hresult := fresh "H" in
    (raw_bit_to_pfx_impl Hresult; [ apply pfx_bit_emb_bit_at in Hresult | ]).
*)

Opaque bit_at.

Ltac step_hook ::=
  match goal with
  | |- _ => simple_finish_step

  (* simple logic *)
  | H: ?Q, H2: ?Q -> ?P |- _ => specialize (H2 H)
  | H: ?b = ?a, H2: ?a = ?b -> ?P |- _ => specialize (H2 (eq_sym H))

  | |- _ => comparison_simpl_step
  | |- _ => misc_simpl_step
  | |- _ => subst_step
  | |- _ => small_map_basic_op_simpl_step
  | |- _ => bit_at_step
  | |- _ => pfx_simpl_step

  (* maps *)
  | H: map.split ?cr ?cl1 ?cl2 |- _ =>
       tryif ident_starts_with c cr then destruct H; subst cr else fail
  | H1: ?w = /[0], H2: ?w = /[1] |- _ =>
    rewrite H2 in H1; apply word.of_Z_inj_small in H1
  | |- map.split (map.putmany ?c1 ?c2) ?c1 ?c2 =>
       unfold map.split; split; [ reflexivity | ]
  | H: map.get ?c ?k <> None |- map.get (map.putmany ?c ?c') ?k <> None =>
       apply map_get_putmany_not_None_iff; left; exact H
  | H: map.get ?c ?k <> None |- map.get (map.putmany ?c' ?c) ?k <> None =>
       apply map_get_putmany_not_None_iff; right; exact H
  | |- map.put (map.putmany ?m1 ?m2) ?k ?v = map.putmany ?m1 (map.put ?m2 ?k ?v) =>
       eapply map.put_putmany_commute
  | |- map.put (map.putmany ?m1 ?m2) ?k ?v = map.putmany (map.put ?m1 ?k ?v) ?m2 =>
       eapply map_put_putmany_left
  | H: map.get (map.putmany ?c1 ?c2) ?k = None |- map.get ?c2 ?k = None =>
       eapply map.invert_get_putmany_None; exact H
  | H: map.get (map.putmany ?c1 ?c2) ?k = None |- map.get ?c1 ?k = None =>
       apply map.invert_get_putmany_None in H
  | H: map.disjoint ?c1 ?c2 |- map.disjoint (map.put ?c1 ?k ?v) ?c2 =>
       eapply map.disjoint_put_l
  | H: map.disjoint ?c1 ?c2 |- map.disjoint ?c1 (map.put ?c2 ?k ?v) =>
       eapply map.disjoint_put_r
  | H: map.get ?c2 ?k = None |- map.get (map.putmany ?c1 ?c2) ?k = None =>
       enough (map.get c1 k = None) as Hleftn;
       [ rewrite <- Hleftn; apply map.get_putmany_left; assumption | ]
  | H: map.get ?c1 ?k = None |- context[ map.get (map.putmany ?c1 ?c2) ?k ] =>
    erewrite map_get_putmany_not_left
  | H: map.get ?c2 ?k = None |- context[ map.get (map.putmany ?c1 ?c2) ?k ] =>
    erewrite map.get_putmany_left
  | |- map.get ?c2 ?k = None <-> map.get (map.putmany ?c1 ?c2) ?k = None =>
       rewrite map_get_putmany_not_left
  | H1: map.get ?c2 ?k = None, H2: map.get (map.putmany ?c1 ?c2) ?k <> None
     |- map.get ?c1 ?k <> None =>
     rewrite map.get_putmany_left in H2; [ exact H2 | exact H1 ]
  | |- map.put ?c ?k ?v = map.putmany ?c (map.singleton ?k ?v) =>
       rewrite map_putmany_singleton_r; reflexivity
  | |- map.disjoint ?c (map.singleton ?k ?v) => apply map_disjoint_singleton_r
  | H: map.get ?c ?k = None
    |- map.put ?c ?k ?v = map.putmany (map.singleton ?k ?v) ?c =>
    rewrite map_putmany_singleton_l; [ reflexivity | exact H ]
  | |- map.disjoint (map.singleton ?k ?v) ?c => apply map_disjoint_singleton_l

  (* prefixes *)
  | |- pfx_le ?p ?p => apply pfx_le_reflx
  | H1: pfx_bit ?p1 ?i false, H2: pfx_le ?p1 ?p2, H3: pfx_bit ?p2 ?i true |- _ =>
        exfalso; apply (pfx_bit_not_both p2 i); [ apply (pfx_bit_le p1) | ]
  | H1: pfx_le ?p1 ?p2, H2: pfx_le ?p2 ?p3 |- pfx_le ?p1 ?p3 =>
        apply (pfx_le_trans _ p2 _)
  | |- context[pfx_len (pfx_emb _)] => rewrite pfx_emb_len
  | H: context[pfx_len (pfx_emb _)] |- _ => rewrite pfx_emb_len in H
  | H1: pfx_le ?p1 ?p2, H2: pfx_len ?p2 <= ?n |- pfx_len ?p1 <= ?n =>
        apply pfx_le_len in H1
  | H1: pfx_bit ?p1 ?i true, H2: pfx_le ?p1 ?p2, H3: pfx_bit ?p2 ?i false |- _ =>
       exfalso; apply (pfx_bit_not_both p2 i); [ | apply (pfx_bit_le p1) ]
  (*
  | H: word.and (?k ^>> ?n) /[1] = /[1] |- pfx_bit (pfx_emb ?k) \[?n] true =>
       apply pfx_emb_bitop1
  | H: word.and (?k ^>> ?n) /[1] <> /[1] |- pfx_bit (pfx_emb ?k) \[?n] false =>
       apply pfx_emb_bitop0
  *)
  | H1: pfx_bit ?p1 ?n false, H2: pfx_le ?p1 ?p,
    H3: pfx_bit ?p2 ?n true, H4: pfx_le ?p2 ?p |- _ =>
    exfalso; apply (pfx_bit_not_both p n);
    [ exact (pfx_bit_le _ _ _ _ H2 H1) | exact (pfx_bit_le _ _ _ _ H4 H3) ]
  | |- pfx_le (pfx_meet ?p1 ?p2) ?p1 => apply pfx_meet_le_l
  | |- pfx_le (pfx_meet ?p1 ?p2) ?p2 => apply pfx_meet_le_r
  | H1: pfx_le ?p1 ?p2, H2: pfx_bit ?p1 ?n false, H3: pfx_bit ?p3 ?n true |-
    pfx_len (pfx_meet ?p2 ?p3) <= ?n =>
      apply (pfx_meet_bit_diff_len _ _ _ false true);
      [ apply (pfx_bit_le p1); [ exact H1 | exact H2 ] | exact H3 | congruence ]
  | H1: pfx_le ?p1 ?p2, H2: pfx_bit ?p1 ?n true, H3: pfx_bit ?p3 ?n false |-
    pfx_len (pfx_meet ?p2 ?p3) <= ?n =>
      apply (pfx_meet_bit_diff_len _ _ _ true false);
      [ apply (pfx_bit_le p1); [ exact H1 | exact H2 ] | exact H3 | congruence ]
  | H1: pfx_le ?p1 ?p2, H2: pfx_le ?p2 ?p3
    |- pfx_le (pfx_meet ?p1 ?p4) (pfx_meet ?p3 ?p4) =>
       apply pfx_meet_le_meet_l; apply (pfx_le_trans _ p2); [ exact H1 | exact H2 ]
  | H1: pfx_le ?p1 ?p2, H2: pfx_bit ?p1 ?n ?b |- pfx_bit ?p2 ?n ?b
    => exact (pfx_bit_le _ _ _ _ H1 H2)
  | H1: map.get ?c1 ?k = None, H2: map.get (map.putmany ?c1 ?c2) ?k <> None |-
    map.get ?c2 ?k <> None =>
      rewrite (map_get_putmany_not_left _ _ _ H1) in H2; exact H2
  | H: pfx_le ?p1 (pfx_meet ?p' ?p2) |- pfx_le ?p1 ?p2 =>
       apply (pfx_le_trans _ (pfx_meet p' p2) _); [ exact H | apply pfx_meet_le_r ]
  | |- pfx_meet ?p1 ?p2 = ?p1 => apply pfx_meet_le_eq
  | H: pfx_le ?p1 ?p2 |- pfx_le (pfx_meet ?p1 _) ?p2 =>
       apply (pfx_le_trans _ p1 _); [ apply pfx_meet_le_l | exact H ]
  | H: pfx_le (pfx_app ?p1 ?b) ?p2 |- pfx_bit ?p2 (pfx_len ?p1) ?b
    => exact (pfx_bit_le _ _ _ _ H (pfx_app_bit _ _))
  | H1: pfx_le ?p1 ?p2, H2: pfx_bit ?p2 (pfx_len ?p1) ?b |- pfx_le (pfx_app ?p1 ?b) ?p2
   => exact (pfx_app_le _ _ _ H1 H2)
  | H1: pfx_le ?p1 ?p2, H2: pfx_le ?p0 ?p1, H3: pfx_bit ?p1 (pfx_len ?p0) ?b
      |- pfx_le (pfx_app ?p0 ?b) ?p2 =>
      apply (pfx_le_trans _ p1 _);
      [ apply pfx_app_le; [ exact H2 | exact H3 ] | exact H1 ]
  | H1: pfx_le ?p ?p1, H2: pfx_len (pfx_meet ?p1 ?p2) = pfx_len ?p
      |- pfx_le ?p (pfx_meet ?p1 ?p2) =>
      apply (pfx_lele_len_ord _ _ p1); [ exact H1 | apply pfx_meet_le_l | lia ]
  | H: pfx_le ?p1 ?p2 |- pfx_le (pfx_meet ?p1 ?p') (pfx_meet ?p2 ?p') =>
        exact (pfx_meet_le_meet_l _ _ _ H)
  | |- pfx_le (pfx_meet ?p1 ?p2) ?p2 => apply pfx_meet_le_r
  | H1: pfx_len (pfx_meet ?p1 ?p2) = ?n,
    H2: pfx_bit ?p1 ?n ?b, H3: pfx_bit ?p2 ?n ?b |- _ =>
      apply (pfx_app_le_self (pfx_meet p1 p2) b);
      apply pfx_meet_le_both; apply pfx_app_le;
      [ apply pfx_meet_le_l | rewrite H1; exact H2
      | apply pfx_meet_le_r | rewrite H1; exact H3 ]

  (* content, TODO: sort better *)
  | H: map.get (half_subcontent ?c ?b) ?k <> None |- map.get ?c ?k <> None =>
    exact (map_get_extends_nNone c
                                 (half_subcontent c b)
                                 k
                                 (half_subcontent_extends _ _)
                                 H)
  | |- context[ pfx_mmeet (map.singleton _ _) ] => rewrite pfx_mmeet_singleton
  | |- pfx_bit (pfx_emb ?k) ?i (bit_at ?k ?i) => apply pfx_bit_bit_at_emb
  | H: acbt (Node _ _) ?c |- 0 <= pfx_len (pfx_mmeet ?c) < 32 =>
    apply acbt_prefix_length in H; pose proof (pfx_len_nneg (pfx_mmeet c)); lia
  | H: map.get ?c ?k <> None |- pfx_le (pfx_mmeet ?c) (pfx_emb ?k) =>
    apply pfx_mmeet_key_le; exact H
  | H1: pfx_bit ?p1 ?i false, H2: pfx_bit ?p2 ?i true
    |- pfx_len (pfx_meet ?p1 ?p2) <= ?i
       => apply pfx_meet_bit_diff_len with (b1:=false) (b2:=true);
          [ exact H1 | exact H2 | congruence ]
  | H: pfx_bit (pfx_emb ?k) (pfx_len (pfx_mmeet ?c)) _ |-
    context[ half_subcontent (map.put ?c ?k _) _ ] =>
      rewrite half_subcontent_put; apply pfx_bit_emb_bit_at in H; rewrite H
  | |- context[ if false then _ else _ ] => cbv iota
  | |- context[ if true then _ else _ ] => cbv iota
  | H: bit_at ?k (pfx_len (pfx_mmeet ?c)) = _ |-
    context[ half_subcontent (map.put ?c ?k _) _] =>
      rewrite half_subcontent_put; rewrite H
  | H: map.get ?c ?k <> None |- context[ pfx_mmeet (map.put ?c ?k _) ] =>
       rewrite (pfx_mmeet_put_incl _ _ _ H)
  | H: context[ pfx_mmeet (map.singleton _ _) ] |- _ => rewrite pfx_mmeet_singleton in H
  | H: bit_at ?k (pfx_len (pfx_mmeet ?c)) = _
    |- context[ map.get (half_subcontent ?c _) ?k ] =>
      rewrite half_subcontent_get; rewrite H
  | H1: acbt (Node _ _) ?c, H2: /[pfx_len (pfx_mmeet ?c)] = /[32] |- _ =>
    apply acbt_prefix_length in H1; pose proof (pfx_len_nneg (pfx_mmeet c)); hwlia

  (* misc *)
  | |- /[match ?opt1 with | Some _ => ?vs | None => ?vn end] =
       /[match ?opt2 with | Some _ => ?vs | None => ?vn end] =>
     enough (opt1 = None <-> opt2 = None); [ destruct opt1; destruct opt2;
     intuition congruence | ]
  | H1: word.and ?w1 /[1] <> /[1], H2: word.and ?w1 /[1] <> word.and ?w2 /[1]
    |- word.and ?w2 /[1] = /[1] => apply (and_1_not_not_1 w1 w2)
  | |- _ => my_simpl_step
  | |- map.split _ _ _ => unfold map.split
end.

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
  split; intros; destruct tree; simpl cbt' in *; steps; subst c; steps.
Qed.

Ltac destruct_in_putmany :=
  match goal with
  | H: map.get (map.putmany _ _) _ <> None |- _ =>
       apply map_get_putmany_not_None_iff in H; destruct H
  end.

Ltac hyps_to_with_mem := repeat match goal with
  | H: ?P ?m |- _ => apply to_with_mem in H
  end.

Lemma du_def_split : forall (m m1 : mem) (mm: mmap mem),
    mm ||| m1 = m -> exists m2 : mem, mm = m2 /\ map.split m m2 m1.
Proof.
  intros. pose proof H. unfold "|||" in H0. destruct mm eqn:E. exists m0.
  split. reflexivity. apply split_du. assumption. discriminate.
Qed.

Lemma manual_du_on_sep : forall (m m1 m2: mem) (P Q : mem -> Prop),
    P m1 -> Q m2 -> mmap.du m1 m2 = m -> sep P Q m.
Proof.
  steps. change (P m1) with (m1 |= P) in H.
  change (Q m2) with (m2 |= Q) in H0. steps.
Qed.

Ltac destruct_split H :=
  try apply split_du in H; unfold map.split in H; destruct H.

Ltac provide_new_ghosts_hook ::= manual_new_ghosts.

Definition map_some_key (c: word_map) default := map.fold (fun _ k _ => k) default c.

Lemma map_some_key_singleton : forall k v k', map_some_key (map.singleton k v) k' = k.
Proof.
  intros. unfold map_some_key, map.singleton. apply map.fold_singleton.
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
    (eapply map_get_extends_nNone; [ eapply half_subcontent_extends | eauto ]).
Qed.

Lemma eq_None_by_false {X : Type}: forall o: option X, ~(o <> None) -> o = None.
Proof.
  intros. destruct o. exfalso. apply H. congruence. congruence.
Qed.

Set Ltac Profiling.
Reset Ltac Profile.

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
  destruct (word.eqb retv k) eqn:E; simpl cbt'; steps.
  subst k.
  assert (map.get c retv <> None). {
  match goal with
  | H: _ = retv |- _ => rewrite <- H
  end.
  eapply map_get_extends_nNone. eapply half_subcontent_extends.
  eapply cbt_best_lookup_in. steps. }
  steps. .**/
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
  destruct (word.eqb retv k) eqn:E; simpl cbt'; steps.
  subst k.
  assert (map.get c retv <> None). {
  match goal with
  | H: _ = retv |- _ => rewrite <- H
  end.
  eapply map_get_extends_nNone. eapply half_subcontent_extends.
  eapply cbt_best_lookup_in. steps. }
  steps. .**/
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

Show Ltac Profile.

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
  steps. clear Error. simpl cbt'. steps. .**/
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
  instantiate (5:=/[12]).
  (* TODO: move to `step_hook` (?) *) replace \[/[12]] with 12 by hwlia.
  steps. .**/
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

(*
Lemma cbt_nonempty : forall sk pr c tp m,
  cbt' sk pr c tp m -> exists k, map.get c k <> None.
Proof.
  induction sk; intros; simpl in H.
  - steps. subst. steps.
  - repeat heapletwise_step.
    match goal with
    | IH: context[ cbt' sk2 _ _ _ _ -> _ ], H: _ |= cbt' sk2 _ _ _ |- _ =>
      apply IH in H
    end.
    steps. instantiate (1:=k). steps.
Qed.
*)

Ltac one_not_one_cases w :=
  let Hmone := fresh "Hmone" in assert (Hmone: w = /[1] \/ w <> /[1]) by hwlia;
  destruct Hmone.

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
  symmetry. apply pfx_cb_charac.
  { steps. apply pfx_bit_bit_at_emb. steps.
  match goal with | H: forall _, _ |- _ => rewrite H end.
  apply pfx_bit_bit_at_emb. steps. steps. }
  { steps. 2: apply pfx_bit_bit_at_emb; steps. 2: apply pfx_bit_bit_at_emb; steps.
  unzify. destruct_or. assert (Hui: \[i] = 31) by lia. rewrite Hui in *. intro.
  match goal with
  | H: k1 <> k2 |- _ => apply H
  end.
  apply bit_at_inj. intros. assert (Hcmp: i0 = 31 \/ i0 < 31) by lia. destruct Hcmp.
  { steps. } { match goal with | H: forall _, _ |- _ => apply H end. lia. }
  steps. }
Qed.

Lemma pfx_bit_meet : forall p1 p2 i b,
  pfx_bit p1 i b /\ pfx_bit p2 i b <-> pfx_bit (pfx_meet p1 p2) i b.
Admitted.

Lemma cbt_best_lookup_cb_not_node : forall sk c k,
  acbt sk c -> pfx_len (pfx_mmeet c) < 32 -> pfx_le (pfx_mmeet c) (pfx_emb k) ->
  pfx_len (pfx_mmeet c) <
    pfx_len (pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))).
Proof.
  intros. destruct sk.
  - simpl acbt in *. steps.
  - match goal with | |- pfx_len ?lhs < pfx_len ?rhs => assert (pfx_le lhs rhs) end.
    { apply pfx_meet_le_both; steps. apply pfx_mmeet_key_le. apply cbt_best_lookup_in.
    steps. }
    match goal with
    | |- _ < pfx_len ?rhs =>
      assert (Hlp: pfx_le (pfx_app (pfx_mmeet c) (bit_at k (pfx_len (pfx_mmeet c)))) rhs)
    end.
    { apply pfx_app_le. steps. apply pfx_bit_meet. steps.
    eassert (Hpb: pfx_bit _ _ _). {
      apply (pfx_bit_bit_at_emb (cbt_best_lookup (Node sk1 sk2) c k)
                                (pfx_len (pfx_mmeet c))).
      pose proof (pfx_len_nneg (pfx_mmeet c)). lia. } simpl cbt_best_lookup in *.
    simpl acbt in *. steps. destruct (bit_at k (pfx_len (pfx_mmeet c))) eqn:E;
    (eassert (Hbeq: bit_at _ _ = _); [ | rewrite Hbeq in Hpb; exact Hpb ];
    apply half_subcontent_in_bit; apply cbt_best_lookup_in; steps). }
    apply pfx_le_len in Hlp. rewrite pfx_app_len in Hlp. lia.
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
  (* move k' before Scope1. *)
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
      subst k'. apply cbt_best_lookup_in. steps. steps. steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *.
  match goal with
  | H1: bit_at ?k ?i = _, H2: context[ if bit_at ?k ?i then _ else _ ] |- _ =>
    rewrite H1 in H2; cbv iota in H2
  end.
  subst k'. steps. instantiate (1:=Node sk1 sk'). simpl cbt'. clear Error. steps.
  rewrite pfx_mmeet_put.
  replace (pfx_meet (pfx_emb k) (pfx_mmeet c)) with (pfx_mmeet c). steps. symmetry.
  steps. rewrite pfx_meet_comm. steps.
  (* TODO: collect *)
  match goal with
  | H: acbt _ ?c |- ?c <> map.empty => apply acbt_nonempty in H; exact H
  end. .**/
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
      subst k'. apply cbt_best_lookup_in. steps. steps. steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *.
  match goal with
  | H1: bit_at ?k ?i = _, H2: context[ if bit_at ?k ?i then _ else _ ] |- _ =>
    rewrite H1 in H2; cbv iota in H2
  end.
  subst k'. steps. instantiate (1:=Node sk' sk2). simpl cbt'. clear Error. steps.
  rewrite pfx_mmeet_put.
  replace (pfx_meet (pfx_emb k) (pfx_mmeet c)) with (pfx_mmeet c). steps. symmetry.
  steps. rewrite pfx_meet_comm. steps.
  (* already COLLECTED *)
  match goal with
  | H: acbt _ ?c |- ?c <> map.empty => apply acbt_nonempty in H; exact H
  end. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == 0) /* split */ {                                           /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**.
  clear Error. destruct sk; simpl cbt' in *; steps. .**/
  else {                                                                     /**. .**/
    uintptr_t new_node = Malloc(12);                                         /**. .**/
    if (new_node == 0) /* split */ {                                         /**. .**/
      return 0;                                                              /**. .**/
    }                                                                        /**.
  clear Error. destruct sk; simpl cbt' in *; steps. .**/
    else {                                                                   /**. .**/
      store(new_node, load(p));                                              /**. .**/
      store(new_node + 4, load(p + 4));                                      /**. .**/
      store(new_node + 8, load(p + 8));                                      /**. .**/
      store(p, cb);                                                          /**. .**/
      if (((k >> cb) & 1) == 1) /* split */ {                                /**. .**/
        store(p + 4, new_node);                                              /**. .**/
        store(p + 8, new_leaf);                                              /**. .**/
        return tp;                                                           /**. .**/
      }                                                                      /*?.
  repeat clear_array_0. subst. steps.
  clear Error. instantiate (1:=Node sk Leaf). simpl cbt'.
  repeat match goal with
  | H: merge_step _ |- _ => clear H
  end.
  assert (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) = \[cb]). {
    assert (pfx_meet (pfx_emb k) (pfx_mmeet c)
            = pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))). {
      apply pfx_le_asym. apply pfx_meet_le_meet_r. apply pfx_mmeet_key_le.
      (* TODO: collect *)
      match goal with
      | H: acbt ?sk ?c |- map.get ?c (cbt_best_lookup ?sk ?c _) <> None =>
        apply cbt_best_lookup_in; exact H
      end.
      apply pfx_meet_le_both. steps.
      apply pfx_lele_len_ord with (pfx_emb (cbt_best_lookup sk c k)). steps.
      apply pfx_mmeet_key_le.
      (* already COLLECTED *)
      match goal with
      | H: acbt ?sk ?c |- map.get ?c (cbt_best_lookup ?sk ?c _) <> None =>
        apply cbt_best_lookup_in; exact H
      end. lia.
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
  unfold split_concl_at, canceling. simpl seps. split; [ | apply I ]. intros.
  apply sep_comm. clear D. (* TODO: investigate why this D appears *)
  simpl cbt' in *. steps. subst. apply half_subcontent_put_excl_key. lia.
  congruence. steps. unfold split_concl_at.
  destruct sk; simpl cbt' in *; steps. subst. steps. rewrite pfx_mmeet_put.
  steps. eapply acbt_nonempty. eassumption. symmetry.
  apply half_subcontent_put_excl_bulk. lia. steps. congruence.
   (* TODO: investigate why many duplicated hypotheses *)
   (* TODO (not local to here): remove/modify the application of
      half_subcontent_put_incl in step_hook because of the added hypothesis *) .**/
      else {                                                                  /**. .**/
        store(p + 4, new_leaf);                                               /**. .**/
        store(p + 8, new_node);                                               /**. .**/
        return tp;                                                            /**. .**/
      }                                                                       /*?.
  repeat clear_array_0. subst. steps.
  clear Error. instantiate (1:=Node Leaf sk). simpl cbt'.
  repeat match goal with
  | H: merge_step _ |- _ => clear H
  end.
  assert (pfx_len (pfx_meet (pfx_emb k) (pfx_mmeet c)) = \[cb]). {
    assert (pfx_meet (pfx_emb k) (pfx_mmeet c)
            = pfx_meet (pfx_emb k) (pfx_emb (cbt_best_lookup sk c k))). {
      apply pfx_le_asym. apply pfx_meet_le_meet_r. apply pfx_mmeet_key_le.
      (* already COLLECTED *)
      match goal with
      | H: acbt ?sk ?c |- map.get ?c (cbt_best_lookup ?sk ?c _) <> None =>
        apply cbt_best_lookup_in; exact H
      end.
      apply pfx_meet_le_both. steps.
      apply pfx_lele_len_ord with (pfx_emb (cbt_best_lookup sk c k)). steps.
      apply pfx_mmeet_key_le.
      (* already COLLECTED *)
      match goal with
      | H: acbt ?sk ?c |- map.get ?c (cbt_best_lookup ?sk ?c _) <> None =>
        apply cbt_best_lookup_in; exact H
      end. lia.
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
  subst. apply half_subcontent_put_excl_key. lia. congruence.
  unfold split_concl_at. destruct sk; simpl cbt' in *; steps. subst. steps.
  rewrite pfx_mmeet_put. steps. eapply acbt_nonempty. eassumption. symmetry.
  apply half_subcontent_put_excl_bulk. lia. steps. congruence. .**/
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
  }                                                                        /**.
  subst. unfold map.singleton. steps. .**/
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

(* NOTE: the three lemmas below have the exact same assumptions
         (the idea is that we are removing key `k` from content `c` and the
          lemmas are only valid if
          `half_subcontent c (bit_at k (pfx_len (pfx_mmeet c)))` contains other
          keys than just `k`) *)

(* TODO: collect *)
Lemma pfx_mmeet_remove_unchanged : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  pfx_mmeet (map.remove c k) = pfx_mmeet c.
Admitted.

(* TODO: collect *)
Lemma half_subcontent_remove_same : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  half_subcontent (map.remove c k) b = map.remove (half_subcontent c b) k.
Admitted.

(* TODO: collect *)
Lemma half_subcontent_remove_other : forall c k b,
  bit_at k (pfx_len (pfx_mmeet c)) = b ->
  map.remove (half_subcontent c b) k <> map.empty ->
  half_subcontent (map.remove c k) (negb b) = half_subcontent c (negb b).
Admitted.

(* TODO: collect *)
Lemma half_subcontent_removed_half_leaf : forall c k v b,
  half_subcontent c b = map.singleton k v ->
  half_subcontent c (negb b) = map.remove c k.
Admitted.

(* TODO: collect *)
Lemma map_extends_remove_in_both : forall (cbig clittle: word_map) k,
  map.extends cbig clittle -> map.extends (map.remove cbig k) (map.remove clittle k).
Proof.
  unfold map.extends. intros. eq_neq_cases k x.
  - subst. rewrite map.get_remove_same in *. discriminate.
  - rewrite map.get_remove_diff in *. auto. congruence. congruence.
Qed.

(* TODO: collect *)
Lemma map_extends_nonempty : forall (cbig clittle: word_map),
  map.extends cbig clittle -> clittle <> map.empty -> cbig <> map.empty.
Proof.
  unfold map.extends. intros. intro.
  match goal with
  | H: clittle <> map.empty |- _ => apply H
  end. apply map.map_ext. steps. destruct (map.get clittle k) eqn:E;
  [ exfalso | reflexivity ].
  match goal with
  | H: forall _, _ |- _ => apply H in E
  end.
  steps.
Qed.

(* added `try tauto` to be able to derive `acbt` predicates *)
Ltac clear_pure_hyp_if_derivable h tp ::=
  tryif ident_starts_with __pure_ h then
    try (clear h; assert_succeeds (idtac; assert tp
        by (try tauto; zify_goal; xlia zchecker)))
    else idtac.

#[export] Instance spec_of_cbt_delete_from_nonleaf: fnspec :=                          .**/

uintptr_t cbt_delete_from_nonleaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (skL skR: tree_skeleton) (c: word_map)
                (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' (Node skL skR) c tp
                     * R }> m;
  ensures t' m' res := t' = t
                /\ if word.eqb res /[0] then
                      map.get c k = None
                   else
                      map.get c k <> None
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
  if (((k >> load(par)) & 1) == 1) {                                       /**. .**/
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
  | H1: ?mL |= cbt' skL _ _,
    H2: ?mR |= cbt' skR _ _ |- _ =>
    remember (if brc then mR else mL) as mcur;
    remember (if brc then mL else mR) as msib;
    assert (mcur |= cbt' skC (half_subcontent c brc) cur) by (destruct brc; congruence);
    assert (msib |= cbt' skS (half_subcontent c (negb brc)) sib)
       by (destruct brc; simpl negb; congruence)
  end.

  match goal with
  | H: _ |= sepapps _ ?pp |- _ =>
       replace aL with (if brc then sib else cur) in H by (destruct brc; congruence);
       replace aR with (if brc then cur else sib) in H by (destruct brc; congruence);
       replace pp with par in H by congruence
  end.
  Ltac purge x := repeat match goal with
                         | H: context[ x ] |- _ => clear H
                         end; clear x.
  purge aL. purge aR. purge skL. purge skR.

  rewrite mmap.du_comm in D. rewrite <- mmap.du_assoc in D.
  rewrite <- mmap.du_assoc in D.
  replace ((m2 ||| m1) ||| m3) with (m2 ||| mcur ||| msib) in D; cycle 1.
  do 2 rewrite mmap.du_assoc. f_equal. subst mcur. subst msib.
  destruct brc. apply mmap.du_comm. reflexivity.
  purge m1. purge m3.

  match goal with
  | H: merge_step _ |- _ => clear H
  end.
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
  end.
  unfold ready. (* `unfold ready` so that `steps` doesn't finish immediately *)
  steps. } .**/
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
  unpurify. steps.
  apply eq_None_by_false. intro HnN. apply half_subcontent_get_nNone in HnN.
  apply HnN. subst brc. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).
  unpurify. destruct brc eqn:E; simpl cbt'; steps.
  (* TODO: below, more or less the same proof is repeated several (6) times.
           Simplify? *)
  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps. rewrite Hhcr.
  steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  rewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k false) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ false). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps. .**/
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
  (*
  Set Ltac Profiling.
  Reset Ltac Profile.
  *)

  steps. apply eq_None_by_false. intro HnN.
  apply half_subcontent_get_nNone in HnN. apply HnN. subst brc. steps.
  clear Error. instantiate (1:=if brc then Node skS sk' else Node sk' skS).

  destruct brc eqn:E; simpl cbt'; unpurify; steps.

  (*
  Show Ltac Profile.
  Reset Ltac Profile.
  *)

  (* steps. (* this `steps.` is now a few lines above *)*)
  (* this `steps.` takes very long
     measurement 1: with `unpurify.` before the `steps.`   26 s
     measurement 2: without unpurify                       55 s
     measurement 3: with unpurify                           9 s
     measurement 4: without unpurify                       55 s

     profiling shows that most time is spent on `xlia`
   *)

  (* Show Ltac Profile. *)

    (* TODO: below, more or less the same proof is repeated several (6) times.
           Simplify? (as before) *)

  pose proof (half_subcontent_remove_other c k true) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=true). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite half_subcontent_remove_same. steps. congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  pose proof (half_subcontent_remove_other c k false) as Hhcr. steps.
  rewrite Hhcr. steps. eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps.

  erewrite pfx_mmeet_remove_unchanged. steps. instantiate (1:=false). congruence.
  eapply map_extends_nonempty. eapply map_extends_remove_in_both.
  eapply (half_subcontent_extends _ true). rewrite map.remove_not_in.
  eapply acbt_nonempty. eassumption. rewrite half_subcontent_get. steps. .**/
  }                                                                        /**.
  destruct skC; cycle 1. { exfalso.
  repeat match goal with
  | H: acbt (Node _ _) _ |- _ => apply acbt_prefix_length in H
  end. pose proof (pfx_len_nneg (pfx_mmeet (half_subcontent c brc))). hwlia. } .**/
  if (load(cur + 4) == k) /* split */ {                                    /**.
  match goal with
  | H: _ |= cbt' _ _ sib |- _ => apply cbt_expose_fields in H
  end. repeat heapletwise_step.
  .**/
    cbt_raw_node_free(cur);                                                /**. .**/
    store(par, load(sib));                                                 /**. .**/
    store(par + 4, load(sib + 4));                                         /**. .**/
    store(par + 8, load(sib + 8));                                         /**. .**/
    cbt_raw_node_free(sib);                                                /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**.
  hwlia.
  eapply map_get_extends_nNone. apply half_subcontent_extends.
  match goal with
  | H: half_subcontent _ _ = map.singleton _ _ |- _ => rewrite H
  end. steps.
  clear Error. instantiate (1:=skS).
  replace (map.remove c k) with (half_subcontent c (negb brc)); cycle 1.
  { eapply half_subcontent_removed_half_leaf. eassumption. }
  repeat match goal with
  | H: merge_step _ |- _ => clear H
  end.
  repeat match goal with
  | H: context[hole 4] |- _ => match type of H with
                               | ?m |= _ => unfold sepapps in H; simpl in H;
                                            unfold sepapp in H; unfold "|=", hole in H
                               end
  end. repeat heapletwise_step.
  destruct skS; simpl cbt'; steps.
  match goal with
  | H: half_subcontent c (negb brc) = map.singleton _ _ |- _ => rewrite H
  end. steps. .**/
  else {                                                                   /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
  apply eq_None_by_false. intro HnN. apply half_subcontent_get_nNone in HnN.
  match goal with
  | H: brc = bit_at _ _ |- _ => rewrite <- H in HnN
  end.
  match goal with
  | H: half_subcontent c brc = map.singleton _ _ |- _ => rewrite H in HnN
  end. steps. .**/
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
                    (* TODO: make this more specific to guarantee more
                             1 instead of just a non-zero *)
                /\ if word.eqb res /[0] then
                      map.get c k = None
                   else
                      map.get c k <> None
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
      }                                                                    /**.
  hwlia.
  (* TODO: move this into a tactic *)
  repeat match goal with
  | H: context[hole 4] |- _ => match type of H with
                               | ?m |= _ => unfold sepapps in H; simpl in H;
                                            unfold sepapp in H; unfold "|=", hole in H
                               end
  end. steps. .**/
      else {                                                               /**. .**/
        return 0;                                                          /**. .**/
      }                                                                    /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**.
  destruct tree. { exfalso. steps. } .**/
      uintptr_t ret = cbt_delete_from_nonleaf(tp, k);                      /**.
  simpl cbt'. clear Error. steps. unfold enable_frame_trick.enable_frame_trick.
  steps. .**/
      return ret;                                                          /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
