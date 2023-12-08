(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Require Coq.Bool.Bool.

(* some parts of this file are based on tree_set.v (binary search trees) *)

Inductive tree_skeleton: Set :=
| Leaf
| Node(leftChild rightChild: tree_skeleton).

Definition tree_skeleton_lt(sk1 sk2: tree_skeleton): Prop :=
  match sk2 with
  | Node leftChild rightChild => sk1 = leftChild \/ sk1 = rightChild
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


Load LiveVerif.

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

Definition bit_at (w: word) (i: Z) := Z.testbit \[w] i.

Fixpoint pfx'_emb_rec (w: word) (remaining: nat) :=
  match remaining with
  | O => nil
  | S n => cons (bit_at w (32 - Z.of_nat remaining)) (pfx'_emb_rec w n)
  end.

Definition pfx_emb (w: word) := pfx'_emb_rec w 32.


Lemma pfx_emb_len : forall (w: word), pfx_len (pfx_emb w) = 32.
Admitted.

(* TODO: use List.get instead of Znth *)
Definition pfx_bit (p: prefix) (i: Z) (b: bool) :=
  0 <= i < len p /\ List.Znth i p b = b.

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

Lemma pfx_emb_bitop0 : forall (w: word) (i: Z), 0 <= i < 32 ->
    word.and (w ^>> /[i]) /[1] <> /[1] <-> pfx_bit (pfx_emb w) i false.
Admitted.

Lemma pfx_emb_bitop1 : forall (w: word) (i: Z), 0 <= i < 32 ->
    word.and (w ^>> /[i]) /[1] = /[1] <-> pfx_bit (pfx_emb w) i true.
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

Lemma pfx_meet_le_r : forall (p1 p2: prefix), pfx_le (pfx_meet p1 p2) p2.
Admitted.

Lemma pfx_meet_le_both : forall (p p1 p2: prefix),
                         pfx_le p p1 -> pfx_le p p2 -> pfx_le p (pfx_meet p1 p2).
Admitted.

Lemma pfx_meet_bit_diff_len : forall (p1 p2: prefix) (i: Z) (b1 b2: bool),
  pfx_bit p1 i b1 -> pfx_bit p2 i b2 -> b1 <> b2 -> pfx_len (pfx_meet p1 p2) <= i.
Admitted.

Lemma pfx_meet_le_eq : forall (p1 p2: prefix),
  pfx_le p1 p2 -> pfx_meet p1 p2 = p1.
Admitted.

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

Context {consts: malloc_constants}.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

Ltac f_apply f H :=
  match type of H with
  | ?lhs = ?rhs =>
      let h := fresh "H" in assert (h: f lhs = f rhs); [ rewrite H; reflexivity | ];
                            cbv beta in h; clear H; rename h into H
  end.

(* no need to use word (record) for ghost: might use positive *)
Fixpoint cbt' (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word): mem -> Prop :=
  match sk with
    | Leaf => EX (k: word) (v: word),
        <{ * emp (a <> /[0])
           * freeable 12 a
           * <{ + uintptr /[-1] (* uint 32 (2 ^ 32 - 1) *)
                + uintptr k
                + uintptr v }> a
           * emp (p = pfx_emb k)
           * emp (c = map.singleton k v) }>
  | Node skL skR => EX (aL: word) (pL: prefix) (cL: word_map)
                       (aR: word) (pR: prefix) (cR: word_map),
          <{ * emp (a <> /[0])
             * freeable 12 a
             * <{ + uintptr /[pfx_len p] (* uint 32 p.(length) *)
                  + uintptr aL
                  + uintptr aR }> a
             * cbt' skL pL cL aL
             * cbt' skR pR cR aR
             * emp (pfx_le p pL)
             * emp (pfx_bit pL (pfx_len p) false)
             * emp (pfx_le p pR)
             * emp (pfx_bit pR (pfx_len p) true)
             * emp (map.split c cL cR) }>
  end.

Definition nncbt (c: word_map) (a: word): mem -> Prop := EX sk p, cbt' sk p c a.

(* in full generality, a CBT can be represented as a pointer which is either
   - NULL for an empty CBT, or
   - pointing to the CBT root node *)
Definition cbt (c: word_map) (a: word): mem -> Prop :=
  if \[a] =? 0 then emp (c = map.empty) else nncbt c a.

Lemma eq_refl_iff: forall {A : Type} (x : A), (x = x) <-> True.
Proof.
  intros. tauto.
Qed.

Lemma map_get_singleton_same : forall (k v: word),
  map.get (map.singleton k v) k = Some v.
Proof.
  intros. unfold map.singleton. apply map.get_put_same.
Qed.

Lemma map_get_singleton_same_eq : forall (k v k': word),
  k' = k -> map.get (map.singleton k v) k' = Some v.
Proof.
  intros. subst k'. apply map_get_singleton_same.
Qed.

Lemma map_get_singleton_diff : forall (k k' v : word),
  k' <> k -> map.get (map.singleton k v) k' = None.
Proof.
  intros. unfold map.singleton. rewrite map.get_put_diff. apply map.get_empty.
  assumption.
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
  intros. eq_neq_cases k k'; [ trivial | exfalso ].
  rewrite map_get_singleton_diff in H; congruence.
Qed.

Lemma map_put_singleton_same_eq : forall (k v k' v': word),
  k' = k -> map.put (map.singleton k v) k' v' = map.singleton k v'.
Proof.
  intros. unfold map.singleton. subst k'. apply map.put_put_same.
Qed.

Lemma map_singleton_inj : forall (k1 k2 v1 v2 : word),
    map.singleton k1 v1 = map.singleton k2 v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros. unfold map.singleton in *. assert (k1 = k2).
  assert (k1 = k2 \/ k1 <> k2). step. destruct H0; [ trivial | exfalso ].
  f_apply (fun m: word_map => map.get m k2) H. rewrite map.get_put_same in H.
  rewrite map.get_put_diff in H. rewrite map.get_empty in H. discriminate.
  auto. subst k1. steps. f_apply (fun m: word_map => map.get m k2) H.
  repeat rewrite map.get_put_same in H. congruence.
Qed.

Ltac my_simpl_step :=
  match goal with
  | |- context [ \[/[0]] ] => rewrite word.unsigned_of_Z_0
  | H: ?w <> /[0] |- context[ \[?w] =? 0 ] => replace (\[w] =? 0) with false by hwlia
  | H1: ?w <> /[0], H2: context[ \[?w] =? 0 ] |- _ =>
        replace (\[w] =? 0) with false in H2 by hwlia
  | H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
        rewrite map_get_singleton_same_eq in H; [ | solve [ trivial ] ]
  | |- context [ map.get (map.singleton ?k ?v) ?k']  =>
        rewrite map_get_singleton_same_eq; [ | solve [ trivial ] ]
  | H: context [ map.get (map.singleton ?k ?v) ?k' ] |- _ =>
        rewrite map_get_singleton_diff in H; [ | solve [ trivial ] ]
  | |- context [ map.get (map.singleton ?k ?v) ?k' ] =>
        rewrite map_get_singleton_diff; [ | solve [ trivial ] ]
  | H: context [ map.put (map.singleton ?k ?v) ?k' ?v' ] |- _ =>
        rewrite map_put_singleton_same_eq in H; [ | solve [ trivial ] ]
  | |- context [ map.put (map.singleton ?k ?v) ?k' ?v' ] =>
        rewrite map_put_singleton_same_eq; [ | solve [ trivial ] ]
  | H: context [ map.get map.empty ?k ] |- _ => rewrite map.get_empty in H
  | |- context [ map.get map.empty ?k ] => rewrite map.get_empty
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

(* needed because the other notation contains a closing C comment *)
Notation "a ||| b" := (mmap.du a b) (at level 34, no associativity).

Require Import coqutil.Tactics.ident_ops.

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

Ltac step_hook ::=
  match goal with

  (* simple logic / equalities *)
  | H: ?P |- ?P => exact H
  | |- ?P <-> ?P => reflexivity
  | H1: ?P, H2: ~?P |- _ => apply H2 in H1; destruct H1
  | H: ?x <> ?x |- _ => exfalso; apply (H (eq_refl x))
  | H: ?Q, H2: ?Q -> ?P |- _ => specialize (H2 H)
  | H: ?b = ?a, H2: ?a = ?b -> ?P |- _ => specialize (H2 (eq_sym H))
  | |- Some ?v <> None => congruence
  | H1: ?n = 0, H2: context[ ?n =? 0 ] |- _ =>
    replace (n =? 0) with true in H2 by lia
  | H1: ?n <> 0, H2: context[ ?n =? 0 ] |- _ =>
    replace (n =? 0) with false in H2 by lia
  | |- context[ ?n =? ?n ] => rewrite Z.eqb_refl
  | H: context[ ?n =? ?n ] |- _ => rewrite Z.eqb_refl in H

  (* words *)
  | |- context[word.eqb ?w ?w] => rewrite word.eqb_eq; [ | reflexivity ]
  | H: ?w1 <> ?w2 |- context[word.eqb ?w1 ?w2] => rewrite word.eqb_ne; [ | assumption ]
  | |- context[/[\[ _ ]]] => rewrite word.of_Z_unsigned

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
  | H: ?k1 <> ?k2 |- context[map.get (map.singleton ?k1 _) ?k2] =>
      rewrite map_get_singleton_diff; [ | congruence ]
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
  | H: word.and (?k ^>> ?n) /[1] = /[1] |- pfx_bit (pfx_emb ?k) \[?n] true =>
       apply pfx_emb_bitop1
  | H: word.and (?k ^>> ?n) /[1] <> /[1] |- pfx_bit (pfx_emb ?k) \[?n] false =>
       apply pfx_emb_bitop0
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

Lemma weak_purify_cbt' :
  forall sk p c a, purify (cbt' sk p c a) (a <> /[0] (* /\ 0 <= length p <= 32 *)).
Proof.
  unfold purify. intros. destruct sk; simpl cbt' in *; steps; subst; cbn; steps.
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

Hint Resolve weak_purify_cbt' : purify.

Local Hint Extern 1 (PredicateSize (cbt' ?sk)) => exact 12 : typeclass_instances.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | cbt' ?sk2 ?p2 ?c2 =>
      lazymatch hypPred with
      | cbt' ?sk1 ?p1 ?c1 =>
          (* Note: address has already been checked, and if sk and/or s don't
             unify, sidecondition solving steps will make them match later,
             so here, we just need to take care of instantiating evars from conclPred *)
          try syntactic_unify_only_inst_r p1 p2;
          try syntactic_unify_only_inst_r c1 c2;
          try syntactic_unify_only_inst_r sk1 sk2
      end
  end.

Lemma cbt_expose_fields (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word):
  impl1 (cbt' sk p c a) (EX w2 w3,
    <{ * freeable 12 a
       * <{ + uintptr /[match sk with | Leaf => -1 | Node _ _ => pfx_len p end]
            + uintptr w2
            + uintptr w3 }> a
       * emp (a <> /[0])
       * match sk with
         | Leaf => <{ * emp (p = pfx_emb w2)
                      * emp (c = map.singleton w2 w3) }>
         | Node skL skR => EX pL cL pR cR,
                         <{ * cbt' skL pL cL w2
                            * cbt' skR pR cR w3
                            * emp (pfx_le p pL)
                            * emp (pfx_bit pL (pfx_len p) false)
                            * emp (pfx_le p pR)
                            * emp (pfx_bit pR (pfx_len p) true)
                            * emp (map.split c cL cR) }>
         end
                                                              }>).
Proof.
  unfold impl1. intro m. intros. destruct sk; simpl cbt' in *; steps.
Qed.

Ltac destruct_in_putmany :=
  match goal with
  | H: map.get (map.putmany _ _) _ <> None |- _ =>
       apply map_get_putmany_not_None_iff in H; destruct H
  end.

Lemma cbt_key_has_prefix : forall (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word) (m: mem) (k: word),
    cbt' sk p c a m -> map.get c k <> None -> pfx_le p (pfx_emb k).
Proof.
  induction sk; intros; simpl cbt' in *; steps.
  - subst. steps. subst. steps.
  - destruct_in_putmany;
    match goal with
    | Hcontains: map.get ?c _ <> None, Hcbt: _ |= cbt' ?sk _ ?c _,
      IH: context[ cbt' ?sk _ _ _ _ -> _ ] |- _ => eapply IH in Hcbt; [ | eassumption ]
    end;
    steps.
Qed.

Lemma cbt_prefix_length : forall (sk: tree_skeleton) (p: prefix) (c: word_map)
                                 (a: word) (m: mem) (k: word),
    cbt' sk p c a m -> pfx_len p <= 32.
Proof.
  induction sk; intros; simpl cbt' in *; steps.
  - subst.
    steps.
  - match goal with
    | Hcbt: _ |= cbt' ?sk _ _ _, IH: context[cbt' ?sk _ _ _ _ -> _] |- _ =>
         eapply IH in Hcbt; [ | eassumption ]
    end.
    steps.
Qed.



Lemma purify_cbt' :
  forall sk p c a, purify (cbt' sk p c a)
                   (a <> /[0] /\
                   match sk with
                   | Leaf => pfx_len p = 32
                   | Node _ _ => 0 <= pfx_len p < 32
                   end
                   /\ forall k, map.get c k <> None -> pfx_le p (pfx_emb k)).
Proof.
  unfold purify. steps.
  3: eauto using cbt_key_has_prefix.
  all: destruct sk; simpl cbt' in *; steps; subst; steps.
  assert (pfx_len pL <= 32) by (eauto using cbt_prefix_length).
  eassert _. eapply pfx_bit_len with (p:=pL). eassumption. lia.
Qed.

Remove Hints weak_purify_cbt' : purify.
Hint Resolve purify_cbt' : purify.

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

(*
Ltac in_content_to_prefix :=
  match goal with
  | H1: context[ map.get ?c _ <> None -> is_prefix_key _ _ ],
    H2: map.get ?c _ <> None |- _ =>
    apply H1 in H2
  end.
*)

Definition closest_key_in (c: word_map) (k_target k_close: word) :=
  map.get c k_close <> None /\
  (forall k, map.get c k <> None ->
  pfx_le (pfx_meet (pfx_emb k) (pfx_emb k_target))
         (pfx_meet (pfx_emb k_close) (pfx_emb k_target))).

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Lemma eq_None_by_false {X : Type}: forall o: option X, ~(o <> None) -> o = None.
Proof.
  intros. destruct o. exfalso. apply H. congruence. congruence.
Qed.

Ltac raw_bit_to_pfx :=
  match goal with
  | H: word.and (?k ^>> /[?n]) /[1] = /[1] |- _ => apply pfx_emb_bitop1 in H
  | H: word.and (?k ^>> ?w) /[1] = /[1] |- _ =>
    replace w with /[\[w]] in H by hwlia; apply pfx_emb_bitop1 in H
  | H: word.and (?k ^>> /[?n]) /[1] <> /[1] |- _ => apply pfx_emb_bitop0 in H
  | H: word.and (?k ^>> ?w) /[1] <> /[1] |- _ =>
    replace w with /[\[w]] in H by hwlia; apply pfx_emb_bitop0 in H
  end.

Ltac apply_key_prefix_hyp :=
  match goal with
  | Hq: context[ map.get ?c _ <> None -> pfx_le _ (pfx_emb _) ],
    Hc: map.get ?c _ <> None |- _ =>
    apply Hq in Hc
  end.

(*
#[export] Instance spec_of_cbt_update_or_best: fnspec :=                        .**/

uintptr_t cbt_update_or_best(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt' sk pr c tp
                     * R }> m;
  ensures t' m' res := t' = t /\ closest_key_in c k res /\
                <{ * cbt' sk pr (if word.eqb res k then map.put c k v else c) tp * R }> m' #**/     /**.
Derive cbt_update_or_best SuchThat (fun_correct! cbt_update_or_best)
  As cbt_update_or_best_ok. .**/
{                                                                            /**. .**/
  uintptr_t p = tp;                                                          /**.

  (* setting up the loop precondition *)
  rewrite <- Def0 in H0.
  move t before tp.
  rewrite <- Def0. rewrite Def0 at 2.
  delete #(p = ??).
  move sk at bottom.
  move c after Scope1.
  move R after Scope1.
  move pr after Scope1.
  loop invariant above m.
                                                                                .**/
  while (load(p) != -1) /* initial_ghosts(p, pr, c, R); decreases sk */ {  /*?.
  subst v0.
  instantiate (3:=(match sk with | Leaf => ?[vLeaf] | _ => ?[vNode] end)).
  destruct sk; cycle 1. simpl cbt' in *. steps. .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                             /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pR, cR, <{ * R
                           * freeable 12 p'
                           * cbt' sk1 pL cL aL
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr aL
                                + uintptr p }> p' }>).
  step. steps. step. steps. step.
  assert (map.get cL retv = None). { apply eq_None_by_false. intro.
  unfold closest_key_in in *. fwd. do 2 apply_key_prefix_hyp. steps. }
  steps. unfold closest_key_in in *. steps.
  destruct_in_putmany. apply_key_prefix_hyp. steps.
  apply (pfx_le_trans _ (pfx_meet pr (pfx_emb k)) _).
  apply pfx_meet_le_both. apply (pfx_lele_len_ord _ _ (pfx_emb k0)); steps.
  raw_bit_to_pfx. steps. steps. steps. apply_key_prefix_hyp. steps.
  match goal with
  | H: forall _, map.get cR _ <> None -> pfx_le (pfx_meet _ _) _ |- _ => apply H
  end.
  steps.
  destruct (word.eqb retv k) eqn:E; steps.
  destruct (word.eqb retv k) eqn:E; steps; subst; steps. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pL, cL, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 pR cR aR
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr p
                                + uintptr aR }> p' }>).
  step. steps. step. steps. step.
  assert (map.get cR retv = None). { apply eq_None_by_false. intro.
  unfold closest_key_in in *. fwd. do 2 apply_key_prefix_hyp. steps. }
  steps. unfold closest_key_in in *. steps. destruct_in_putmany. steps.
  match goal with
  | H: forall _, map.get cL _ <> None -> pfx_le (pfx_meet _ _) _ |- _ => apply H
  end. steps.
  apply_key_prefix_hyp.
  steps. apply (pfx_le_trans _ (pfx_meet pr (pfx_emb k)) _).
  apply pfx_meet_le_both. apply (pfx_lele_len_ord _ _ (pfx_emb k0)); steps.
  raw_bit_to_pfx. steps. steps. steps. apply_key_prefix_hyp. steps.
  destruct (word.eqb retv k) eqn:E; steps; subst; steps.
  destruct (word.eqb retv k) eqn:E; steps; subst; steps. .**/
  }                                                                          /**.
  simpl cbt' in *. steps. .**/
    if (load(p + 4) == k) /* split */ {                                       /**. .**/
    store(p + 8, v);                                                        /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  unfold closest_key_in. steps; subst; steps; subst; steps. subst; steps. .**/
  else {                                                                    /**. .**/
    return load(p + 4);                                                     /**. .**/
  }                                                                         /**.
  unfold closest_key_in. steps; subst; steps; subst; steps. .**/
}                                                                           /**.
Qed.

#[export] Instance spec_of_cbt_lookup_impl: fnspec :=                           .**/
uintptr_t cbt_lookup_impl(uintptr_t tp, uintptr_t k, uintptr_t val_out) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map)
                (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * cbt' sk pr c tp
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = /[match map.get c k with | Some _ => 1 | None => 0 end])
                 * cbt' sk pr c tp
                 * uintptr (match map.get c k with
                            | Some v => v
                            | None => val_out_orig
                            end) val_out
                 * R }> m'         #**/                                     /**.
Derive cbt_lookup_impl SuchThat (fun_correct! cbt_lookup_impl)
  As cbt_lookup_impl_ok.                                                         .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  (* unfold ready. *)
  rewrite <- Def0 in *. rewrite Def0 at 2.
  delete #(p = ??).
  move pr after Scope1.
  move p after Scope1.
  move R after Scope1.
  move c after Scope1.
  match goal with
  | H: _ |= R |- _ => move H at bottom
  end.
  match goal with
  | H: _ |= cbt' _ _ _ _ |- _ => loop invariant above H
  end.
  move sk at bottom.
  .**/
  while (load(p) != -1) /* initial_ghosts(p,pr,c,R); decreases sk */ {           /*?.
  subst v.
  instantiate (3:=(match sk with | Leaf => ?[vLeaf] | _ => ?[vNode] end)).
  destruct sk; cycle 1. simpl cbt' in *. steps. .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                             /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pR, cR, <{ * R
                           * freeable 12 p'
                           * cbt' sk1 pL cL aL
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr aL
                                + uintptr p }> p' }>).
  assert (map.get cL k = None).
  { apply eq_None_by_false. intro. apply_key_prefix_hyp. raw_bit_to_pfx.
  steps. steps. } steps. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pL, cL, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 pR cR aR
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr p
                                + uintptr aR }> p' }>).
  assert (map.get cR k = None).
  { apply eq_None_by_false. intro. apply_key_prefix_hyp. raw_bit_to_pfx.
  steps. steps. } steps. .**/
  }                                                                          /**.
  simpl cbt' in *. steps. .**/
  if (load(p + 4) == k) /* split */ {                                        /**. .**/
    store(val_out, load(p + 8));                                             /**. .**/
    return 1;                                                                /**. .**/
  }                                                                          /**.
  subst. steps. subst. steps. .**/
  else {                                                                     /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**.
  subst. steps. subst. steps. .**/
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
  }                                                                         /**.
  subst. steps. subst. steps. .**/
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
                        * cbt' Leaf (pfx_emb k) (map.singleton k v) res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_alloc_leaf SuchThat (fun_correct! cbt_alloc_leaf) As cbt_alloc_leaf_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = Malloc(12);                                                /**. .**/
  if (p == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    store(p, -1);                                                          /**.
    clear H4. .**/
    store(p + 4, k);                                                       /**. .**/
    store(p + 8, v);                                                       /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /*?.
  repeat clear_array_0. simpl cbt'. steps. .**/
}                                                                          /**.
Qed.

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

Ltac one_not_one_cases w :=
  let Hmone := fresh "Hmone" in assert (Hmone: w = /[1] \/ w <> /[1]) by hwlia;
  destruct Hmone.

#[export] Instance spec_of_critical_bit: fnspec :=                              .**/

uintptr_t critical_bit(uintptr_t k1, uintptr_t k2) /**#
  (* heaplet packaging doesn't work well then there's just one item in the heap *)
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
  assert (forall n, 0 <= n < \[i] ->
           exists b, pfx_bit (pfx_emb k1) n b /\ pfx_bit (pfx_emb k2) n b).
  intros. hwlia.
  delete #(i = /[0]).
  loop invariant above H.
  move i at bottom. .**/
  while (i < 31 && ((k1 >> i & 1) == ((k2 >> i & 1))))
    /* decreases (32 - \[i]) */ {                                          /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /*?.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step.
  assert (Hcmp: n = \[i'] \/ n < \[i']) by hwlia. destruct Hcmp.
  one_not_one_cases (word.and (k1 ^>> i') /[1]).
  exists true. steps. subst. steps. subst. steps.
  assert (word.and (k2 ^>> i') /[1] = /[1]) by congruence. steps. subst.
  exists false. steps.
  assert (word.and (k2 ^>> i') /[1] <> /[1]) by congruence. steps.
  match goal with
  | H: forall _, _ |- _ => apply H
  end.
  steps. steps. steps. .**/
  return i;                                                                /**. .**/
}                                                                          /**.
  assert (word.and (k1 ^>> i) /[1] <> word.and (k2 ^>> i) /[1]).
  unzify. destruct_or; [ | assumption ]. assert (Hui: \[i] = 31) by lia.
  rewrite Hui in *. intro.
  match goal with
  | H: k1 <> k2 |- _ => apply H
  end.
  apply pfx_emb_inj. apply pfx_bit_inj. steps. intros. step.
  assert (Hcmp: i0 = 31 \/ i0 < 31) by lia. destruct Hcmp. subst.
  one_not_one_cases (word.and (k1 ^>> i) /[1]); rewrite <- Hui.
  exists true. steps. assert (word.and (k2 ^>> i) /[1] = /[1]) by congruence. steps.
  exists false. steps. assert (word.and (k2 ^>> i) /[1] <> /[1]) by congruence. steps.
  match goal with
  | H: forall _, _ |- _ => apply H
  end.
  steps.
  symmetry. apply pfx_cb_charac. steps.
  one_not_one_cases (word.and (k1 ^>> i) /[1]).
  exists true. exists false. steps.
  assert (word.and (k2 ^>> i) /[1] <> /[1]) by congruence. steps.
  exists false. exists true. steps.
  assert (word.and (k2 ^>> i) /[1] = /[1]).
  steps. steps.
Qed.

#[export] Instance spec_of_cbt_insert_at: fnspec :=                             .**/

uintptr_t cbt_insert_at(uintptr_t tp, uintptr_t cb, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' sk pr c tp
                     * R }> m
                  /\ 0 <= \[cb] < 32
                  /\ exists k',
                       (map.get c k' <> None /\
                           pfx_len (pfx_meet (pfx_emb k') (pfx_emb k)) = \[cb])
                  /\ forall k',
                       (map.get c k' <> None ->
                           pfx_len (pfx_meet (pfx_emb k') (pfx_emb k)) <= \[cb]);
  ensures t' m' res := t' = t
                       /\ if \[res] =? 0 then
                            <{ * allocator_failed_below 12
                               * cbt' sk pr c tp
                               * R
                               * (fun _ => True) }> m'
                          else
                            (* `id` is a hack to identify this occurrence when
                                rewriting *)
                            res = id tp /\
                            (EX sk',
                              <{ * allocator
                                 * cbt' sk' (pfx_meet pr (pfx_emb k)) (map.put c k v) tp
                                 * R }>) m' #**/ /**.
Derive cbt_insert_at SuchThat (fun_correct! cbt_insert_at) As cbt_insert_at_ok.  .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  assert (Htpnn: tp <> /[0]).
  (* would move to the step hook, but purify_cbt' not available there yet *)
  match goal with
  | H: _ |= cbt' _ _ _ ?tp |- ?tp <> /[0] => apply purify_cbt' in H; tauto
  end.
  move Htpnn after Scope1.
  rewrite <- Def0 in H2.
  move t before tp.
  rewrite <- Def0. rewrite Def0 at 2. replace (id p) with tp.
  delete #(p = ??).
  move sk at bottom.
  move k' before Scope1.
  move p before Scope1.
  loop invariant above m.
                                                                                .**/
  while (load(p) < cb)
    /* initial_ghosts(p, pr, c, R); decreases sk */
  {                                                                        /*?.
  subst v0.
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ _ |- _ => apply cbt_expose_fields in H
  end. steps.
  destruct sk; [ exfalso | ]. steps.
  .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                            /**. .**/
      p = load(p + 8);                                                      /**. .**/
    }                                                                       /**.
  new_ghosts(p, pR, cR, <{ * R
                           * freeable 12 p'
                           * cbt' sk1 pL cL w2
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr w2
                                + uintptr p }> p' }>).
  instantiate (1:=sk2). step. step. steps.
  assert (map.get cL k' = None). { apply eq_None_by_false. intro.
  enough (\[cb] <= pfx_len pr) by hwlia.
  match goal with
  | H: _ = \[cb] |- _ => rewrite <- H
  end.
  apply_key_prefix_hyp. raw_bit_to_pfx. subst.
  assert (pfx_bit (pfx_emb k') (pfx_len pr) false) by steps. steps. steps. }
  steps.
  match goal with
  | H: forall _, _ -> pfx_len _ <= \[cb] |- _ => apply H
  end. steps.
  step. steps. unfold state_implication. steps.
  match goal with
  | H: context[expect_1expr_return] |- _ => destruct H
  end.
  steps.
  assert (pfx_le pr (pfx_emb k)). {
  assert (pfx_le pr (pfx_emb k')).
  destruct_in_putmany; apply_key_prefix_hyp; steps.
  assert (pfx_le pr (pfx_meet (pfx_emb k') (pfx_emb k))).
  apply (pfx_lele_len_ord _ _ (pfx_emb k')); steps. steps. }
  assert (Hnewpr: pfx_meet pr (pfx_emb k) = pr) by steps.
  econstructor. eassumption. simpl cbt' in *. step. step. steps. step. steps.
  step. step. step. step. step. step. step. step. step. step. steps. step.
  instantiate (1:=Node sk1 sk'). simpl cbt'. steps. rewrite Hnewpr. steps.
  rewrite Hnewpr. enough (pfx_le (pfx_app pr true) (pfx_meet pR (pfx_emb k))).
  steps. apply pfx_meet_le_both. steps. raw_bit_to_pfx. steps. steps.
  apply eq_None_by_false. intro. steps. apply_key_prefix_hyp. raw_bit_to_pfx. steps.
  steps. rewrite Hnewpr. steps. .**/
    else {                                                                    /**. .**/
      p = load(p + 4);                                                        /**. .**/
    }                                                                         /**.
  new_ghosts (p, pL, cL,
      <{ * R
         * freeable 12 p'
         * <{ + uintptr /[pfx_len pr]
              + uintptr p
              + uintptr w3 }> p'
         * cbt' sk2 pR cR w3 }>).
  instantiate (1:=sk1). step. step. steps.
  assert (map.get cR k' = None). { apply eq_None_by_false. intro.
  enough (\[cb] <= pfx_len pr) by hwlia.
  match goal with
  | H: _ = \[cb] |- _ => rewrite <- H
  end.
  apply_key_prefix_hyp. raw_bit_to_pfx. subst.
  assert (pfx_bit (pfx_emb k') (pfx_len pr) true) by steps. steps. steps. }
  steps. steps.
  match goal with
  | H: forall _, _ -> pfx_len _ <= \[cb] |- _ => apply H
  end. steps.
  step. steps. unfold state_implication. steps.
  match goal with
  | H: context[expect_1expr_return] |- _ => destruct H
  end.
  steps.
  assert (pfx_le pr (pfx_emb k)). {
  assert (pfx_le pr (pfx_emb k')).
  destruct_in_putmany; apply_key_prefix_hyp; steps.
  assert (pfx_le pr (pfx_meet (pfx_emb k') (pfx_emb k))).
  apply (pfx_lele_len_ord _ _ (pfx_emb k')); steps. steps. }
  assert (Hnewpr: pfx_meet pr (pfx_emb k) = pr) by steps.
  assert (map.get cR k = None). { apply eq_None_by_false. intro. steps.
  apply_key_prefix_hyp. raw_bit_to_pfx. steps. steps. }
  steps.
  econstructor. eassumption. simpl cbt' in *. step. step. steps. step. steps.
  step. step. step. step. step. step. step. step. step. step. steps. step.
  instantiate (1:=Node sk' sk2). simpl cbt'. steps. rewrite Hnewpr.
  enough (pfx_le (pfx_app pr false) (pfx_meet pL (pfx_emb k))).
  steps. apply pfx_meet_le_both. steps. raw_bit_to_pfx. steps. steps.
  rewrite Hnewpr. steps. rewrite Hnewpr. steps. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == 0) /* split */ {                                           /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /*?.
  step. step. steps. step. step. destruct sk; simpl cbt' in *; steps. .**/
  else {                                                                     /**. .**/
    uintptr_t new_node = Malloc(12);                                         /**. .**/
    if (new_node == 0) /* split */ {                                         /**. .**/
      return 0;                                                              /**. .**/
    }                                                                        /*?.
  step. step. step. step. step. steps. step. destruct sk; simpl cbt' in *; steps. .**/
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
  assert (Hcbpr: \[cb] < pfx_len pr). {
    destruct sk. steps.
    assert (Hcmp: \[cb] < pfx_len pr \/ \[cb] = pfx_len pr) by hwlia.
    destruct Hcmp; [ assumption | exfalso ]. steps. subst.
    match goal with
    | H: _ |= cbt' _ _ cR _ |- _ => apply cbt_nonempty in H
    end. fwd.
    assert (pfx_len (pfx_meet (pfx_emb k0) (pfx_emb k)) <= \[cb]). {
    match goal with
    | H: forall _, map.get _ _ <> None -> _ <= _ |- _ => apply H
    end. steps. }
    enough (Hlem: pfx_le (pfx_app pr true) (pfx_meet (pfx_emb k0) (pfx_emb k))).
    apply pfx_le_len in Hlem. rewrite pfx_app_len in Hlem. lia.
    do 2 apply_key_prefix_hyp.
    apply pfx_meet_le_both. steps. raw_bit_to_pfx.
    match goal with
    | H: \[cb] = _ |- _ => rewrite H in *
    end.
    assert (pfx_le pr (pfx_emb k)). {
    assert (pfx_le pr (pfx_meet (pfx_emb k') (pfx_emb k))). steps. steps. }
    steps. steps.
  }
  assert (pfx_le pr (pfx_emb k')). {
    destruct sk; steps; subst; steps; subst; steps.
    destruct_in_putmany; apply_key_prefix_hyp; steps.
  }
  assert (Hprmk: pfx_len (pfx_meet pr (pfx_emb k)) = \[cb]). {
    match goal with
    | H: _ = \[cb] |- _ => rewrite <- H
    end.
    f_equal. apply pfx_le_asym. steps.
    apply pfx_meet_le_both. apply (pfx_lele_len_ord _ _ (pfx_emb k')); steps.
    steps.
  }
  assert (Hcknone: map.get c k = None). {
    apply eq_None_by_false. intro. do 2 apply_key_prefix_hyp.
    assert (Hprk: pfx_meet pr (pfx_emb k) = pr). steps. rewrite <- Hprk in Hcbpr.
    lia. }
  step. step. step. step. step. steps. step. steps. step.
  instantiate (1:=Node sk Leaf). simpl cbt'. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. instantiate (2:=c). instantiate (4:=pr).
  repeat clear_array_0. simpl cbt' in *. repeat heapletwise_step.
  unfold canceling. unfold seps. split; [ | apply I]. intros.
  apply sep_comm. step. step. step. step. step. step. instantiate (5:=k0).
  instantiate (4:=v0). step. step. step. step. step. step. step. step.
  instantiate (1:=pfx_emb k). step. instantiate (1:=map.singleton k v).
  step. step. step. step. step. step. step. subst.
  rewrite Hprmk. raw_bit_to_pfx.
  destruct (pfx_bit_or pr \[cb]). steps. steps. exfalso.
  steps. steps. step. steps. step. rewrite Hprmk. raw_bit_to_pfx.
  steps. steps. step. steps. step.
  clear D. (* without clearing D, some heaplets appear in multiple equations,
              which the canceling tactics don't like

              (I think that my `unfold state_implication` could be the root cause *)
  destruct sk; simpl cbt' in *; steps. .**/

      else {                                                                  /**. .**/
        store(p + 4, new_leaf);                                               /**. .**/
        store(p + 8, new_node);                                               /**. .**/
        return tp;                                                            /**. .**/
      }                                                                       /*?.
  assert (Hcbpr: \[cb] < pfx_len pr). {
    destruct sk. steps.
    assert (Hcmp: \[cb] < pfx_len pr \/ \[cb] = pfx_len pr) by hwlia.
    destruct Hcmp; [ assumption | exfalso ]. steps. subst.
    match goal with
    | H: _ |= cbt' _ _ cL _ |- _ => apply cbt_nonempty in H
    end. fwd.
    assert (pfx_len (pfx_meet (pfx_emb k0) (pfx_emb k)) <= \[cb]). {
    match goal with
    | H: forall _, map.get _ _ <> None -> _ <= _ |- _ => apply H
    end. steps. }
    enough (Hlem: pfx_le (pfx_app pr false) (pfx_meet (pfx_emb k0) (pfx_emb k))).
    apply pfx_le_len in Hlem. rewrite pfx_app_len in Hlem. lia.
    do 2 apply_key_prefix_hyp.
    apply pfx_meet_le_both. steps. raw_bit_to_pfx.
    match goal with
    | H: \[cb] = _ |- _ => rewrite H in *
    end.
    assert (pfx_le pr (pfx_emb k)). {
    assert (pfx_le pr (pfx_meet (pfx_emb k') (pfx_emb k))). steps. steps. }
    steps. steps.
  }
  assert (pfx_le pr (pfx_emb k')). {
    destruct sk; steps; subst; steps; subst; steps.
    destruct_in_putmany; apply_key_prefix_hyp; steps.
  }
  assert (Hprmk: pfx_len (pfx_meet pr (pfx_emb k)) = \[cb]). {
    match goal with
    | H: _ = \[cb] |- _ => rewrite <- H
    end.
    f_equal. apply pfx_le_asym. steps.
    apply pfx_meet_le_both. apply (pfx_lele_len_ord _ _ (pfx_emb k')); steps.
    steps.
  }
  assert (Hcknone: map.get c k = None). {
    apply eq_None_by_false. intro. do 2 apply_key_prefix_hyp.
    assert (Hprk: pfx_meet pr (pfx_emb k) = pr). steps. rewrite <- Hprk in Hcbpr.
    lia. }
  step. step. step. step. step. steps. step. steps. step.
  instantiate (1:=Node Leaf sk). simpl cbt'. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step.
  instantiate (7:=c). instantiate (6:=pr).
  step. step. step. step. step. steps. step.
  repeat clear_array_0. simpl cbt' in *. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step.
  instantiate (1:=k). step. step. step. instantiate (1:=v). step. step.
  unfold canceling. unfold seps. split; [ | apply I]. intros. apply sep_comm.
  step. step. steps. step. rewrite Hprmk. steps. rewrite Hprmk. subst.
  raw_bit_to_pfx. step. steps. step.
  destruct (pfx_bit_or pr \[cb]). steps. exfalso.
  steps. steps. step. steps. step.
  clear D. destruct sk; simpl cbt' in *; steps. steps. steps. steps. .**/
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
  subst. steps. subst. unfold map.singleton. steps. .**/
  else {                                                                   /**. .**/
  uintptr_t best_k = cbt_update_or_best(tp, k, v);                         /**. .**/
    if (best_k == k) /* split */ {                                         /**. .**/
      return tp;                                                           /**. .**/
    }                                                                      /**.
  subst. steps. .**/
    else {                                                                 /**. .**/
      uintptr_t cb = critical_bit(k, best_k);                              /**.
  instantiate (3:=emp True). steps.
  unfold enable_frame_trick.enable_frame_trick. steps. .**/
      uintptr_t result = cbt_insert_at(tp, cb, k, v);                      /**.
  instantiate (1:=best_k). unfold closest_key_in in *. steps.
  unfold closest_key_in in *. rewrite pfx_meet_comm. steps. steps.
  unfold closest_key_in in *. fwd.
  match goal with
  | H: \[cb] = _ |- _ => rewrite pfx_meet_comm in H; rewrite H
  end.
  apply pfx_le_len.
  match goal with
  | H: forall _, map.get _ _ <> None -> pfx_le _ _ |- _ => apply H
  end.
  steps. unfold enable_frame_trick.enable_frame_trick. steps. .**/
      return result;                                                       /**. .**/
    }                                                                      /**.
  replace (\[result] =? 0) with false by steps. unfold id in *. steps. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.
*)

#[export] Instance spec_of_cbt_delete_from_nonleaf: fnspec :=                          .**/

uintptr_t cbt_delete_from_nonleaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (skL skR: tree_skeleton) (pr: prefix) (c: word_map)
                (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' (Node skL skR) pr c tp
                     * R }> m;
  ensures t' m' res := t' = t
                /\ if word.eqb res /[0] then
                      map.get c k = None
                   else
                      map.get c k <> None
                /\ <{ * allocator
                      * (EX sk' pr', cbt' sk' pr' (map.remove c k) tp)
                      * R }> m' #**/                                       /**.
Derive cbt_delete_from_nonleaf SuchThat
  (fun_correct! cbt_delete_from_nonleaf) As cbt_delete_from_nonelaf_ok.         .**/
{                                                                          /**. .**/
  uintptr_t cur = 0;                                                       /**. .**/
  uintptr_t sib = 0;                                                       /**. .**/
  uintptr_t par = tp;                                                   /**.
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
  (* shouldn't merge_step disappear? *)
  loop invariant above cR. (* move cR after Scope2. *)
  remember (if c then skR else skL) as skC. (* move skC after Scope2. *)
  remember (if c then skL else skR) as skS. move skS after Scope2.
  remember (if c then pR else pL) as pC. move pC after Scope2.
  remember (if c then pL else pR) as pS. move pS after Scope2.
  remember (if c then cR else cL) as cC. move cC after Scope2.
  remember (if c then cL else cR) as cS. move cS after Scope2.
  move cur after Scope2. move sib after Scope2. move pr before Scope2.
  move R before Scope2.

  match goal with
  | H: _ |= cbt' skL ?pp ?cc ?aa |- _ =>
       replace (cbt' skL pp cc aa)
         with (if c then cbt' skS pS cS sib else cbt' skC pC cC cur: mem -> Prop)
         in H
         by (destruct c; congruence)
  end.
  match goal with
  | H: _ |= cbt' skR ?pp ?cc ?aa |- _ =>
       replace (cbt' skR pp cc aa)
         with (if c then cbt' skC pC cC cur else cbt' skS pS cS sib: mem -> Prop)
         in H
         by (destruct c; congruence)
  end.
  match goal with
  | H: _ |= <{ + _ + uintptr aL + uintptr aR }> ?pp |- _ =>
       replace aL with (if c then sib else cur) in H by (destruct c; congruence);
       replace aR with (if c then cur else sib) in H by (destruct c; congruence);
       replace pp with par in H by congruence
  end.
  Ltac purge x := repeat match goal with
                         | H: context[ x ] |- _ => clear H
                         end; clear x.
  purge aL. purge aR. purge pL. purge pR. purge skL. purge skR.
  replace (map.putmany cL cR) with (map.putmany cC cS).
  2: {
  subst cC cS. destruct c; steps.
  (* TODO: collect *)
  match goal with
  | H: map.disjoint ?c1 ?c2 |- map.putmany ?c2 ?c1 = map.putmany ?c1 ?c2 =>
       symmetry; apply map.putmany_comm; exact H
  end.
  }
  purge cL. purge cR.
  match goal with
  | H: merge_step _ |- _ => clear H
  end.
  match goal with
  | H: par = tp |- _ => rewrite <- H in *; rewrite H at 2; clear H
  end.
  delete #(0 <= pfx_len pr < 32).
  .**/
  (* TODO: define a current sk/pr/c and sibling sk/pr/c ? *)
  while (load(cur) != -1) /* initial_ghosts(pC, cC, cur, skS, pS, cS, sib, pr, par, R);
    decreases skC */ {  /**.

  clear Error.
  (* rename par' into par. *)
  split.
  destruct c;
  match goal with
  | H: _ |= cbt' _ _ _ cur |- _ => apply cbt_expose_fields in H
  end;
  steps; unfold seps; steps.
  steps. destruct skC; [ exfalso; hwlia | ]. .**/
    par = cur;                                                             /**. .**/
    if (((k >> load(cur)) & 1) == 1) /* split */ {                         /**.
  clear Error.
  split.
  destruct c;
  match goal with
  | H: _ |= cbt' _ _ _ cur |- _ => simpl cbt' in H (* apply cbt_expose_fields in H *)
  end;
  steps; unfold seps; steps. steps.
  match goal with
  | H1: ?ma |= (if c then cbt' _ _ _ sib else _),
    H2: ?mb |= (if c then cbt' ?skcur _ _ cur else _)
    |- _ =>
    let Hcur := fresh "Hcur" in
    assert (Hcur: (if c then mb else ma) |= cbt' skcur pC cC cur)
      by (destruct c; congruence);
    assert (Hsib: (if c then ma else mb) |= cbt' skS pS cS sib)
      by (destruct c; congruence);
    clear H1 H2;
    simpl cbt' in Hcur  (*
    apply cbt_expose_fields in Hcur *)
  end.
  repeat heapletwise_step.
  (* assert (c=true). subst c. apply word.eqb_eq. steps. *)
  .**/
      sib = load(cur + 4);                                                 /**.
  clear Error. split. instantiate (1:=aL).
  destruct c; steps; unfold seps; steps. steps. .**/
      cur = load(cur + 8);                                                 /**.
  clear Error. split. instantiate (1:=aR).
  destruct c; steps; unfold seps; steps. steps. .**/
    }                                                                      /**.
  new_ghosts(_, _, _, _, _, _, _, pC, _, <{ * R
                                            * freeable 12 par'
                                            * <{ + uintptr _
                                                 + uintptr (if c then _ else _)
                                                 + uintptr (if c then _ else _) }> par'
                                            * cbt' _ _ _ sib' }>).
  (* TODO: collect *)
  match goal with
  | H: ?a = ?b |- context[ word.eqb ?a ?b ] =>
      replace (word.eqb a b) with true by (symmetry; apply word.eqb_eq; exact H)
  end. steps. destruct c; steps. destruct c; steps. destruct c; steps.

  Search cS. (* <-- processing this causes
  Backtrace:

  Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/.
  *)


  step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step.
; steps. subst
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step.
 steps. step. step. step. step. step. step. step. step. step. steps.
    else {                                                                 /**.

  match goal with
  | H: _ |= cbt' _ _ cL _ |- _ => apply cbt_expose_fields in H
  end.
  match goal with
  | H: _ |= cbt' _ _ cR _ |- _ => apply cbt_expose_fields in H
  end.



End LiveVerif. Comments .**/ //.
