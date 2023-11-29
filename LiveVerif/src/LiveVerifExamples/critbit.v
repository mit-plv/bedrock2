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

(* TODO *)
Definition bit_at (w: word) (i: Z) := false.
Opaque bit_at.

Fixpoint pfx'_emb_rec (w: word) (remaining: nat) :=
  match remaining with
  | O => nil
  | S n => cons (bit_at w (32 - Z.of_nat remaining)) (pfx'_emb_rec w n)
  end.

Definition pfx_emb (w: word) := pfx'_emb_rec w 32.

Lemma pfx_emb_len : forall (w: word), pfx_len (pfx_emb w) = 32.
Admitted.

Definition pfx_bit (p: prefix) (i: Z) (b: bool) :=
  0 <= i < len p /\ List.Znth i p b = b.

Lemma pfx_bit_excl : forall (p: prefix) (i: Z), ~pfx_bit p i false \/ ~pfx_bit p i true.
Admitted.

Lemma pfx_bit_not_both :
  forall (p: prefix) (i: Z), pfx_bit p i false -> pfx_bit p i true -> False.
Admitted.

Lemma pfx_bit_or : forall (p: prefix) (i: Z),
                   0 <= i < len p -> pfx_bit p i false \/ pfx_bit p i true.
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

Definition pfx_app (p: prefix) (b: bool) := p ++ cons b nil.

Lemma pfx_app_le : forall (p1 p2: prefix) (b: bool),
                   pfx_le p1 p2 -> pfx_bit p1 (pfx_len p2) b ->
                   pfx_le (pfx_app p1 b) p2.
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

Lemma pfx_meet_le_r : forall (p1 p2: prefix), pfx_le (pfx_meet p1 p2) p2.
Admitted.

Lemma pfx_meet_le_both : forall (p p1 p2: prefix),
                         pfx_le p p1 -> pfx_le p p2 -> pfx_le p (pfx_meet p1 p2).
Admitted.

Lemma pfx_cb_charac : forall (p1 p2: prefix) (n: Z),
  (forall i, 0 <= i < n ->
     exists b, pfx_bit p1 i b /\ pfx_bit p2 i b) ->
  (exists b1 b2, b1 <> b2 /\ pfx_bit p1 n b1 /\ pfx_bit p2 n b2) ->
  pfx_len (pfx_meet p1 p2) = n.
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

  (* word simplification *)
  | |- context[word.eqb ?w ?w] => rewrite word.eqb_eq; [ | reflexivity ]
  | H: ?w1 <> ?w2 |- context[word.eqb ?w1 ?w2] => rewrite word.eqb_ne; [ | assumption ]
  | |- context[/[\[ _ ]]] => rewrite word.of_Z_unsigned

  (* expressions with maps *)
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

  (* prefixes *)
  | |- pfx_le ?p ?p => apply pfx_le_reflx
  | H1: pfx_bit ?p1 ?i false, H2: pfx_le ?p1 ?p2, H3: pfx_bit ?p2 ?i true |- _ =>
        exfalso; apply (pfx_bit_not_both p2 i); [ apply (pfx_bit_le p1) | ]
  | H1: pfx_le ?p1 ?p2, H2: pfx_le ?p2 ?p3 |- pfx_le ?p1 ?p3 =>
        apply (pfx_le_trans _ p2 _)
  | |- context[pfx_len (pfx_emb _)] => rewrite pfx_emb_len
  | H1: pfx_le ?p1 ?p2, H2: pfx_len ?p2 <= ?n |- pfx_len ?p1 <= ?n =>
         apply pfx_le_len in H1
  | H1: pfx_bit ?p1 ?i true, H2: pfx_le ?p1 ?p2, H3: pfx_bit ?p2 ?i false |- _ =>
        exfalso; apply (pfx_bit_not_both p2 i); [ | apply (pfx_bit_le p1) ]
  | H: word.and (?k ^>> ?n) /[1] = /[1] |- pfx_bit (pfx_emb ?k) \[?n] true =>
       apply pfx_emb_bitop1
  | H: word.and (?k ^>> ?n) /[1] <> /[1] |- pfx_bit (pfx_emb ?k) \[?n] false =>
       apply pfx_emb_bitop0
(*
  | H1: is_prefix (append_0 ?p) ?p1, H2: is_prefix_key ?p1 ?k
          |- is_prefix_key ?p ?k =>
             apply (is_prefix_key_trans _ p1);
             [ | | apply (is_prefix_trans _ (append_0 p)) | ]
  | H1: is_prefix (append_1 ?p) ?p1, H2: is_prefix_key ?p1 ?k
          |- is_prefix_key ?p ?k =>
             apply (is_prefix_key_trans _ p1);
             [ | | apply (is_prefix_trans _ (append_1 p)) | ]
  | H1: is_prefix ?p1 ?p2, H2: is_prefix_key (append_0 ?p2) ?k
          |- is_prefix_key ?p1 ?k =>
             apply (is_prefix_key_trans _ p2)
  | H1: is_prefix ?p1 ?p2, H2: is_prefix_key (append_1 ?p2) ?k
          |- is_prefix_key ?p1 ?k =>
             apply (is_prefix_key_trans _ p2)
  | H1: is_prefix ?p1 ?p2, H2: is_prefix_key ?p2 ?k |- is_prefix_key ?p1 ?k =>
          apply (is_prefix_key_trans p1 p2 k)
  | H: is_prefix (append_0 ?p1) ?p2 |- is_prefix ?p1 ?p2 =>
          apply weaken_is_prefix_append_0; assumption
  | H: is_prefix (append_1 ?p1) ?p2 |- is_prefix ?p1 ?p2 =>
          apply weaken_is_prefix_append_1; assumption
  | H: is_prefix_key (append_0 ?p) ?k |- is_prefix_key ?p ?k =>
          apply weaken_is_prefix_key_append_0; assumption
  | H: is_prefix_key (append_1 ?p) ?k |- is_prefix_key ?p ?k =>
          apply weaken_is_prefix_key_append_1; assumption
  | |- is_prefix ?p (append_0 ?p) => apply is_prefix_append_0
  | |- is_prefix ?p (append_1 ?p) => apply is_prefix_append_1
  | H1: is_prefix_key ?p1 ?k, H2: is_prefix_key ?p2 ?k, H3: length ?p1 <= length ?p2
    |- is_prefix ?p1 ?p2 =>
       apply (prefixes_of_same p1 p2 (full_prefix k))
  | H1: is_prefix (append_0 ?p1) ?p2, H2: is_prefix_key ?p2 ?k,
    H3: word.and (?k ^>> /[length ?p1]) /[1] = /[1] |- _ =>
    enough (is_prefix_key (append_0 p1) k) as Hprex;
    [ apply append_0_prefix in Hprex | apply (is_prefix_key_trans (append_0 p1) p2 k);
      try assumption; try lia; simpl; lia ]
  | H1: is_prefix (append_1 ?p1) ?p2, H2: is_prefix_key ?p2 ?k,
    H3: word.and (?k ^>> /[length ?p1]) /[1] <> /[1] |- _ =>
    enough (is_prefix_key (append_1 p1) k) as Hprex;
    [ apply append_1_prefix in Hprex | apply (is_prefix_key_trans (append_1 p1) p2 k);
      try assumption; try lia; simpl; lia ]
  | H1: is_prefix_key ?pr ?k, H2: word.and (?k ^>> /[length ?pr]) /[1] <> /[1]
    |- is_prefix_key (append_0 ?pr) ?k =>
    apply and_1_not_1_0 in H2; apply is_prefix_key_extend_0
  | H1: is_prefix_key ?pr ?k, H2: word.and (?k ^>> /[length ?pr]) /[1] = /[1]
    |- is_prefix_key (append_1 ?pr) ?k =>
    apply is_prefix_key_extend_1
  | H1: is_prefix_key (append_0 ?pr) ?k, H2: word.and (?k ^>> /[length ?pr]) /[1] = /[1]
    |- _ => apply append_0_prefix in H1; try lia; rewrite H2 in H1; hwlia
  | H1: is_prefix_key (append_1 ?pr) ?k, H2: word.and (?k ^>> /[length ?pr]) /[1] <> /[1]
    |- _ => apply append_1_prefix in H1; try lia; rewrite H1 in H2; contradiction
  | |- context [ length (full_prefix ?k) ] =>
       change (length (full_prefix k)) with 32
  | |- context [ length (append_0 ?p) ] =>
       change (length (append_0 p)) with (length p + 1)
  | |- context [ length (append_1 ?p) ] =>
       change (length (append_1 p)) with (length p + 1)
  | H: word.and ?w /[1] <> /[1] |- word.and ?w /[1] = /[0] =>
       apply and_1_not_1_0; exact H *)
  | |- /[match ?opt1 with | Some _ => ?vs | None => ?vn end] =
       /[match ?opt2 with | Some _ => ?vs | None => ?vn end] =>
     enough (opt1 = None <-> opt2 = None); [ destruct opt1; destruct opt2;
     intuition congruence | ]
  | |- _ => my_simpl_step
  | |- map.split _ _ _ => unfold map.split (*
  | |- is_prefix_key {| length := ?l; bits := prefix_bits ?l ?k |} ?k =>
     apply record_prefix_is_prefix
  | H1: prefix_bits \[?l] ?k = prefix_bits \[?l] ?k',
    H2: word.and (?k ^>> ?l) /[1] = ?b,
    H3: word.and (?k' ^>> ?l) /[1] = ?b
    |- prefix_bits (\[?l] + 1) ?k = prefix_bits (\[?l] + 1) ?k' =>
      apply extend_prefix_bits_eq;
      [ lia | exact H1 | rewrite H2; rewrite H3; reflexivity ] *)
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
  | H: word.and (?k ^>> /[?n]) /[1] <> /[1] |- _ => apply pfx_emb_bitop0 in H
  end.

Ltac apply_key_prefix_hyp :=
  match goal with
  | Hq: context[ map.get ?c _ <> None -> _ ], Hc: map.get ?c _ <> None |- _ =>
    apply Hq in Hc
  end.

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
                                + uintptr p }> p' }>). steps.
  unfold closest_key_in in *. steps.
  destruct (word.eqb retv k) eqn:E; steps.
  destruct (word.eqb retv k) eqn:E; steps. apply eq_None_by_false. intro.
  apply_key_prefix_hyp. raw_bit_to_pfx.
  steps. steps. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pL, cL, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 pR cR aR
                           * <{ + uintptr /[pfx_len pr]
                                + uintptr p
                                + uintptr aR }> p' }>).
  assert (map.get cR k = None). apply eq_None_by_false. intro.
  apply_key_prefix_hyp. steps. raw_bit_to_pfx; steps. steps.
  unfold closest_key_in in *. steps.
  destruct (word.eqb retv k) eqn:E; steps.
  destruct (word.eqb retv k) eqn:E; steps. .**/
  }                                                                          /**.
  simpl cbt' in *. steps. .**/
    if (load(p + 4) == k) /* split */ {                                       /**. .**/
    store(p + 8, v);                                                        /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  unfold closest_key_in. steps; subst. steps. subst. steps. .**/
  else {                                                                    /**. .**/
    return load(p + 4);                                                     /**. .**/
  }                                                                         /**.
  unfold closest_key_in. steps; subst. steps. subst. steps. .**/
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
  subst. steps.
  subst. steps. .**/
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
  subst. steps. subst. steps. cbn. steps. .**/
  else {                                                                    /**. .**/
    uintptr_t found = 0;  /**.
    (* can't process the above command because of the error
       In nested Ltac calls to ".* (constr) *", "next_snippet", "add_snippet",
"add_regular_snippet" and "isnt_local_var", last call failed.*)

    .**/
    found = cbt_lookup_impl(tp, k, val_out);                      /**. .**/
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

(*
Lemma xor_0_l: forall w, word.xor /[-1] w = word.not w.
Proof.
Admitted.
(*
  intros. apply word.unsigned_inj. unfold_bits. apply Z.bits_inj.
  unfold Z.eqf. intros. unfold_bits. destruct (Z.testbit \[w] n);
  destruct xorb eqn:E; unfold xorb in E; fwd; lia.
Qed.
*)

(* TODO: collect *)
Lemma shl_zero : forall w, w ^<< /[0] = w.
Admitted.

(* TODO: collect *)
Lemma not_m1 : word.not /[-1] = /[0].
Admitted.

(* TODO: collect *)
Lemma and_zero_l : forall w, word.and /[0] w = /[0].
Admitted.
*)

#[export] Instance spec_of_critical_bit: fnspec :=                              .**/

uintptr_t critical_bit(uintptr_t k1, uintptr_t k2) /**#
  (* heaplet packaging doesn't work well then there's just one item in the heap *)
  ghost_args := (R1 R2: mem -> Prop);
  requires t m := <{ * R1 * R2 }> m /\ k1 <> k2;
  ensures t' m' res := t = t' /\ <{ * R1 * R2 }> m'
                /\ 0 <= \[res] < 32
                /\ \[res] = pfx_len (pfx_meet (pfx_emb k1) (pfx_emb k2)) (*
                /\ prefix_bits \[res] k1 = prefix_bits \[res] k2
                /\ prefix_bits (\[res] + 1) k1 <> prefix_bits (\[res] + 1) k2*) #**/  /**.
Derive critical_bit SuchThat (fun_correct! critical_bit) As critical_bit_ok.    .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.
  prove (0 <= \[i] < 32).
  prove (forall n, 0 <= n < \[i] ->
           exists b, pfx_bit (pfx_emb k1) n b /\ pfx_bit (pfx_emb k2) n b).
  (*prove (word.and (word.not (/[-1] ^<< i)) k1 = word.and (word.not (/[-1] ^<< i)) k2).
  subst i.
  (* TODO: collect *)
  match goal with
  | |- context[_ ^<< /[0]] => rewrite shl_zero
  end.
  (* TODO: collect *)
  match goal with
  | |- context[word.not /[-1]] => rewrite not_m1
  end.
  (* TODO: collect *)
  repeat match goal with
  | |- context[word.and /[0] _] => rewrite and_zero_l
  end.
  steps.
  *)
  (*
  replace (word.not (/[-1] ^<< /[0])) with /[0]. apply word.unsigned_inj.
  unfold_bits. repeat rewrite Z.land_0_r. reflexivity. apply word.unsigned_inj.
  unfold_bits. simpl. reflexivity.*)
  delete #(i = /[0]).
  loop invariant above H.
  move i at bottom. .**/
  while (i < 31 && ((k1 >> i & 1) == ((k2 >> i & 1))))
    /* decreases (32 - \[i]) */ { (*
  while (i < 31 && ((-1 ^ (-1 << (i + 1))) & k1) == ((-1 ^ (-1 << (i + 1))) & k2))
    /* decreases (32 - \[i]) */ {   *)                                     /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /*?.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step.
  assert (Hcmp: n = \[i'] \/ n < \[i']) by hwlia. destruct Hcmp.
  assert (Hmone: word.and (k1 ^>> i') /[1] = /[1] \/ word.and (k1 ^>> i') /[1] <> /[1])
  by hwlia. destruct Hmone. exists true. steps. subst. steps. subst. steps.
  assert (word.and (k2 ^>> i') /[1] = /[1]) by congruence. subst.
  match goal with
  | H: word.and (?k ^>> ?n) /[1] = /[1] |- pfx_bit (pfx_emb ?k) \[?n] true =>
       apply pfx_emb_bitop1
  end. steps. subst. steps.
  exists false. steps. subst. steps. subst. steps.
  assert (word.and (k2 ^>> i') /[1] <> /[1]) by congruence. subst. steps
  match goal with
  | H: forall _, _ |- _ => apply H
  end.
  steps. steps. steps. (*
  mat
  rewrite word.of_Z_unsigned.
  match goal with
  |
  match goal with
  | H: word.and _ _ = word
  subst i. replace (word.opp /[1]) with (/[-1]) in * by hwlia.
  rewrite xor_0_l in H5. assumption. hwlia.*) .**/
  return i;                                                                /**. .**/
}                                                                          /**.
  symmetry. apply pfx_cb_charac. steps.
  assert (Hmone: word.and (k1 ^>> i) /[1] = /[1] \/ word.and (k1 ^>> i) /[1] <> /[1])
    by hwlia.
  destruct Hmone. exists true. exists false. steps.
  (* TODO: think about the prefix interface more carefully? *)
  unfold prefix_bits. assert (Hi: \[i] =? 32 = false). lia. rewrite Hi.
  replace /[\[i]] with i. assumption. hwlia.
  unfold prefix_bits. destruct (\[i] + 1 =? 32) eqn:E. assumption.
  destruct H. exfalso. hwlia. replace (word.opp /[1]) with (/[-1]) in H.
  rewrite xor_0_l in H. replace (/[\[i] + 1]) with (i ^+ /[1]).
  assumption. hwlia. hwlia.
Qed.

#[export] Instance spec_of_cbt_insert_at: fnspec :=                             .**/

uintptr_t cbt_insert_at(uintptr_t tp, uintptr_t cb, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (total_pr: prefix) (pr: prefix) (c: word_map)
                (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' sk pr c tp
                     * R }> m
                  /\ 0 <= length total_pr
                  /\ is_prefix total_pr pr /\ is_prefix_key total_pr k
                  /\ 0 <= \[cb] < 32
                  /\ exists k',
                       (map.get c k' <> None
                         /\ prefix_bits \[cb] k' = prefix_bits \[cb] k)
                  /\ forall k',
                       (map.get c k' <> None ->
                         prefix_bits (\[cb] + 1) k' <> prefix_bits (\[cb] + 1) k);
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
                            (EX sk' pr',
                              <{ * allocator
                                 * emp (is_prefix total_pr pr')
                                 * cbt' sk' pr' (map.put c k v) tp
                                 * R }>) m' #**/ /**.
Derive cbt_insert_at SuchThat (fun_correct! cbt_insert_at) As cbt_insert_at_ok.  .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  assert (Htpnn: tp <> /[0]). apply purify_cbt' in H2. tauto.
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
    /* initial_ghosts(p, pr, total_pr, c, R); decreases sk */
  {                                                                        /*?.
  subst v0.
  repeat heapletwise_step.
  apply cbt_expose_fields in H13. steps.
  destruct sk; [ exfalso | ]. steps.
  .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                            /**. .**/
      p = load(p + 8);                                                      /**. .**/
    }                                                                       /**.
  new_ghosts(p, pR, append_1 pr, cR, <{ * R
                                        * freeable 12 p'
                                        * cbt' sk1 pL cL w2
                                        * <{ + uintptr /[length pr]
                                             + uintptr w2
                                             + uintptr p }> p' }>).
  instantiate (1:=sk2). step. step. steps.
  enough (is_prefix_key pr k).
  steps.
  enough (is_prefix_key pr k') as Hprk'.
  unfold is_prefix_key. unfold is_prefix. unfold full_prefix.
  unfold is_prefix_key in Hprk'. unfold is_prefix in Hprk'. unfold full_prefix in Hprk'.
  cbn in Hprk'. fwd. step. step. step. rewrite Hprk'p1.
  eapply clip_prefix_bits_equality with (n2:=\[cb]). step. step. step.
  destruct_in_putmany; apply_key_prefix_hyp; steps. steps.
  destruct_in_putmany; [ exfalso | ]. apply_key_prefix_hyp.
  assert (Hprk': is_prefix_key (append_0 pr) k'). steps.
  assert (is_prefix_key (append_0 pr) k).
  unfold is_prefix_key. unfold is_prefix. unfold full_prefix.
  unfold is_prefix_key in Hprk'. unfold is_prefix in Hprk'. unfold full_prefix in Hprk'.
  cbn in Hprk'. cbn. fwd. step. step. rewrite Hprk'p1.
  eapply clip_prefix_bits_equality with (n2:=\[cb]). steps. steps. steps.
  steps. steps. steps.
  match goal with
  | H: context[(_ <> None) -> (prefix_bits (\[cb] + 1) _ <> _)] |- _ => apply H
  end.
  steps. step. steps. unfold state_implication. steps.
  match goal with
  | H: context[expect_1expr_return] |- _ => destruct H
  end.
  steps.
  econstructor. eassumption.
  step. step. steps. step. simpl cbt'. step. steps. step. step.
  repeat heapletwise_step. step. step. steps. step. step.
  instantiate (1:=pr). instantiate (1:=Node sk1 sk'). simpl cbt'.
  steps. apply eq_None_by_false. intro. apply_key_prefix_hyp.
  steps. .**/
    else {                                                                    /**. .**/
      p = load(p + 4);                                                        /**. .**/
    }                                                                         /**.
  new_ghosts (p, pL, append_0 pr, cL,
      <{ * R
         * freeable 12 p'
         * <{ + uintptr /[length pr]
              + uintptr p
              + uintptr w3 }> p'
         * cbt' sk2 pR cR w3 }>).
  instantiate (1:=sk1). step. step. steps.
  enough (is_prefix_key pr k). steps.
  enough (is_prefix_key pr k') as Hprk'.
  unfold is_prefix_key. unfold is_prefix. unfold full_prefix.
  unfold is_prefix_key in Hprk'. unfold is_prefix in Hprk'. unfold full_prefix in Hprk'.
  cbn in Hprk'. fwd. step. step. step. rewrite Hprk'p1.
  eapply clip_prefix_bits_equality with (n2:=\[cb]). step. step. step.
  destruct_in_putmany; apply_key_prefix_hyp; steps. steps.
  destruct_in_putmany; cycle 1; [ exfalso | ]. apply_key_prefix_hyp.
  assert (Hprk': is_prefix_key (append_1 pr) k'). steps.
  assert (is_prefix_key (append_1 pr) k).
  unfold is_prefix_key. unfold is_prefix. unfold full_prefix.
  unfold is_prefix_key in Hprk'. unfold is_prefix in Hprk'. unfold full_prefix in Hprk'.
  cbn in Hprk'. cbn. fwd. step. step. rewrite Hprk'p1.
  eapply clip_prefix_bits_equality with (n2:=\[cb]). steps. steps. steps.
  steps. steps. steps.
  match goal with
  | H: context[(_ <> None) -> (prefix_bits (\[cb] + 1) _ <> _)] |- _ => apply H
  end.
  steps. step. steps. unfold state_implication. steps.
  match goal with
  | H: context[expect_1expr_return] |- _ => destruct H
  end.
  steps.
  econstructor. eassumption.
  step. step. steps. step. simpl cbt'. step. steps. step. step.
  repeat heapletwise_step. step. step. steps. step. step.
  instantiate (1:=pr). instantiate (1:=Node sk' sk2). simpl cbt'.
  steps. steps. apply eq_None_by_false. intro. apply_key_prefix_hyp.
  steps. apply eq_None_by_false. intro. apply_key_prefix_hyp.
  steps. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == 0) /* split */ {                                           /**. .**/
    return 0;                                                                /**.
  change (0 =? 0) with true in H1. cbv iota in H1. .**/
  }                                                                          /*?.
  step. step. steps. step. step. step. destruct sk; simpl cbt' in *; steps.
  steps. .**/
  else {                                                                     /**. .**/
    uintptr_t new_node = Malloc(12);                                         /**. .**/
    if (new_node == 0) /* split */ {                                         /**.
  change (0 =? 0) with true in *. cbv iota in *. .**/
      return 0;                                                              /**. .**/
    }                                                                        /*?.
  step. step. step. steps. step. destruct sk; simpl cbt' in *; steps. steps. .**/
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
  step. step. step. step. step. steps. step. step. step. step.
  instantiate (2:=Node sk Leaf). simpl cbt'.
  instantiate (1:={|length:=\[cb]; bits:=prefix_bits \[cb] k|}). step.
  enough (length total_pr <= \[cb]).
  unfold is_prefix. step. step. step. rewrite clip_prefix_bits.
  match goal with
  | H: is_prefix_key total_pr k |- _ =>
    unfold is_prefix_key, is_prefix in H; simpl in H
  end. step. assumption. lia. lia.
  assert (length total_pr <= 32).
  match goal with
  | H: is_prefix_key total_pr k |- _ =>
    unfold is_prefix_key, full_prefix, is_prefix in H; simpl in H
  end. lia.
  assert (Hcmp: length total_pr <= \[cb] \/ \[cb] + 1 <= length total_pr). lia.
  destruct Hcmp; [ assumption | exfalso ].
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => apply H with k'
  end. step.
  apply clip_prefix_bits_equality with (length total_pr). lia. lia.
  apply same_prefix_bits_equality. 2: assumption.
  enough (is_prefix_key pr k'). steps.
  apply_key_prefix_hyp. step.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. instantiate (2:=c). instantiate (3:=pr).
  repeat clear_array_0.
  simpl cbt' in *. instantiate (2:=full_prefix k). instantiate (1:=map.singleton k v).
  destruct sk; simpl cbt'; steps; cbn; steps. subst. steps.
  unfold is_canonic. unfold canonic_bits. cbn. rewrite clip_prefix_bits; steps.
  subst. assert (w2 = k'). steps. subst.
  match goal with
  | H: prefix_bits \[cb] k' = prefix_bits \[cb] k0 |- _ => rewrite <- H
  end.
  apply is_prefix_key_extend_0; steps.
  assert (prefix_bits (\[cb] + 1) k' <> prefix_bits (\[cb] + 1) k0).
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => apply H
  end.
  steps.
  assert (word.and (k' ^>> cb) /[1] <> /[1]). intro.
  match goal with
  | H: prefix_bits (\[cb] + 1) k' <> prefix_bits _ _ |- _ => apply H
  end.
  change (\[cb] + 1)
    with (length (append_1 {| length := \[cb]; bits := k0 |})).
  eapply same_prefix_bits_equality. apply is_prefix_key_extend_1. step.
  unfold is_prefix_key, full_prefix, is_prefix. cbn. steps. steps.
  apply is_prefix_key_extend_1; steps.
  (* TODO: automate *)
  unfold is_prefix_key, full_prefix, is_prefix;
  cbn; steps. steps. apply is_prefix_key_extend_1; steps.
  (* TODO: automate *)
  rewrite map_putmany_singleton_r. steps.
  apply map_disjoint_singleton_r. apply eq_None_by_false. intro.
  apply_key_prefix_hyp. subst. step. step. assert (w2 = k0). steps.
  match goal with
  | H: is_prefix_key (full_prefix _) _ |- _ =>
    unfold is_prefix_key, is_prefix, full_prefix in H; cbn in H
  end. steps. subst. step.
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => specialize (H k0); apply H
  end.
  steps. steps. subst. steps.
  (* TODO automate *)
  match goal with
  | |- is_canonic {| length := ?l; bits := prefix_bits ?l ?k |} =>
    unfold is_canonic, canonic_bits; cbn; rewrite clip_prefix_bits; try lia
  end.
  steps. subst. step.
  assert (Hcbp1: prefix_bits (\[cb] + 1) k' <> prefix_bits (\[cb] + 1) k0).
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => apply H
  end.
  steps.
  apply_key_prefix_hyp.
  assert (Hcmp: \[cb] = length pr \/ \[cb] < length pr). step.
  destruct Hcmp.
  exfalso.
  match goal with
  | H: _ |= cbt' _ pR _ _ |- _ => apply cbt_nonempty in H
  end.
  steps.
  match goal with
  | H1: context[_ -> prefix_bits (\[cb] + 1) _ <> _],
    H2: map.get cR ?k <> None
    |- _ => apply H1 with k
  end.
  step.
  assert (word.and (k ^>> cb) /[1] = /[1]). replace cb with /[length pr] by hwlia.
  apply_key_prefix_hyp.
  assert (Hprk: is_prefix_key (append_1 pr) k). steps.
  apply append_1_prefix in Hprk. steps. steps.
  assert (prefix_bits \[cb] k = prefix_bits \[cb] k0).
  assert (is_prefix_key pr k). apply_key_prefix_hyp. steps.
  assert (prefix_bits (length pr) k = prefix_bits (length pr) k').
  apply same_prefix_bits_equality; steps. congruence. steps.
  edestruct is_prefix_extend_0_or_1; [ | | |  eassumption | ]; cbn; steps.
  assert (prefix_bits (length pr) (bits pr) = prefix_bits (length pr) k').
  match goal with
  | H: is_prefix_key pr k' |- _ => unfold is_prefix_key, is_prefix, full_prefix in H
  end.
  step. step.
  match goal with
  | H: (prefix_bits (length pr) _ = prefix_bits (length pr) _) |- _ =>
    apply clip_prefix_bits_equality with (n1:=\[cb]) in H
  end.
  replace (prefix_bits \[cb] k0) with (prefix_bits \[cb] (bits pr)) by congruence.
  unfold is_prefix. cbn. step. step. apply clip_prefix_bits. steps. steps.
  steps. steps.
  exfalso.
  assert (Hprfk': is_prefix_key (append_1 {| length := \[cb]; bits := prefix_bits \[cb] k0 |}) k'). steps. cbn. steps.
  apply append_1_prefix in Hprfk'. cbn in Hprfk'.
  (* TODO: automate *)
  match goal with
  | H: context[ /[\[ _ ]] ] |- _ => rewrite word.of_Z_unsigned in H
  end.
  apply Hcbp1. steps. cbn. steps. steps. apply is_prefix_key_extend_1; cbn; steps.
  (* TODO: automate *)
  rewrite map_putmany_singleton_r. steps.
  apply map_disjoint_singleton_r. apply eq_None_by_false. intro.
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => apply H with k
  end; steps. .**/

      else {                                                                  /**. .**/
        store(p + 4, new_leaf);                                               /**. .**/
        store(p + 8, new_node);                                               /**. .**/
        return tp;                                                            /**. .**/
      }                                                                       /*?.
  step. step. step. step. step. step. step. step. instantiate (2:=Node Leaf sk).
  simpl cbt'. instantiate (1:={|length:=\[cb]; bits:=prefix_bits \[cb] k|}).
  steps. 2: instantiate (8:=k). 2: instantiate (7:=v).
  2: instantiate (4:=full_prefix k). 2: instantiate (1:=c).
  2: instantiate (1:=map.singleton k v). 2: instantiate (1:=pr).
  enough (length total_pr <= \[cb]).
  unfold is_prefix. step. step. step. rewrite clip_prefix_bits.
  match goal with
  | H: is_prefix_key total_pr k |- _ =>
    unfold is_prefix_key, is_prefix in H; simpl in H
  end. step. assumption. lia. lia.
  assert (length total_pr <= 32).
  match goal with
  | H: is_prefix_key total_pr k |- _ =>
    unfold is_prefix_key, full_prefix, is_prefix in H; simpl in H
  end. lia.
  assert (Hcmp: length total_pr <= \[cb] \/ \[cb] + 1 <= length total_pr). lia.
  destruct Hcmp; [ assumption | exfalso ].
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> _] |- _ => apply H with k'
  end. step.
  apply clip_prefix_bits_equality with (length total_pr). lia. lia.
  apply same_prefix_bits_equality. 2: assumption.
  enough (is_prefix_key pr k'). steps.
  apply_key_prefix_hyp. step. simpl cbt' in *. simpl length.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step.
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H; idtac H
  end. subst. step. step.
  step. step. step. step. step. step. step.
  step. step. step. step. step. step.
  step. unfold canceling. unfold seps. step. step.
  2: apply I.
  step. step. apply sep_comm.
  step. step. step. step.

  unfold is_canonic. unfold canonic_bits. cbn. rewrite clip_prefix_bits; steps.
  simpl length in *.
  step. apply is_prefix_key_extend_0; steps; cbn; steps.
  assert (Hprn1:
     ~is_prefix (append_0 {| length := \[cb]; bits := prefix_bits \[cb] k0 |}) pr).
  intro Hprpr. assert (map.get c k' <> None) by assumption. apply_key_prefix_hyp.
  eapply is_prefix_key_trans in Hprpr; [ | cbn; steps | steps | eassumption ].
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> prefix_bits (\[cb] + 1) _]
       |- _ => apply H with k'
  end. steps. apply append_0_prefix in Hprpr. cbn in Hprpr.
  match goal with
  | H: context[/[\[ _ ]]] |- _ => rewrite word.of_Z_unsigned in H
  end.
  assert (word.and (k0 ^>> cb) /[1] = /[0]) by steps. steps. cbn. steps.
  assert (\[cb] < length pr).
  assert (\[cb] <= length pr). destruct sk; steps; subst; steps.
  assert (Hcmp: \[cb] < length pr \/ \[cb] = length pr) by lia.
  destruct Hcmp; [ assumption | exfalso ].
  { destruct sk; steps; subst.
  - simpl length in *. steps.
  - match goal with
    | H: _ |= cbt' _ pL _ _ |- _ => apply cbt_nonempty in H
    end. steps.
    match goal with
    | H: context[_ -> prefix_bits (\[cb] + 1) _ <> prefix_bits (\[cb] + 1) _]
         |- _ => apply H with k
    end. steps. repeat apply_key_prefix_hyp.
    assert (word.and (k0 ^>> cb) /[1] = /[0]). steps.
    assert (word.and (k ^>> cb) /[1] = /[0]).
    assert (Hprk: is_prefix_key (append_0 pr) k) by steps.
    apply append_0_prefix in Hprk. replace /[length pr] with cb in Hprk; steps. steps.
    assert (prefix_bits \[cb] k = prefix_bits \[cb] k0).
    assert (Hprk': is_prefix_key pr k) by steps.
    eapply same_prefix_bits_equality with (k1:=k') in Hprk'. 2: assumption.
    replace (length pr) with \[cb] in Hprk' by steps. congruence. steps. }
  assert (is_prefix {| length := \[cb]; bits := prefix_bits \[cb] k0 |} pr).
  apply_key_prefix_hyp.
  match goal with
  | H: is_prefix_key pr k' |- _ =>
       unfold is_prefix_key, is_prefix, full_prefix in H; cbn in H
  end. steps.
  match goal with
  | H: prefix_bits (length pr) _ = prefix_bits (length pr) _ |- _ =>
       apply clip_prefix_bits_equality with (n1:=\[cb]) in H
  end.
  unfold is_prefix. cbn. step. step. rewrite clip_prefix_bits. congruence.
  steps. steps. steps. steps.
  step. edestruct is_prefix_extend_0_or_1; [ | | | exfalso | eassumption ]; cbn; steps.
  step.
  assert (map.get c k0 = None). { apply eq_None_by_false. intro Hprk0.
  apply_key_prefix_hyp. apply same_prefix_bits_equality with (k1:=k') in Hprk0.
  match goal with
  | H: context[_ -> prefix_bits (\[cb] + 1) _ <> prefix_bits (\[cb] + 1) _]
       |- _ => apply H with k'
  end; steps. eapply clip_prefix_bits_equality; [ | | eassumption ]; steps.
  apply_key_prefix_hyp. steps. }
  steps. symmetry. apply map_putmany_singleton_l. steps.
  apply map_disjoint_singleton_l. steps.
  step. destruct sk; simpl cbt'; repeat clear_array_0; steps;
  unfold canceling, seps, emp; steps. .**/
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
  subst. steps. simpl (0 =? 0) in *. steps. subst. unfold map.singleton. steps.
  simpl (0 =? 0) in *. cbv iota in *. steps. .**/
  else {                                                                   /**. .**/
  uintptr_t best_k = cbt_update_or_best(tp, k, v);                         /**. .**/
    if (best_k == k) /* split */ {                                         /**.
  subst best_k.
  match goal with
  | H: _ \/ _ |- _ => destruct H; [ | tauto ]
  end. step. unzify. .**/
      return tp;                                                           /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**.
  match goal with
  | H: _ \/ _ |- _ => destruct H; [ tauto | ]
  end. steps. .**/
      uintptr_t cb = critical_bit(k, best_k);                              /**.
  instantiate (3:=emp True). steps.
  unfold enable_frame_trick.enable_frame_trick. steps.
  instantiate (2:=<{ * allocator * R }>). unfold canceling. steps. simpl. steps. .**/
      uintptr_t result = cbt_insert_at(tp, cb, k, v);                      /**.
  instantiate (1:=empty_prefix). unfold empty_prefix. cbn. step.
  apply empty_is_prefix. step. apply empty_is_prefix. cbn. step.
  instantiate (1:=best_k). unfold closest_key_in in *. steps. symmetry.
  steps. unfold closest_key_in in *. steps.
  intro Hprkk'.
  match goal with
  | H: prefix_bits _ _ <> prefix_bits _ _ |- _ => apply H
  end.
  assert (Hprkb: is_prefix_key {| length := \[cb] + 1; bits := prefix_bits (\[cb] + 1) k' |} best_k).
  match goal with
  | H: context[map.get c _ <> None -> (is_prefix_key _ _ -> _ )] |- _ => eapply H
  end.
  2: eassumption. cbn. steps. steps. rewrite Hprkk'. steps.
  unfold is_prefix_key, is_prefix, full_prefix in Hprkb. cbn in Hprkb.
  rewrite clip_prefix_bits in Hprkb. steps. steps. steps.

  unfold enable_frame_trick.enable_frame_trick. steps. .**/
      return result;                                                       /**. .**/
    }                                                                      /**.
  replace (\[result] =? 0) with false by steps.
  match goal with
  | H: (_ \/ _) |- _ => destruct H; [steps; tauto | ]
  end.
  fwd. unfold id in *. subst. steps. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
