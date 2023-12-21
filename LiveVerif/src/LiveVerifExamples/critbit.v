(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Require Coq.Bool.Bool.

Load LiveVerif.

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
  intros. unfold pfx_len. lia.
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

Definition bit_at (w: word) (i: Z) := Z.testbit \[w] i.

Lemma bit_at_raw : forall w i, 0 <= i < 32 -> bit_at w i = word.eqb (word.and (w ^>> /[i]) /[1]) /[1].
Admitted.

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

Lemma and_1_not_1_0 : forall w,
  word.and w /[1] <> /[1] -> word.and w /[1] = /[0].
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
Proof.
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
Admitted.

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
  | |- context[ Bool.eqb false false ] => simpl Bool.eqb
  | |- context[ Bool.eqb true false ] => simpl Bool.eqb
  | |- context[ Bool.eqb false true ] => simpl Bool.eqb
  | |- context[ Bool.eqb true true ] => simpl Bool.eqb
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
  (*  unfold impl1. intro m. intros. destruct tree; simpl cbt' in *; steps.
  subst c. steps. *)
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

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Lemma eq_None_by_false {X : Type}: forall o: option X, ~(o <> None) -> o = None.
Proof.
  intros. destruct o. exfalso. apply H. congruence. congruence.
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
  (* instantiate (3:=(match tree with | Leaf _ _ => ?[vLeaf] | _ => ?[vNode] end)). *)
  repeat heapletwise_step.
  match goal with
  | H: _ |= cbt' _ _ _ |- _ => apply cbt_expose_fields in H
  end.
  steps. destruct tree. { exfalso. steps. subst. steps. }
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
  instantiate (1:=tree2). steps. simpl. raw_bit_to_bit_at. steps. steps.

  clear Error.
  raw_bit_to_pfx; [ | steps ].
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
  instantiate (1:=tree1). steps. simpl. raw_bit_to_bit_at. steps. steps.

  clear Error.
  raw_bit_to_pfx; [ | steps ].
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
    if (load(p + 4) == k) /* split */ {                                       /**. .**/
    store(p + 8, v);                                                        /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  subst. simpl. apply map_some_key_singleton. clear Error. simpl cbt'. steps.
  subst. steps. .**/
  else {                                                                    /**. .**/
    return load(p + 4);                                                     /**. .**/
  }                                                                         /**.
  simpl. subst. apply map_some_key_singleton. clear Error. simpl cbt'. steps. .**/
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
  destruct sk. { exfalso. steps. subst. steps. }
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
  steps. raw_bit_to_bit_at. steps. steps.
  clear Error. simpl cbt'. steps. raw_bit_to_bit_at. steps. steps. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, half_subcontent c false, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 (half_subcontent c true) aR
                           * <{ + uintptr /[pfx_len (pfx_mmeet c)]
                                + uintptr p
                                + uintptr aR }> p' }>).
  steps. raw_bit_to_bit_at. steps. steps.
  clear Error. simpl cbt'. steps. raw_bit_to_bit_at. steps. steps. .**/
    }                                                                          /**.
  destruct sk; cycle 1. { exfalso. steps. } simpl cbt' in *. .**/
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
                        * cbt' Leaf (map.singleton k v) res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_alloc_leaf SuchThat (fun_correct! cbt_alloc_leaf) As cbt_alloc_leaf_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = Malloc(12);                                                /**. .**/
  if (p == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    store(p, 32);                                                          /**. .**/
    store(p + 4, k);                                                       /**. .**/
    store(p + 8, v);                                                       /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /*?.
  repeat clear_array_0. simpl cbt'. steps. .**/
}                                                                          /**.
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
  { subst. rewrite bit_at_raw. rewrite bit_at_raw. steps. steps. steps. }
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
  rewrite bit_at_raw by steps. rewrite bit_at_raw by steps. steps. intro.
  match goal with
  | H: word.and _  _ <> _ |- _ => apply H
  end.
  match goal with
  | H: word.eqb _ _ = ?rhs |- _ => destruct rhs eqn:E
  end.
  steps. steps.
  do 2 match goal with | H: _ <> /[1] |- _ => apply and_1_not_1_0 in H end.
  congruence. }
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
  steps. destruct sk. { exfalso. steps. subst. steps. }
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
      subst k'. apply cbt_best_lookup_in. steps. steps.
      match goal with | H: ?rhs = _ |- _ <= ?rhs => rewrite H end.
      match goal with (* where does the mod come from in the first place? *)
      | H: pfx_len _ mod _ < _ |- _ => rewrite Zmod_small in H
      end.
      steps.
      pose proof (pfx_len_nneg (pfx_mmeet c)). pose proof (pfx_mmeet_len c). steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *. raw_bit_to_bit_at.
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
  end.
  steps. .**/
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
      subst k'. apply cbt_best_lookup_in. steps. steps.
      match goal with | H: ?rhs = _ |- _ <= ?rhs => rewrite H end.
      match goal with (* where does the mod come from in the first place? *)
      | H: pfx_len _ mod _ < _ |- _ => rewrite Zmod_small in H
      end.
      steps.
      pose proof (pfx_len_nneg (pfx_mmeet c)). pose proof (pfx_mmeet_len c). steps. }
    { steps. } }
  simpl cbt_best_lookup in *. simpl cbt' in *. raw_bit_to_bit_at.
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
  end.
  steps. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == 0) /* split */ {                                           /**. .**/
    return 0;                                                                /**. .**/
  }                                                                          /**.
  clear Error. destruct sk; simpl cbt' in *; steps. subst. steps. .**/
  else {                                                                     /**. .**/
    uintptr_t new_node = Malloc(12);                                         /**. .**/
    if (new_node == 0) /* split */ {                                         /**. .**/
      return 0;                                                              /**. .**/
    }                                                                        /**.
  clear Error. destruct sk; simpl cbt' in *; steps. subst. steps. .**/
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
  match goal with (* where does the mod come from in the first place? *)
  | H: _ <= pfx_len _ mod _ |- _ => rewrite Zmod_small in H
  end.
  2: { pose proof (pfx_len_nneg (pfx_mmeet c)). pose proof (pfx_mmeet_len c). steps. }
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
    destruct sk.
    - simpl (acbt Leaf _) in *. steps. subst. steps.
    - steps. raw_bit_to_bit_at. simpl cbt_best_lookup in *.
      match goal with
      | H: context [ if bit_at ?k ?i then _ else _ ] |- _ =>
        replace (bit_at k i) with true in H by congruence; cbv iota in H
      end.
      eapply pfx_meet_len_same_bit_false.
      instantiate (2:=pfx_emb (cbt_best_lookup _ _ _)).
      eassumption. instantiate (1:=true).
      (* TODO: collect *)
      match goal with
      | H: bit_at ?k ?i = ?b |- pfx_bit (pfx_emb ?k) ?i ?b =>
        rewrite <- H; apply pfx_bit_bit_at_emb
      end. steps.
      replace \[cb] with (pfx_len (pfx_mmeet c)) by congruence.
      eassert (Hbtrue: bit_at _ _ = true); cycle 1. rewrite <- Hbtrue at 2.
      eapply pfx_bit_bit_at_emb. steps. apply half_subcontent_in_bit.
      (* TODO: collect *)
      match goal with
      | |- map.get ?c (cbt_best_lookup _ ?c _) <> None => apply cbt_best_lookup_in
      end.
      steps. steps. }
  replace (half_subcontent (map.put c k v) false) with c. steps.
  unfold split_concl_at, canceling. simpl seps. split; [ | apply I ]. intros.
  apply sep_comm. clear D. (* TODO: investigate why this D appears *)
  simpl cbt' in *. steps. subst. apply half_subcontent_put_excl_key. lia.
  raw_bit_to_bit_at. congruence. steps. unfold split_concl_at.
  destruct sk; simpl cbt' in *; steps. subst. steps. rewrite pfx_mmeet_put.
  steps. eapply acbt_nonempty. eassumption. symmetry.
  apply half_subcontent_put_excl_bulk. lia. simpl negb.
  raw_bit_to_bit_at. congruence. steps.
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
  match goal with (* where does the mod come from in the first place? *)
  | H: _ <= pfx_len _ mod _ |- _ => rewrite Zmod_small in H
  end.
  2: { pose proof (pfx_len_nneg (pfx_mmeet c)). pose proof (pfx_mmeet_len c). steps. }
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
    destruct sk.
    - simpl (acbt Leaf _) in *. steps. subst. steps.
    - steps. raw_bit_to_bit_at. simpl cbt_best_lookup in *.
      match goal with
      | H: context [ if bit_at ?k ?i then _ else _ ] |- _ =>
        replace (bit_at k i) with false in H by congruence; cbv iota in H
      end.
      (* TODO (not really local here) rename to _False *)
      eapply pfx_meet_len_same_bit_false.
      instantiate (2:=pfx_emb (cbt_best_lookup _ _ _)).
      eassumption. instantiate (1:=false).
      (* already COLLECTED *)
      match goal with
      | H: bit_at ?k ?i = ?b |- pfx_bit (pfx_emb ?k) ?i ?b =>
        rewrite <- H; apply pfx_bit_bit_at_emb
      end. steps.
      replace \[cb] with (pfx_len (pfx_mmeet c)) by congruence.
      eassert (Hbfalse: bit_at _ _ = false); cycle 1. rewrite <- Hbfalse at 2.
      eapply pfx_bit_bit_at_emb. steps. apply half_subcontent_in_bit.
      (* already COLLECTED *)
      match goal with
      | |- map.get ?c (cbt_best_lookup _ ?c _) <> None => apply cbt_best_lookup_in
      end.
      steps. steps. }
  replace (half_subcontent (map.put c k v) true) with c. simpl cbt' in *. steps.
  subst. apply half_subcontent_put_excl_key. lia. raw_bit_to_bit_at. congruence.
  steps. unfold split_concl_at. destruct sk; simpl cbt' in *; steps. subst. steps.
  rewrite pfx_mmeet_put. steps. eapply acbt_nonempty. eassumption. symmetry.
  apply half_subcontent_put_excl_bulk. lia. simpl negb. raw_bit_to_bit_at.
  congruence. steps. .**/
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
