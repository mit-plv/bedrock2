(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

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

Context {consts: malloc_constants}.

Fixpoint bst'(sk: tree_skeleton)(s: set Z)(addr: word){struct sk}: mem -> Prop :=
  match sk with
  | Leaf => emp (addr = /[0] /\ forall x, ~ s x)
  | Node skL skR => ex1 (fun p: word => (ex1 (fun v: Z => (ex1 (fun q: word =>
      <{ * emp (addr <> /[0])
         * emp (s v)
         * freeable 12 addr
         * <{ + uintptr p
              + uint 32 v
              + uintptr q }> addr
         * bst' skL (fun x => s x /\ x < v) p
         * bst' skR (fun x => s x /\ v < x) q }>)))))
  end.

Definition bst(s: set Z)(addr: word): mem -> Prop :=
  ex1 (fun sk: tree_skeleton => bst' sk s addr).

Local Hint Extern 1 (PredicateSize (bst' ?sk)) =>
  let r := eval cbv iota in
    (match sk with
     | Node _ _ => 12
     | Leaf => 0
     end) in
  exact r
: typeclass_instances.

#[local] Hint Extern 1 (cannot_purify (bst' _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (bst _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.

#[local] Hint Unfold bst : heapletwise_always_unfold.

Lemma invert_bst'_null: forall sk s m,
    m |= bst' sk s /[0] ->
    m |= emp (forall x, ~ s x).
Proof.
  unfold with_mem. intros. destruct sk; simpl in *.
  - unfold emp in *. intuition auto.
  - repeat heapletwise_step. exfalso. apply H0. reflexivity.
Qed.

Lemma invert_bst'_nonnull: forall sk s p m,
    p <> /[0] ->
    m |= bst' sk s p ->
    exists skL skR pL v pR,
      sk = Node skL skR /\
      s v /\
      <{ * freeable 12 p
         * <{ + uintptr pL
              + uint 32 v
              + uintptr pR }> p
         * bst' skL (fun x => s x /\ x < v) pL
         * bst' skR (fun x => s x /\ v < x) pR }> m.
Proof.
  intros.
  destruct sk; simpl in *|-.
  { exfalso. unfold with_mem, emp in *. intuition idtac. }
  repeat heapletwise_step.
  do 5 eexists. split. 1: reflexivity.
  split. 1: eassumption.
  repeat heapletwise_step.
Qed.

  (* TODO use and move or delete *)
  Lemma after_if_skip' b fs (PThen PElse Post: trace -> mem -> locals -> Prop):
    bool_expr_branches b (forall t m l, PThen t m l -> Post t m l)
                         (forall t m l, PElse t m l -> Post t m l) True ->
    @after_if _ _ _ _ _ _ fs b PThen PElse cmd.skip Post.
  Proof.
    intros.
    unfold after_if.
    intros ? ? ? [? ? ?]. subst x.
    eapply wp_skip.
    apply proj1 in H.
    destruct b; eauto.
  Qed.

Ltac step_hook ::=
  match goal with
  | |- _ => progress cbn [bst']
  | sk: tree_skeleton |- _ => progress subst sk
  end.

(* TODO move *)
Local Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (PredicateSize_not_found (freeable _))
      => constructor : suppressed_warnings.

#[export] Instance spec_of_bst_contains: fnspec :=                              .**/

uintptr_t bst_contains(uintptr_t p, uintptr_t v) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * bst s p
                     * R }> m;
  ensures t' m' b := t' = t /\
                     (\[b] = 1 /\ s \[v] \/ \[b] = 0 /\ ~ s \[v]) /\
                     <{ * bst s p
                        * R }> m' #**/                                     /**.
Derive bst_contains SuchThat (fun_correct! bst_contains) As bst_contains_ok.    .**/
{                                                                          /**.
  change (bst' sk s p m0) with (m0 |= bst' sk s p) in *.
  (* TODO ex1 destruct should leave |= intact *)                                .**/
  uintptr_t res = 0;                                                       /**. .**/
  uintptr_t a = p;                                                         /**.

  unfold ready.

  let cond := constr:(live_expr:(!res && a != 0)) in
  let measure0 := constr:(sk) in
  eapply (wp_while_tailrec_with_done_flag measure0 (s, a, R) cond)
         with (pre := fun sk (g: (set Z * word * (mem -> Prop))) ti mi li =>
                        let '(s, a, F) := g in
                        exists res, res = /[0] /\
                        li = map.of_list [|("a", a); ("p", p); ("res", res); ("v", v)|] /\
                        ti = t /\
                        <{ * bst' sk s a * F }> mi).
  1: eauto with wf_of_type.
  1: solve [steps].
  {
    intros. fwd. subst t0 l.
    steps.
    { (* loop condition false implies post (which could be constructed here from
         the context, hopefully) *)
      instantiate (1 := fun sk (g: (set Z * word * (mem -> Prop))) ti mi li =>
                        let '(s, olda, F) := g in
                        exists a res,
                        li = map.of_list [|("a", a); ("p", p); ("res", res); ("v", v)|] /\
                        <{ * bst' sk s olda * F }> mi /\
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        ti = t).
      cbv beta iota.
      destruct H. 1: contradiction.
      { steps.
        subst r.
        let H := constr:(#bst') in eapply invert_bst'_null in H.
        steps.
        right. bottom_up_simpl_in_goal. eauto. }
    }
    (* loop body: *)
    let H := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as H.
    clear H0 H1 D. rename v0 into sk0, r into a, res0 into res.
    let H := constr:(#(bst')) in eapply invert_bst'_nonnull in H.
    2: assumption.
    fwd. repeat heapletwise_step.
                                                                                .**/
    uintptr_t here = load32(a+4);                                          /**. .**/
    if (v < here) /* split */ {                                            /**. .**/
      a = load(a);                                                         /**. .**/
    }                                                                      /**.
      all: steps.

      destruct H; try (exfalso; congruence); [].
      subst a.
      (* left subtree empty, so nothing will be found there, so leaving res at 0 was ok *)
      eapply invert_bst'_null in H1.
      steps.
      specialize (H1 \[v]). solve [intuition idtac].
                                                                                .**/
    else {                                                                 /**. .**/
      if (here < v) /* split */ {                                          /**. .**/
        a = load(a+8);                                                     /**. .**/
      }                                                                    /**.
        (* goal ordering problem/evars *)
        { step. }
        { step. }
        { subst res.
          right.
          destruct H. 1: exfalso; congruence. subst a.
          (* subtree empty, so nothing will be found there, so leaving res at 0 was ok *)
          eapply invert_bst'_null in H5.
          steps.
          specialize (H5 \[v]). solve [intuition idtac]. }
                                                                                .**/
      else {                                                               /**. .**/
        res = 1;                                                           /**. .**/
      }                                                                    /**.

        { step. }
        { left. replace \[v] with v0 by steps. steps. }
                                                                                .**/
    }                                                                      /**. .**/
  }                                                                        /**.
  }
  (* after loop *)
  steps.
  fwd.
  clear res Def0. rename res0 into res. subst l.
                                                                                .**/
  return res;                                                              /**. .**/
}                                                                          /**.
Qed.

(* note: inability to break out of loop is cumbersome, because it complicates pre:
   it has to incorporate almost all of post for the res=true case,
   and even if we break, we still have to decrease the termination measure *)

End LiveVerif. Comments .**/ //.
