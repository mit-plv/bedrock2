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

Lemma invert_bst'_null{sk s p m}:
    p = /[0] ->
    m |= bst' sk s p ->
    sk = Leaf /\
    m |= emp (forall x, ~ s x).
Proof.
  unfold with_mem. intros. subst. destruct sk; simpl in *.
  - unfold emp in *. intuition auto.
  - repeat heapletwise_step. exfalso. apply H1. reflexivity.
Qed.

Lemma invert_bst'_nonnull{sk s p m}:
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
  | H: _ |= bst' _ _ ?p, E: ?p = /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_null E) in H
  | H: _ |= bst' _ _ ?p, N: ?p <> /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_nonnull N) in H
  | s: set Z, H: forall x: Z, ~ _ |- _ =>
      lazymatch goal with
      | |- context[s ?v] =>
          lazymatch type of H with
          | context[s] => unique pose proof (H v)
          end
      end
  | |- ?A \/ ?B =>
      tryif (assert_succeeds (assert (~ A) by (zify_goal; xlia zchecker)))
      then right else
      tryif (assert_succeeds (assert (~ B) by (zify_goal; xlia zchecker)))
      then left else fail
  | H1: ?x <= ?y, H2: ?y <= ?x, C: ?s ?x |- ?s ?y =>
      (replace y with x by xlia zchecker); exact C
  | |- _ => solve [auto 3]
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

  unfold ready, bst.
ex1 in post needs to become termination measure! tricky generalization step when not written down completely manually
"just" pull out ex1 from sep and ands? no, still need weakening step to introduce existential

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
    { unfold bst.
      lazymatch goal with
      | |- with_finalpost_fyi (fun _ _ _ => expect_1expr_return ?P _ _ _)
                              (?post_evar _ ?g0 _ _ _) =>
          let tg := type of g0 in
          lazymatch eval pattern s, p, R in P with
          | ?genP s p R =>
              unify post_evar (fun (sk: tree_skeleton) (g: tg) ti mi li =>
               let '(s, olda, F) := g in
               exists a res,
                 li = map.of_list [|("a", a); ("p", p); ("res", res); ("v", v)|] /\
                   genP s a F ti mi res);
              let post := eval cbv beta in post_evar in idtac post
          end
      end.

fun sk (g: (set Z * word * (mem -> Prop))) ti mi li =>
                        let '(s, olda, F) := g in
                        exists a res,
                        li = map.of_list [|("a", a); ("p", p); ("res", res); ("v", v)|] /\
                        <{ * bst' sk s olda * F }> mi /\
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        ti = t).

      unfold with_finalpost_fyi, bst.
      steps.
      eapply sep_ex1_l. exists Leaf. steps.
      (* TODO heapletwise with only one heaplet *)
      eapply sep_emp_l. split. 2: assumption.
      steps.
    }
    (* loop body: *)
    let H := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as H.
    clear H0 H1 D. rename r into a, res0 into res.
                                                                                .**/
    uintptr_t here = load32(a+4);                                          /**. .**/
    if (v < here) /* split */ {                                            /**. .**/
      a = load(a);                                                         /**. .**/
    }                                                                      /**.

{
.**/
    else {                                                                 /**. .**/
      if (here < v) /* split */ {                                          /**. .**/
        a = load(a+8);                                                     /**. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        res = 1;                                                           /**. .**/
      }                                                                    /**. .**/
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
