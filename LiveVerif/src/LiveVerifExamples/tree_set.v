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

  loop pre above a.
  move R after a. move s after a.
  swap p with a in #(bst').

  unfold ready.
  let cond := constr:(live_expr:(!res && a != 0)) in
  let measure0 := constr:(sk) in
  eapply (wp_while_tailrec_with_done_flag measure0 (s, a, R) cond).
  1: eauto with wf_of_type.
  { (* delete #(a = p). *)
    move Def1 after Scope2.

    collect_heaplets_into_one_sepclause.

  lazymatch goal with
  | H: _ ?m |- ?E ?t ?m ?l =>
      (* always package sep log assertion, even if memory was not changed in current block *)
      move H at bottom;
      (* when proving a loop invariant at the end of a loop body, it tends to work better
         if memory hyps come earlier, because they can help determine evars *)
      lazymatch goal with
      | s: scope_marker _ |- _ =>
          move H before s (* <-- "before" in the direction of movement *)
      end
      (* Note: the two above moves should be replaced by one single `move H below s`,
         but `below` is not implemented yet: https://github.com/coq/coq/issues/15209 *)
  | |- ?E ?t ?m ?l => fail "No separation logic hypothesis about" m "found"
  end;
  let Post := fresh "Post" in
  pose proof ands_nil as Post;
  repeat add_hyp_to_post Post.

  add_equalities_to_post Post.
  repeat add_last_var_or_hyp_to_post Post.
  (* add_var_as_exists_to_post a Post. : *)

let x := a in
  vpattern x in Post;
  lazymatch type of Post with
  | ?f x => eapply (ex_intro f x) in Post
  end.
(* NO  clear x. *)

(*
add ghosts and measure last, without clearing them (because eqs further above might contain the ghosts)
why do we clear at all?
just for bookkeeping so that the loop works?
need tracking of what is ghost var and measure because they might be defined further
up in order to be usable in non-loopinv assertions


  let lasthyp := last_var_except Post in
  lazymatch type of lasthyp with
  | scope_marker _ => idtac
  | _ => idtac "Warning: package_context failed to package" lasthyp "(and maybe more)"
  end;
  lazymatch goal with
  | |- _ ?Measure ?Ghosts ?T ?M ?L => pattern Measure, Ghosts, T, M, L in Post
  | |- _ ?Measure ?T ?M ?L => pattern Measure, T, M, L in Post
  | |- _ ?T ?M ?L => pattern T, M, L in Post
  end;
  (let t := type of Post in log_packaged_context t);
  exact Post.

    package_context. }
  {

Ltac start_loop_body :=
    repeat match goal with
      | H: sep _ _ ?M |- _ => clear M H
      end;
    clear_until_LoopInvOrPreOrPost_marker;
    (* Note: will also appear after loop, where we'll have to clear it,
       but we have to pose it here because the foralls are shared between
       loop body and after the loop *)
    (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
    cbv beta;
    intros;
    unpackage_context;
    lazymatch goal with
    | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
    | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
    end.

    start_loop_body. subst g.
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
      steps.
      (* TODO heapletwise with only one heaplet *)
      eapply sep_emp_l. split. 2: assumption.
      steps.
    }
    (* loop body: *)
    let H := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as H.
                                                                                .**/
    uintptr_t here = load32(a+4);                                          /**. .**/
    if (v < here) /* split */ {                                            /**. .**/
      a = load(a);                                                         /**. .**/
    }                                                                      /**. .**/
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
  subst a. clear res Def0.
  clear_until_LoopInvOrPreOrPost_marker.
  steps.
  subst l.
                                                                                .**/
  return res;                                                              /**. .**/
}                                                                          /**.
Qed.
*)
Abort.

(* note: inability to break out of loop is cumbersome, because it complicates pre:
   it has to incorporate almost all of post for the res=true case,
   and even if we break, we still have to decrease the termination measure *)

End LiveVerif. Comments .**/ //.
