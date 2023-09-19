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

(* Note: one level of indirection because sometimes we have to change the root
   pointer (eg from null (empty) to non-null) or it is convenient *)
Definition bst(s: set Z)(addr: word): mem -> Prop :=
  ex1 (fun rootp => <{ * uintptr rootp addr
                       * freeable 4 addr
                       * ex1 (fun sk: tree_skeleton => bst' sk s rootp) }>).

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
Local Hint Extern 1 (PredicateSize_not_found allocator_failed_below)
      => constructor : suppressed_warnings.
Local Hint Extern 1 (PredicateSize_not_found (@allocator _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (if _ then _ else _))
      => constructor : suppressed_warnings.

#[export] Instance spec_of_bst_init: fnspec :=                              .**/

uintptr_t bst_init( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' res := t' = t /\
                       <{ * (if \[res] =? 0 then
                               allocator_failed_below 4
                             else
                               <{ * allocator
                                  * bst (fun _ => False) res }>)
                          * R }> m' #**/                                   /**.
Derive bst_init SuchThat (fun_correct! bst_init) As bst_init_ok.                .**/
{                                                                          /**. .**/
  uintptr_t res = malloc(4);                                               /**. .**/
  if (res == NULL) /* split */ {                                           /**. .**/
    return NULL;                                                           /**. .**/
  }                                                                        /**.
    replace (\[/[0]] =? 0) with true by steps.
    replace (0 =? 0) with true in * by steps.
    steps.
                                                                                .**/
  else {                                                                   /**.
    replace (\[res] =? 0) with false in * by steps.
    let h := constr:(#(@sep)) in unfold with_mem, anyval in h.
    step. step. step.
    match goal with
    | h: _ |- _ => change (with_mem m0 (array (uint 8) 4 v res)) in h
    end.
                                                                                .**/
    store(res, NULL);                                                      /**. .**/
    return res;                                                            /**. .**/
  }                                                                        /**.
    replace (\[res] =? 0) with false by steps.
    steps.
    instantiate (2 := Leaf). clear Error. unfold find_superrange_hyp. cbn [bst'].
    steps.
                                                                                .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_bst_add: fnspec :=                              .**/

uintptr_t bst_add(uintptr_t p, uintptr_t v) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * allocator
                     * bst s p
                     * R }> m;
  ensures t' m' q := t' = t /\
                     (if \[q] =? 0 then
                        <{ * allocator_cannot_allocate 12
                           * bst s p
                           * R }> m'
                      else
                        <{ * allocator
                           * bst (fun x => x = \[v] \/ s x) q
                           * R }> m') #**/                                 /**.
Derive bst_add SuchThat (fun_correct! bst_add) As bst_add_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t a = load(p);                                                   /**.
  (* invariant: *p = a *)                                                       .**/
  uintptr_t found = 0;                                                     /**.

  prove (found = /[1] -> s \[v]).
  delete #(found = /[0]).
  move sk after a.
  move p after a.
  loop invariant above a.
  unfold ready.
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern R in P with
      | ?f R =>
          change (exec fs body t m l ((fun (g: set Z * (mem -> Prop)) (_: tree_skeleton) =>
            let (_, F) := g in f F) (s, R) sk))
      end
  end.
  let e := constr:(live_expr:(a != NULL && !found)) in
  eapply (wp_while_tailrec_use_functionpost _ _ e).
  { eauto with wf_of_type. }
  { (* Ltac log_packaged_context P ::= idtac P. *)
    package_heapletwise_context. }
  start_loop_body.
  steps.
                                                                                .**/
    uintptr_t x = load32(a + 4);                                           /**. .**/
    if (x == v) {                                                          /**. .**/
      found = 1;                                                           /**. .**/
    } else {                                                               /**. .**/
      if (v < x) {                                                         /**. .**/
        p = a;                                                             /**. .**/
        a = load(p);                                                       /**. .**/
      } else {                                                             /**. .**/
        p = a + 8;                                                         /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**.
      (* TODO can we pull this out of the branches?
        a = load(p);                         *)                                 .**/
    }                                                                      /**. .**/
  }                                                                        /**.

Abort.

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
{                                                                          /**. .**/
  uintptr_t res = 0;                                                       /**. .**/
  uintptr_t a = load(p);                                                   /**.

  let h := constr:(#bst') in loop pre above h.
  (* TODO this step is needed because `m2 |= uintptr a p` will get pulled into
     the loop pre/post even though it could remain outside (because we currently
     mention the whole memory in the loop). Better: Use/integrate frame rule in
     loop rule so that unneeded mem hyps can stay outside *)
  let h := constr:(#(uintptr a p)) in remember a as root in h.

  unfold ready.
  let cond := constr:(live_expr:(!res && a != 0)) in
  let measure0 := constr:(sk) in
  eapply (wp_while_tailrec_with_done_flag measure0 (s, a, R) cond).
  1: eauto with wf_of_type.
  { collect_heaplets_into_one_sepclause.
    package_context. }
  { start_loop_body.
    steps.
    { (* loop condition false implies post (which could be constructed here from
         the context, hopefully) *)
      instantiate (1 := fun '(s, olda, F, sk, ti, mi, li) =>
                        exists newa res,
                        li = map.of_list [|("a", newa); ("p", p); ("res", res); ("v", v)|] /\
                          <{ * uintptr a p
                             * freeable 4 p
                             * bst' sk s olda
                             * F }> mi /\
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        ti = t).
      cbv beta iota.
      cbn [bst']. (* <-- TODO step_hook invoked too late *)
      step. step. step. step.
      steps.
    }
    (* loop body: *)
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

(* note: inability to break out of loop is cumbersome, because it complicates pre:
   it has to incorporate almost all of post for the res=true case,
   and even if we break, we still have to decrease the termination measure *)

End LiveVerif. Comments .**/ //.
