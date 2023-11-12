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
  | Node skL skR => EX (p: word) (v: Z) (q: word),
      <{ * emp (addr <> /[0])
         * emp (s v)
         * freeable 12 addr
         * <{ + uintptr p
              + uint 32 v
              + uintptr q }> addr
         * bst' skL (fun x => s x /\ x < v) p
         * bst' skR (fun x => s x /\ v < x) q }>
  end.

(* Note: one level of indirection because sometimes we have to change the root
   pointer (eg from null (empty) to non-null or vice versa) *)
Definition bst(s: set Z)(addr: word): mem -> Prop :=
  EX rootp, <{ * uintptr rootp addr
               * EX sk: tree_skeleton, bst' sk s rootp }>.

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
  | H: ?addr <> /[0] |- context[bst' ?sk_evar _ ?addr] =>
      is_evar sk_evar;
      let n := open_constr:(Node _ _) in unify sk_evar n
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
  | H: _ \/ _ |- _ => decompose [and or] H; clear H; try (exfalso; xlia zchecker); []
  | |- impl1 (bst' _ _ ?a) (bst' _ _ ?a) =>
      reflexivity (* might instantiate evars and that's ok here, as long as the
                     address is the same on both sides *)
  | |- _ => solve [auto 3]
  end.

#[export] Instance spec_of_bst_init: fnspec :=                              .**/

void bst_init(uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) 4 ? p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * bst (fun _ => False) p
                      * R }> m' #**/                                       /**.
Derive bst_init SuchThat (fun_correct! bst_init) As bst_init_ok.                .**/
{                                                                          /**. .**/
  store(p, 0);                                                             /**. .**/
}                                                                          /*?.
  step. step. step. step. step. step. step. step.
  instantiate (1 := Leaf).
  steps.
Qed.

#[export] Instance spec_of_bst_add: fnspec :=                              .**/

uintptr_t bst_add(uintptr_t p, uintptr_t v) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * allocator
                     * bst s p
                     * R }> m;
  ensures t' m' r := t' = t /\
                     ((\[r] = 0 /\ <{ * allocator_failed_below 12
                                      * bst s p
                                      * R }> m') \/
                      (\[r] = 1 /\ <{ * allocator
                                      * bst (fun x => x = \[v] \/ s x) p
                                      * R }> m')) #**/                     /**.
Derive bst_add SuchThat (fun_correct! bst_add) As bst_add_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t a = load(p);                                                   /**.
  (* invariant: *p = a *)                                                       .**/
  uintptr_t found = 0;                                                     /**.

  pose (measure := sk).
  prove (found = /[0] /\ measure = sk \/ found = /[1] /\ s \[v]) as A.
  move A before sk.
  clearbody measure.
  delete (#(found = /[0])).
  move p after t.
  move sk before t.
  Local Arguments ready : clear implicits.
  loop invariant above a.
  (* Ltac log_packaged_context P ::= idtac P. *)
                                                                                .**/
  while (a != NULL && !found)
    /* initial_ghosts(p, s, sk, R); decreases(measure) */
  {                                                                        /**. .**/
    uintptr_t x = load32(a + 4);                                           /**. .**/
    if (x == v) /* split */ {                                              /**. .**/
      found = 1;                                                           /**. .**/
    }                                                                      /**.
      (* Note: (Node skL skR) doesn't decrease but that's also not the measure *)
      new_ghosts(_, _, Node skL skR , _).
      steps.
      { subst v. bottom_up_simpl_in_goal. assumption. }
      { (* arbitrarily pick skL, could also pick skR, just need something smaller *)
        eapply tree_skeleton_lt_l. constructor. }
                                                                                .**/
    else {                                                                 /**. .**/
      if (v < x) /* split */ {                                             /**. .**/
        p = a;                                                             /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**.
        new_ghosts(_, _, skL, _).
        step. step. step. step. step. step. step. step. step. step. step.
        step. step. step. step.

        (* hole is introduced *)
        step.
        step. step. step.
        (* hole gets move into second subgoal through evar *)
        step. step. step. step. step. step. step. step. step.
        steps.
        lazymatch goal with
        | H: _ \/ _ |- _ \/ _ => destruct H; [left|right]
        end.


step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. 1-2: cycle 1.
step. step. step.
lazymatch goal with
| |- context C[sepapps ?l p] =>
    let r := eval cbn in (sepapps l p) in
    let g := context C[r] in
    change g
end.
unfold sepapp.
lazymatch goal with
| H: ?m |= sepapps ?l p |- _ =>
    let r := eval cbn in (sepapps l p) in
    change (r m) in H;
    unfold sepapp, hole in H
end.
steps.
step.
steps.
clear Error.
lazymatch goal with
| |- context C[sepapps ?l p] =>
    let r := eval cbn in (sepapps l p) in
    let g := context C[r] in
    change g
end.
unfold sepapp.
lazymatch goal with
| H: ?m |= sepapps ?l p |- _ =>
    let r := eval cbn in (sepapps l p) in
    change (r m) in H;
    unfold sepapp, hole in H
end.
step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step.
clear Def0 x __Z_Def0.
replace (fun x : Z => (x = \[v] \/ s x) /\ x < \[v]) with
        (fun x : Z => s x /\ x < \[v]).
2: { Import FunctionalExtensionality PropExtensionality.
     extensionality x.
     apply propositional_extensionality.
     split; steps. }
replace (fun x : Z => (x = \[v] \/ s x) /\ \[v] < x) with
        (fun x : Z => s x /\ \[v] < x).
2: { extensionality x.
     apply propositional_extensionality.
     split; steps. }

(* key sets don't match?? *)

(*
      } else {                                                             /**. .**/
        p = a + 8;                                                         /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**.
      (* TODO can we pull this out of the branches?
        a = load(p);                         *)                                 .**/
    }                                                                      /**.
      new_ghosts(_, if c then skL else skR, _).
      steps.

      step.
                                                                               .**/
  }                                                                        /**.

{

  (* different clause is picked for cancellation based on which of the 3 branches was
     taken, need to do case split... *)
  subst p''''. p''.
*)

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
  eapply (wp_while_tailrec_skip_last_pre measure0 (s, a, R) cond).
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
      steps.
(*
    }
    (* loop body: *)
                                                                                .**/
    uintptr_t here = load32(a+4);                                          /**. .**/
    if (v < here) /* split */ {                                            /**. .**/
      a = load(a);                                                         /**. .**/
    }                                                                      /*?.

step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step.
step. step.

step. (* change: applies invert_bst'_nonnull in H3, earlier than before! *)

step. step. step. step. step. step. step. step. new_ghosts(_, _, _). step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step.

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
