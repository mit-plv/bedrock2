(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Lia.

Load LiveVerif.

Record node := {
  data: word;
  next: word;
}.
Definition node_t(r: node): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uintptr_t data;
  uintptr_t next;
} node_t;
/**.

Fixpoint sll (L : list word) (p : word): mem -> Prop :=
  match L with
  | nil => emp (p = /[0])
  | x::L' => ex1 (fun q =>
         (* TODO maybe all judgments, including uintptr etc, should enforce pointers
            to be non-NULL? *)
      <{ * emp (p <> /[0])
         * uintptr x p
         * uintptr q (p ^+ /[4])
         * sll L' q }>)
  end.

Lemma purify_sll: forall L p, purify (sll L p) True.
Proof.
  unfold purify. auto.
Qed.
Hint Resolve purify_sll | 5 : purify.

Local Hint Extern 1 (PredicateSize (sll ?l)) =>
  let r := eval cbv iota in
    (match l with
     | cons _ _ => 8
     | nil => 0
     end) in
  exact r
: typeclass_instances.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | sll ?l2 => lazymatch hypPred with
               | sll ?l1 => syntactic_unify_only_inst_r hypPred conclPred
               end
  end.

Lemma invert_sll_null: forall l m, m |= sll l /[0] -> m |= emp (l = nil).
Proof.
  unfold with_mem. intros. destruct l; simpl in *.
  - unfold emp in *. destruct H. auto.
  - destruct H as [q H]. repeat heapletwise_step. congruence.
Qed.

Lemma invert_sll_nonnull: forall l m p, p <> /[0] -> sll l p m -> exists x l' q,
  l = x :: l' /\
  <{ * uintptr x p
     * uintptr q (p ^+ /[4])
     * sll l' q }> m.
Proof.
  intros. destruct l.
  - simpl in *. eapply purify_emp in H0. congruence.
  - simpl in *. destruct H0 as [q M]. eapply sep_emp_l in M. apply proj2 in M. eauto.
Qed.

Lemma fold_sll_cons: forall p, p <> /[0] -> forall x q l m,
  <{ * uintptr x p
     * uintptr q (p ^+ /[4])
     * sll l q }> m ->
  sll (cons x l) p m.
Proof.
  intros. simpl. unfold ex1. exists q.
  eapply sep_emp_l. auto.
Qed.

(* even though in-place, memory cell containing the head of the element will change,
   so it returns a pointer to the new head of the list (which used to be its last cell) *)
#[export] Instance spec_of_sll_reverse: fnspec := .**/

uintptr_t sll_reverse(uintptr_t p) /**#
  ghost_args := (l : list word) (R: mem -> Prop);
  requires t m := <{ * sll l p
                     * R }> m;
  ensures t' m' r := t' = t /\
       <{ * sll (List.rev l) r
          * R }> m' #**/ /**.
Derive sll_reverse SuchThat (fun_correct! sll_reverse) As sll_reverse_ok.       .**/
{                                                                          /**. .**/
  uintptr_t acc = 0;                                                       /**.

  pose (lDone := @nil word).
  pose (lTodo := l).
  prove (l = lDone ++ lTodo). { reflexivity. }
  move H before acc.
  swap l with lTodo in #(sll l p).
  swap R with (sep (sll (List.rev lDone) acc) R) in #R.
  { subst lDone. simpl. eapply iff1ToEq.
    step. cancel. simpl. unfold emp, iff1. intuition idtac. }
  unfold with_mem in H1.
  repeat heapletwise_step.
  clearbody lDone. clearbody lTodo.
  loop invariant above acc.
  move p after acc.
  delete #(acc = ??).

                                                                                .**/
  while (p != 0) /* decreases (len lTodo) */ {                             /**.

    match goal with
    | H: _ |= sll lTodo p |- _ => rename H into HT
    end.
    eapply invert_sll_nonnull in HT. 2: assumption. fwd. repeat heapletwise_step.
                                                                                .**/
    uintptr_t tail = load(p + 4);                                          /**. .**/
    store(p + 4, acc);                                                     /**.

    epose proof (fold_sll_cons _ #(p <> /[0])) as HL.
    cancel_in_hyp HL.
    rewrite <- List.rev_unit in HL.
                                                                                .**/
    acc = p;                                                               /**. .**/
    p = tail;                                                              /**. .**/
  }                                                                        /**.
  subst v. subst lTodo.
  bottom_up_simpl_in_goal.
  step.
                                                                                .**/
  return acc;                                                              /**.

  eapply invert_sll_null in H2.
  repeat heapletwise_step. subst lTodo.
  bottom_up_simpl_in_hyps. subst lDone.
                                                                                .**/
}                                                                          /**.
Qed.

Ltac provide_new_ghosts_hook ::= manual_new_ghosts.

#[export] Instance spec_of_sll_inc: fnspec := .**/

void sll_inc(uintptr_t p) /**#
  ghost_args := (l : list word) (R: mem -> Prop);
  requires t m := <{ * sll l p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * sll (List.map (word.add (word.of_Z 1)) l) p
          * R }> m' #**/ /**.
Derive sll_inc SuchThat (fun_correct! sll_inc) As sll_inc_ok.                   .**/
{                                                                          /**.

  let H := constr:(#sll) in loop invariant above H.
  unfold ready.

  let cond := constr:(live_expr:(p != 0)) in
  let measure0 := constr:(len l) in
  eapply (wp_while_tailrec measure0 (l, p, R) cond)
         with (pre := fun '(L, p, F, v, ti, m, l) => ands [|
                        l = map.of_list [|("p", p)|];
                        v = len L;
                        <{ * sll L p * F }> m;
                        ti = t|]).

  1: eauto with wf_of_type.
  1: solve [steps].
  { start_loop_body. subst t0.
    steps.
    { (* when loop condition is false, post must hold, and by generalizing it from
         the symbolic state, we can design it, hopefully without spelling it out
         completely... *)

      instantiate (1 := fun '(L, oldp, F, v, ti, m, l) =>
                          exists p, l = map.of_list [|("p", p)|] /\
                          v = len L /\
                          <{ * sll (List.map (word.add (word.of_Z 1)) L) oldp
                             * F }> m /\
                          ti = t).
      cbv beta iota.
      subst p.
      eapply invert_sll_null in H0.
      heapletwise_step.
      (* note: only one heaplet left --> D gets deleted, and heapletwise stops working *)
      repeat heapletwise_step.
      subst L.
      simpl (sll _ _).
      steps.
      eapply sep_emp_l. auto. }

    { (* loop body *)

      let H := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as H.

      match goal with
      | H: _ |= sll _ ?addr |- _ => rename H into HT, addr into p
      end.
      eapply invert_sll_nonnull in HT. 2: assumption. fwd. repeat heapletwise_step.

      .**/ uintptr_t val = load(p); /**.
      (* unfold ready. *)
      .**/ store(p, val + 1); /**.
      .**/ p = load(p + 4); /**.

      .**/ } /**. new_ghosts(l', _, _).
    cbn [ands].
    rewrite ->?and_assoc. (* to make sure frame evar appears in Rest of canceling, so
                             that canceling_step doesn't instantiate frame with anymem *)

    (* symbolic state at end of loop body implies smaller loop precondition: *)
    step. step. step. step.
    assert (and_flip: forall A B C: Prop, B /\ A /\ C -> A /\ B /\ C). {
      clear. intuition idtac.
    }
    (* manual flipping to make it look more like a function call so that
       heapletwise's "instantiate frame with wand" trick works: *)
    eapply and_flip. split. 1: reflexivity.
    eapply and_flip. split. 1: exact I.
    eapply and_flip. split. 1: lia.
    eapply and_flip. split.
    { (* TODO this is an example where seeing through equalities matters: *)
      subst v L. step. }
    step. step. step. step. step.

    (* small post implies bigger post: *)
    step. step.
    step. step. step. step. step. step.
    step. step. step.

    epose proof (fold_sll_cons _ #(p' <> /[0])) as HL.
    cancel_in_hyp HL.
    subst L.

    simpl (List.map _ (_ ++ _)).

    steps.
  } }

  (* after loop: *)
  cbv beta. intros. fwd. steps.
  clear Scope2.

  .**/ } /*?.
  subst. steps.
Qed.

End LiveVerif. Comments .**/ //.
