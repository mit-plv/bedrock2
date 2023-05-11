(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Lia.

Load LiveVerif.

(* TODO support functions that don't access any memory *)
Definition dummy: mem -> Prop := emp True.

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

#[export] Instance spec_of_malloc: fnspec :=                         .**/
uintptr_t malloc(uintptr_t size)                                     /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  ensures t' m' retPtr := t' = t /\ exists anyData,
       <{ * dummy
          * array uintptr \[size] anyData retPtr
          * R }> m'                                                   #**/ /**.
Parameter malloc : function_with_callees.
Parameter malloc_ok : program_logic_goal_for "malloc" malloc.


#[export] Instance spec_of_malloc_node: fnspec :=                    .**/
uintptr_t malloc_node(uintptr_t anything)                                 /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  (* ensures t' m' retPtr := t' = t /\
                          <{ * ex1 (fun x => node x retPtr)
                             * R }> m                               #**/ /**. *)
  ensures t' m' retPtr := t' = t /\ exists x,
                          <{ * dummy
                             * node_t x retPtr
                             * R }> m'                               #**/ /**.
Derive malloc_node SuchThat (fun_correct! malloc_node) As malloc_node_ok. .**/
{ /**. .**/
  uintptr_t r = malloc(2);   /**.
  assert (len anyData = 2) as Hlen by hwlia.

  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [idtac | simpl in Hlen; lia].

  .**/ return r; /**.
.**/ } /**.

  unfold node_t.
  unfold sepapps.
  simpl.
  unfold sepapp.
  (* TODO: automated memory cast *)
  instantiate (1 := {| data := r0; next := r1 |}).
  unfold array.
  simpl.
  eapply iff1ToEq. cancel.
  unfold seps. unfold iff1. unfold emp. intuition.
Qed.

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
  }                                                                        /*?.

step. step. step. step. step. step. step. step. step. step. step. step.
step. step.
instantiate (1 := l').
step. step. step. step. step. step. step. step. step. step. step. step. step.
end while.
                                                                                .**/
  return acc;                                                              /**.

  eapply invert_sll_null in H2.
  repeat heapletwise_step. subst lTodo.
  bottom_up_simpl_in_hyps. subst lDone.
                                                                                .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_sll_prepend: fnspec := .**/

uintptr_t sll_prepend(uintptr_t p, uintptr_t val) /**#
  ghost_args := (L : list word) (R: mem -> Prop);
  requires t m := <{ * dummy
                     * sll L p
                     * R }> m;
  ensures t' m' res := t' = t /\
       <{ * dummy
          * sll (val::L) res
          * R }> m' #**/ /**.
Derive sll_prepend SuchThat (fun_correct! sll_prepend) As sll_prepend_ok. .**/
{ /**.
  (* TODO: a lot of dummys *)
  (* TODO: should support empty arguments *)
  .**/ uintptr_t r = malloc_node(-123); /**.
  (* set r.data = val *)
  .**/ store(r, val); /**.
  .**/ store(r+4, p); /**.
  .**/ return r; /**.
  (* TODO: all of this should probably be automated *)
  replace ((m4 \*/ (m2 \*/ m3)) \*/ m) with (m \*/ m2 \*/ m3 \*/ m4) in D by admit.
  assert (exists (mm2:mem), m \*/ m2 = mm2) as Hex by admit.
  destruct Hex as [mm2 Hex]. rewrite Hex in D. clear Hex.
  assert (mm2 |= sll (val :: L) r) by admit.
.**/ } /**.
Abort.

End LiveVerif. Comments .**/ //.
