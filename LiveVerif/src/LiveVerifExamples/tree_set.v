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

Load LiveVerif.

Context {consts: malloc_constants}.

Fixpoint bst'(sk: tree_skeleton)(s: set Z)(addr: word){struct sk}: mem -> Prop :=
  match sk with
  | Leaf => emp (addr = /[0] /\ forall x, ~ s x)
  | Node skL skR => ex1 (fun p: word => (ex1 (fun v: Z => (ex1 (fun q: word =>
      <{ * emp (addr <> /[0])
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
  repeat heapletwise_step.
Qed.

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
  eapply (wp_while_tailrec measure0 (s, a, R) cond)
         with (pre := fun sk (g: (set Z * word * (mem -> Prop))) ti mi li =>
                        let '(s, a, F) := g in
                        exists res,
                        li = map.of_list [|("a", a); ("p", p); ("res", res); ("v", v)|] /\
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0) /\
                        <{ * bst' sk s a * F }> mi /\
                        ti = t).
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
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        <{ * bst' sk s olda * F }> mi /\
                        ti = t).
      cbv beta iota.
      clear Error.
      destruct H.
      { steps. clear Error.
        assert (res0 = /[1]) by (zify_hyps; zify_goal; xlia zchecker). subst res0.
        destruct Hp1. 2: { exfalso. bottom_up_simpl_in_hyps. discriminate. }
        bottom_up_simpl_in_goal. intuition auto. }
      { steps. clear Error.
        subst r.
        let H := constr:(#bst') in eapply invert_bst'_null in H.
        steps. clear Error.
        right. destruct Hp1.
        { exfalso. eapply H2. eapply H. }
        eauto. }
    }
    (* loop body: *)
    let H := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as H.
    clear H0 H1 D. rename v0 into sk0, r into a, res0 into res.
    let H := constr:(#(bst')) in eapply invert_bst'_nonnull in H.
    2: assumption.
    fwd. repeat heapletwise_step.
    .**/ uintptr_t here = load32(a+4); /**.
    .**/ if (here == v) {  /**.
    .**/   res = 1;        /**.
    .**/ } else {          /**.
    .**/   if (v < here) { /**.
    .**/     a = load(a);  /**.
    .**/   } else {        /**.
    .**/     a = load(a+8); /**.
    .**/   }                /**.
    .**/ a = a; /**.
    .**/ }                  /**.
    .**/ a = a; /**.
    .**/ } /**.
    all: clear Error.
    { (* smaller precondition holds: *)
      instantiate (2 := (_, _, _)). cbv iota.
      step. step. step.
      apply and_comm.
      unzify.
      (* TODO don't merge before proving smaller pre, lt, and impl *)
Abort.

End LiveVerif. Comments .**/ //.
