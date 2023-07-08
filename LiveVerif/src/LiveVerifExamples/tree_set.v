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

Lemma tree_skeleton_lt_l: forall sk1 sk2 skOther,
    sk2 = Node sk1 skOther -> safe_implication True (tree_skeleton_lt sk1 sk2).
Proof. unfold safe_implication, tree_skeleton_lt. intros. subst. auto. Qed.

Lemma tree_skeleton_lt_r: forall sk1 sk2 skOther,
    sk2 = Node skOther sk1 -> safe_implication True (tree_skeleton_lt sk1 sk2).
Proof. unfold safe_implication, tree_skeleton_lt. intros. subst. auto. Qed.

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
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        <{ * bst' sk s olda * F }> mi /\
                        ti = t).
      cbv beta iota.
      clear Error.
      destruct H. 1: contradiction.
      { steps. clear Error.
        subst r.
        let H := constr:(#bst') in eapply invert_bst'_null in H.
        steps. clear Error.
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
    }                                                                      /*?.

      step. step. step. step. step. step. step. step. step. step. step.
      step. step. step. step. step. step. step. step. step. step. step.
      step. step. step. step. step. step. step. step. step.
      step.
      step. step. step. step. step. step. step. step.
      (* smaller post implies bigger post: *)
      intros.
      step. step. step. step. step. step. step. step. step. step. step.
      intuition idtac.
      step. step.

      step.
Abort.
(*

subst l''.

let logger := fun _ => idtac in
lazymatch goal with
  | |- @eq (@map.rep string (@word.rep _ _) _) ?LHS ?RHS =>
      is_map_expr_with_ground_keys LHS;
      is_map_expr_with_ground_keys RHS;
      logger ltac:(fun _ => idtac "proving equality between two locals maps");
      let LHS' := normalize_locals_expr LHS in
      let RHS' := normalize_locals_expr RHS in
      change (LHS' = RHS');
      repeat f_equal
end.


      (* TODO *)

 step. step. step.

      f_equal.

step. step. step. step. step.
      step. step. step. step. step. step. step. step. step. step. step.
      step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step.
step. step. step.
Set Nested Proofs Allowed.

step.
  lazymatch goal with
  | |- tree_skeleton_lt ?sk1 ?sk2 => try subst sk1; try subst sk2
  end.

unfold tree_skeleton_lt.
step.
auto.

subst sk0.

step.

      f_equal.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      f_equal.


Ltac evar_tuple t :=
  lazymatch t with
  | prod ?t1 ?t2 =>
      let e1 := evar_tuple t1 in
      let e2 := evar_tuple t2 in
      constr:(pair e1 e2)
  | _ => lazymatch open_constr:(_ : t) with
         | ?e => e
         end
  end.

      lazymatch goal with
      | |- exists x: ?t, _ => let e := evar_tuple t in exists e
      end.
                                                              split.
      lazymatch goal with
      | |- exists x: ?t, _ => let e := evar_tuple t in exists e
      end.



      lazymatch goal with
      | |- exists g: _ * _, let '(_, _) := g in _ => idtac g
      end.



 step.
      step. step.
      instantiate (2 := (_, _, _)). cbv iota. eexists.
      step. step. step. step.
      steps.

          eapply wp_skip;
          lazymatch goal with
          | |- needs_to_be_closed_by_single_rbrace ?g => change g
          | |- _ => fail "this then-branch needs to be closed by '} else {'"
          end.


lazymatch goal with
  | |- branch_post ?l0 ?new_vars ?Q ?t ?m ?l =>
      split; [ reflexivity | ];
      let l' := normalize_locals_expr l in
      change (Q t m l');
      tryif is_evar Q then package_heapletwise_context else cbv beta
end.

          step.

unfold ready.
    .**/ } /**.
      bla_tac.
    .**/
    else {                   /**.
 unfold ready.
2: {

    .**/ } else {         /**.
    .**/   if (here < v) {  /**.
    .**/     a = load(a+8); /**.
    .**/   } else {         /**.
    .**/     res = 1;       /**.
    .**/   }                /**.
    .**/   a = a; /**.
    .**/ }                  /**.
    .**/ a = a; /**.
    .**/ } /*?.
    step. step. step. step. step. step. step. step. step. step.
    step. step. step. step. step. step. step. step. step.
    2,3,4: exact I.
    2: step. 2,4: exact I.
    (* two possible outcomes
    2: {
step.
    destr (word.ltu v /[v0]); subst c.
    all: steps; clear Error.
    { (* smaller precondition holds: *)
      unzify.
      instantiate (2 := (_, _, _)). cbv iota. eexists.
      step. step. step. subst a.
      step. step. step. step. step. step.
      subst here.
      destr (word.eqb /[v0] v); subst res.
      { exfalso. lia. }
      { right. bottom_up_simpl_in_goal. reflexivity. }
      step. }
    { (* measure decreases: *)
      subst sk0. cbn. auto. }
    { (* small postcondition implies bigger postcondition: *)
      cbv iota.
      intros. fwd. subst sk0. cbn [bst']. repeat step.
      { intuition lia. }
      { assumption. } }
    { (* smaller precondition holds: *)
      unzify.
      instantiate (2 := (_, _, _)). cbv iota. eexists.
      step. step. step. subst a.
      step. step. step. step. step. step.
      subst here.
      destr (word.eqb /[v0] v); subst res.
      { bottom_up_simpl_in_goal.
        (* oh no, doing a fake recursive call (even though we're done)
           just to evaluate the loop condition one more time (to find it's false)
           requires us to prove its pre, and since the termination measure is
           required to go down, new set membership condition becomes (s0 v0 /\ v0 < v0) *)
*)
*)

(* note: inability to break out of loop is cumbersome, because it complicates pre:
   it has to incorporate almost all of post for the res=true case,
   and even if we break, we still have to decrease the termination measure *)


End LiveVerif. Comments .**/ //.
