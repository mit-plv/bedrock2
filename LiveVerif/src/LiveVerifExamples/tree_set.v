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


  (* Useful for while loops with a done flag:
     Once done is set to true, we don't need to prove pre again for the
     next non-iteration, but we can prove post instead. *)
  Lemma wp_while_tailrec_with_done_flag {measure: Type} {Ghost: Type}
    (v0: measure) (g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre post: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {finalpost: trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      exists b, dexpr_bool3 m l e b
                  (* can't put loop body under context of b=true because we
                     first need to treat the b=false case (which determines post): *)
                  True
                  (* packaging generalized context at exit of loop (with final, smallest
                     measure) determines post: *)
                  (post (g, v, t, m, l))
                  (loop_body_marker (bool_expr_branches b (wp_cmd fs c t m l
                      (fun t' m' l' => exists b',
                         (* evaluating condition e again!! *)
                         dexpr_bool3 m' l' e b'
                           (exists v' g',
                               pre (g', v', t', m', l') /\
                               lt v' v /\
                               (forall t'' m'' l'', post (g', v', t'', m'', l'') ->
                                                    post (g , v , t'', m'', l'')))
                           (post (g, v, t', m', l'))
                           True)) True True)))
    (Hrest: forall t m l, post (g0, v0, t, m, l) -> wp_cmd fs rest t m l finalpost)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t0 m0 l0 finalpost.
  Proof.
    pose proof Hbody as Hinit.
    specialize Hinit with (1 := Hpre). destruct Hinit as (b & Hinit).
    inversion Hinit. subst. clear Hinit. unfold bool_expr_branches in H1.
    apply proj1 in H1.
    eapply wp_while_tailrec with
      (v0 := (negb (word.eqb v (word.of_Z 0)), v0))
      (pre := fun (av: bool * measure) g t m l =>
                let (again, v) := av in
                (exists w, dexpr m l e w /\ again = negb (word.eqb w (word.of_Z 0))) /\
                if again then  pre (g, v, t, m, l) else post (g, v, t, m, l))
      (post := fun (av: bool * measure) g t m l =>
                 let (again, v) := av in post (g, v, t, m, l)).
    { eapply well_founded_with_again_flag. eapply Hwf. }
    { split.
      { eexists. split. 1: eassumption. reflexivity. }
      destr (word.eqb v (word.of_Z 0)); simpl in *.
      1: eassumption. assumption. }
    { intros. fwd. try subst b. destr (word.eqb w (word.of_Z 0)); simpl in *.
      { exists false. econstructor. 1: eassumption.
        { rewrite word.eqb_eq; reflexivity. }
        { unfold bool_expr_branches, loop_body_marker. auto. } }
      { specialize Hbody with (1 := H0p1). destruct Hbody as (b & Hbody).
        inversion Hbody. subst c0. exists b. clear Hbody. subst.
        econstructor. 1: eassumption. 1: reflexivity.
        unfold bool_expr_branches in *.
        destr (word.eqb v1 (word.of_Z 0)); simpl in *.
        1: assumption.
        split. 1: constructor. apply proj2 in H3. unfold loop_body_marker in *.
        apply proj1 in H3. split. 2: constructor.
        eapply weaken_wp_cmd. 1: eassumption.
        cbv beta. clear H3. intros. fwd. inversion H2. subst. clear H2.
        unfold bool_expr_branches in *. apply proj1 in H5.
        destr (word.eqb v2 (word.of_Z 0)); simpl in *.
        { eexists (false, m1(* old, big measure! *)), _.
          ssplit.
          { eexists. split. 1: eassumption. rewrite word.eqb_eq; reflexivity. }
          { eassumption. }
          { exact I. }
          intros *. exact id. }
        { fwd.
          eexists (true, v'(* new, smaller measure *)), _.
          ssplit.
          { eexists. split. 1: eassumption. rewrite word.eqb_ne by assumption.
            reflexivity. }
          { eassumption. }
          { simpl. assumption. }
          assumption. } } }
      { assumption. }
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

  let h := constr:(#bst') in loop pre above h.
  swap p with a in #(bst').
  let h := constr:(#(a = p)) in move h before sk.

  unfold ready.
  let cond := constr:(live_expr:(!res && a != 0)) in
  let measure0 := constr:(sk) in
  eapply (wp_while_tailrec_with_done_flag measure0 (s, a, R) cond).
  1: eauto with wf_of_type.
  {
    collect_heaplets_into_one_sepclause.

  lazymatch goal with
  | H: _ ?m |- ?E (_, ?t, ?m, ?l) =>
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
  | |- ?E (_, ?t, ?m, ?l) => fail "No separation logic hypothesis about" m "found"
  end;
  let Post := fresh "Post" in
  pose proof ands_nil as Post;
  repeat add_hyp_to_post Post.

  lazymatch goal with
  | |- ?E (_, ?T, ?M, ?L) =>
      add_equality_to_post L Post;
      move M at top;
      lazymatch type of Post with
      | context[T] => idtac (* current packaged context already says something about the
                               trace, so only keep that *)
      | _ => add_equality_to_post T Post (* no assertion about trace, so let's add default
                                            assertion saying it doesn't change *)
      end
  end.

  repeat add_last_var_or_hyp_to_post Post.

(* attempt to save names in dlet2's lambda (quadratic)

Definition dlet2[A B R: Type](rhs : A * B)(body: A -> B -> R): R :=
  match rhs with
  | (a, b) => body a b
  end.


Ltac pattern_one_more_in_hyp p h :=
  pattern p in h;
  lazymatch type of h with
  | (fun x => (fun y => @?body y x) ?paty) ?patx =>
      let f := eval cbv beta in (fun tup0 => dlet2 tup0 body) in
      change (f (paty, patx)) in h
  end.

Ltac pattern_tuple_in_hyp t h :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple_in_hyp rest h;
      pattern_one_more_in_hyp outermost h
  | _ => pattern t in h
  end.



  let lasthyp := last_var_except Post in
  lazymatch type of lasthyp with
  | scope_marker _ => idtac
  | _ => idtac "Warning: package_context failed to package" lasthyp "(and maybe more)"
  end.
  lazymatch goal with
  | |- _ ?p => pattern_tuple_in_hyp p Post
  end.
*)



(********)

Ltac pattern_one_more_in_hyp p h :=
  pattern p in h;
  lazymatch type of h with
  | (fun x => (fun y => @?body y x) ?paty) ?patx =>
      let f := eval cbv beta in (fun tup => match tup with (a0, a1) => body a0 a1 end) in
      change (f (paty, patx)) in h
  end.

Ltac pattern_tuple_in_hyp t h :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple_in_hyp rest h;
      pattern_one_more_in_hyp outermost h
  | _ => pattern t in h
  end.



  let lasthyp := last_var_except Post in
  lazymatch type of lasthyp with
  | scope_marker _ => idtac
  | _ => idtac "Warning: package_context failed to package" lasthyp "(and maybe more)"
  end.
  lazymatch goal with
  | |- _ ?p => pattern_tuple_in_hyp p Post
  end.

  (let t := type of Post in log_packaged_context t);
  exact Post.
  }
  {

Ltac pair_destructuring_intros_step :=
  lazymatch goal with
  | |- forall (_: _ * _), _ =>
      (* doesn't really do any intro, but does one step of splitting, leaving
         both sides of the * up for further splitting *)
      let x := fresh in intro x; case x; clear x
  | |- forall _, _ => intro
  end.

Ltac start_loop_body :=
    repeat match goal with
      | H: sep _ _ ?M |- _ => clear M H
      end;
    clear_until_LoopInvOrPreOrPost_marker;
    (* Note: will also appear after loop, where we'll have to clear it,
       but we have to pose it here because the foralls are shared between
       loop body and after the loop *)
    (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
    repeat pair_destructuring_intros_step;
    unpackage_context;
    lazymatch goal with
    | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
    | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
    end.

    start_loop_body.
    (* TODO name locals according to string names
       (could be useful to simplify if-then-else code too) *)

    (*
    steps.
    { (* loop condition false implies post (which could be constructed here from
         the context, hopefully) *)
      instantiate (1 := fun '(s, olda, F, sk, ti, mi, li) =>
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
unfold ready.
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
