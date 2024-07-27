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

Definition same_set{A: Type}(s1 s2: set A) := forall x, s1 x <-> s2 x.
Definition is_empty_set{A: Type}(s: set A) := forall x, ~ s x.

Load LiveVerif.

Context {consts: malloc_constants}.

Fixpoint bst'(sk: tree_skeleton)(s: set Z)(addr: word){struct sk}: mem -> Prop :=
  match sk with
  | Leaf => emp (addr = /[0] /\ is_empty_set s)
  | Node skL skR => EX (p: word) (v: Z) (q: word),
      <{ * emp (addr <> /[0])
         * emp (s v)
         * freeable (sizeof uintptr * 2 + 4) addr
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
     | Node _ _ => sizeof uintptr * 2 + 4
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
      <{ * freeable (sizeof uintptr * 2 + 4) p
         * <{ + uintptr pL
              + uint 32 v
              + uintptr pR }> p
         * bst' skL (fun x => s x /\ x < v) pL
         * bst' skR (fun x => s x /\ v < x) pR }> m.
Proof.
  intros.
  destruct sk; simpl in *.
  { exfalso. unfold with_mem, emp in *. intuition idtac. }
  repeat heapletwise_step.
  eexists _, _, p0, v, q. split. 1: reflexivity.
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

Import FunctionalExtensionality PropExtensionality.

Lemma bst'_change_set: forall sk a s1 s2,
    safe_implication (same_set s1 s2) (impl1 (bst' sk s1 a) (bst' sk s2 a)).
Proof.
  unfold safe_implication, same_set. intros.
  replace s2 with s1. 1: reflexivity.
  extensionality x.
  apply propositional_extensionality.
  apply H.
Qed.

#[local] Hint Resolve bst'_change_set : safe_implication.

(* always unify (set A) with (A -> Prop) *)
#[global] Hint Transparent set : safe_implication.

Ltac zset_solver :=
  unfold same_set, is_empty_set;
  intros;
  lazymatch goal with
  | |- _ <-> _ => split
  | |- _ => idtac
  end;
  intuition (lia || congruence || solve [eauto 3]).

Ltac step_hook ::=
  match goal with
  | |- _ => progress cbn [bst']
  | |- context C[8 * 2 + 4] => let g := context C[20] in change g (* TODO generalize *)
  | |- context C[4 * 2 + 4] => let g := context C[12] in change g (* TODO generalize *)
  | sk: tree_skeleton |- _ => progress subst sk
  | |- same_set _ _ => reflexivity (* <- might instantiate evars and we're fine with that *)
  | |- same_set _ _ => zset_solver
  | |- is_empty_set _ => zset_solver
  | H: _ |= bst' _ _ ?p, E: ?p = /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_null E) in H
  | H: _ |= bst' _ _ ?p, E: \[?p] = 0 |- _ =>
      eapply invert_bst'_null in H; [ | zify_goal; xlia zchecker ]
  | H: _ |= bst' _ _ ?p, N: ?p <> /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_nonnull N) in H
  | H: ?addr <> /[0] |- context[bst' ?sk_evar _ ?addr] =>
      is_evar sk_evar;
      let n := open_constr:(Node _ _) in unify sk_evar n
  | |- context[bst' ?skEvar ?s /[0]] => is_evar skEvar; unify skEvar Leaf
  | s: set Z, H: forall x: Z, ~ _ |- _ =>
      lazymatch goal with
      | |- context[s ?v] =>
          lazymatch type of H with
          | context[s] => unique pose proof (H v)
          end
      end
  | s: set Z |- _ =>
      match goal with
      | H: s ?x1 |- s ?x2 =>
          assert_fails (idtac; has_evar x2);
          assert_fails (idtac; has_evar x1);
          replace x2 with x1; [exact H | solve[steps]]
      | |- ~ s _ => zset_solver
      end
  | H: ?res = ?c1 /\ _ \/ ?res = ?c2 /\ _
    |- ?res = ?c1 /\ _ \/ ?res = ?c2 /\ _ =>
      assert_succeeds (idtac; assert (c1 <> c2) by (zify_goal; xlia zchecker));
      destruct H; [left|right]
  | |- ?A \/ ?B =>
      tryif (assert_succeeds (assert (~ A) by (zify_goal; xlia zchecker)))
      then right else
      tryif (assert_succeeds (assert (~ B) by (zify_goal; xlia zchecker)))
      then left else fail
  | H1: ?x <= ?y, H2: ?y <= ?x, C: ?s ?x |- ?s ?y =>
      (replace y with x by xlia zchecker); exact C
  | H: _ \/ _ |- _ => decompose [and or] H; clear H; try (exfalso; xlia zchecker); []
  | |- _ => solve [auto 3 with nocore safe_core]
  end.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | bst' ?sk2 ?s2 =>
      lazymatch hypPred with
      | bst' ?sk1 ?s1 =>
          (* Note: address has already been checked, and if sk and/or s don't
             unify, sidecondition solving steps will make them match later,
             so here, we just need to take care of instantiating evars from conclPred *)
          try syntactic_unify_only_inst_r s1 s2;
          try syntactic_unify_only_inst_r sk1 sk2
      end
  end.

Ltac provide_new_ghosts_hook ::= manual_new_ghosts.

#[export] Instance spec_of_bst_remove_max: fnspec :=                              .**/

uintptr_t bst_remove_max(uintptr_t c) /**#
  ghost_args := p s sk (R: mem -> Prop);
  requires t m := p <> /[0] /\
                  <{ * allocator
                     * uintptr p c
                     * bst' sk s p
                     * R }> m;
  ensures t' m' r := t' = t /\ exists sk' q,
                     s \[r] /\
                     (forall x, s x -> x <= \[r]) /\
                     <{ * allocator
                        * uintptr q c
                        * bst' sk' (fun x => s x /\ x < \[r]) q
                        * R }> m' #**/                                     /**.
Derive bst_remove_max SuchThat (fun_correct! bst_remove_max)
As bst_remove_max_ok.                                                           .**/
{                                                                          /**. .**/
  uintptr_t p = load(c);                                                   /**. .**/
  uintptr_t res = 0;                                                       /**.
  (* Local Arguments ready : clear implicits. *)
  loop invariant above p.
  delete #(res = ??).
  move skR before t.
                                                                                .**/
  do /* initial_ghosts(s, c, skR, R); decreases skR */ {                   /**. .**/
    c = p + sizeof(uintptr_t) + 4;                                         /**. .**/
    p = load(c);                                                           /**. .**/
    if (p) /* split */ {                                                   /**. .**/
      /* nothing to do */                                                  /**. .**/
    }                                                                      /**.
      instantiate (3 := expr.var "p"). (* <-- need to give loop termination cond
                                          already here... *)
      steps.
      new_ghosts((fun x => (s x /\ v < x)), c, skR, _).
      steps.
      { destr (x <=? v). 1: lia. eauto. }
                                                                                .**/
    else {                                                                 /**. .**/
      res = load32(c - 4);                                                 /**. .**/
    }                                                                      /**.
Abort.

#[export] Instance spec_of_bst_init: fnspec :=                              .**/

void bst_init(uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (sizeof uintptr) ? p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * bst (fun _ => False) p
                      * R }> m' #**/                                       /**.
Derive bst_init SuchThat (fun_correct! bst_init) As bst_init_ok.                .**/
{                                                                          /**. .**/
  store(p, 0);                                                             /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_bst_alloc_node: fnspec :=                              .**/

uintptr_t bst_alloc_node( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' res := t' = t /\
                       ((\[res] =  0 /\ <{ * allocator_failed_below (sizeof uintptr * 2 + 4)
                                           * R }> m') \/
                        (\[res] <> 0 /\ <{ * allocator
                                           * freeable (sizeof uintptr * 2 + 4) res
                                           * uintptr ? res
                                           * uint 32 ? (res ^+ /[sizeof uintptr])
                                           * uintptr ? (res ^+ /[sizeof uintptr + 4])
                                           * R }> m')) #**/                /**.
Derive bst_alloc_node SuchThat (fun_correct! bst_alloc_node)
As bst_alloc_node_ok.                                                           .**/
{                                                                          /**. .**/
  uintptr_t res = Malloc(sizeof(uintptr_t) + 4 + sizeof(uintptr_t));       /**. .**/
  return res;                                                              /**. .**/
}                                                                          /**.
  destruct_one_match_hyp; steps.
Qed.

Ltac provide_new_ghosts_hook ::= guess_new_ghosts.

#[export] Instance spec_of_bst_add: fnspec :=                              .**/

uintptr_t bst_add(uintptr_t p, uintptr_t vAdd) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := \[vAdd] < 2 ^ 32 /\
                  <{ * allocator
                     * bst s p
                     * R }> m;
  ensures t' m' r := t' = t /\
                     ((\[r] = 0 /\ <{ * allocator_failed_below (sizeof uintptr * 2 + 4)
                                      * bst s p
                                      * R }> m') \/
                      (\[r] = 1 /\ <{ * allocator
                                      * bst (fun x => x = \[vAdd] \/ s x) p
                                      * R }> m')) #**/                     /**.
Derive bst_add SuchThat (fun_correct! bst_add) As bst_add_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t a = load(p);                                                   /**.
  (* invariant: *p = a *)                                                       .**/
  uintptr_t found = 0;                                                     /**.

  pose (measure := sk).
  prove (found = /[0] /\ measure = sk \/ found = /[1] /\ s \[vAdd]) as A.
  move A before sk.
  clearbody measure.
  delete (#(found = /[0])).
  move p after t.
  move sk before t.
  (* Local Arguments ready : clear implicits. *)
  loop invariant above a.
  (* Ltac log_packaged_context P ::= idtac P. *)
                                                                                .**/
  while (a && !found)
    /* initial_ghosts(p, s, sk, R); decreases(measure) */
  {                                                                        /**. .**/
    uintptr_t x = load32(a + sizeof(uintptr_t));                           /**. .**/
    if (x == vAdd) /* split */ {                                           /**. .**/
      found = 1;                                                           /**. .**/
    }                                                                      /**.
      (* arbitrarily pick skL, could also pick skR, just need something smaller *)
      eapply tree_skeleton_lt_l. constructor.                                   .**/
    else {                                                                 /**. .**/
      if (vAdd < x) /* split */ {                                          /**. .**/
        p = a;                                                             /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        p = a + sizeof(uintptr_t) + 4;                                     /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
  if (found) /* split */ {                                                 /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    /* key not found, so we zoomed into the tree until it is empty, and
       shrinked the function's postcondition and the context -- there's
       no more tree around, and we'll just retrun a singleton tree! */     /**. .**/
    uintptr_t res = bst_alloc_node();                                      /**. .**/
    if (res) /* split */ {                                                 /**. .**/
      store(res, 0);                                                       /**. .**/
      store32(res + sizeof(uintptr_t), vAdd);                              /**. .**/
      store(res + sizeof(uintptr_t) + 4, 0);                               /**. .**/
      store(p, res);                                                       /**. .**/
      return 1;                                                            /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**. .**/
      /* malloc failed! */                                                 /**. .**/
      return 0;                                                            /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_bst_contains: fnspec :=                              .**/

uintptr_t bst_contains(uintptr_t p, uintptr_t query) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * bst s p
                     * R }> m;
  ensures t' m' b := t' = t /\
                     (\[b] = 1 /\ s \[query] \/ \[b] = 0 /\ ~ s \[query]) /\
                     <{ * bst s p
                        * R }> m' #**/                                     /**.
Derive bst_contains SuchThat (fun_correct! bst_contains) As bst_contains_ok.    .**/
{                                                                          /**. .**/
  uintptr_t found = 0;                                                     /**. .**/
  uintptr_t a = load(p);                                                   /**.

  move sk after found.
  pose (measure := sk).
  loop invariant above a.
  prove (found = /[0] /\ measure = sk \/ found = /[1] /\ s \[query]) as A.
  move A before found.
  delete #(found = ??).
  clearbody measure.
  move sk before t.
  (* Ltac log_packaged_context P ::= idtac P. *)
                                                                                .**/
  while (!found && a != 0)
    /* initial_ghosts(p, s, sk, R); decreases measure */
  {                                                                        /**. .**/
    uintptr_t here = load32(a + sizeof(uintptr_t));                        /**. .**/
    if (query < here) /* split */ {                                        /**. .**/
      p = a;                                                               /**. .**/
      a = load(p);                                                         /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**. .**/
      if (here < query) /* split */ {                                      /**. .**/
        p = a + sizeof(uintptr_t) + 4;                                     /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        found = 1;                                                         /**. .**/
      }                                                                    /**.
        (* arbitrarily pick skL, could also pick skR, just need something smaller *)
        eapply tree_skeleton_lt_l. constructor.                                 .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
  return found;                                                            /**. .**/
}                                                                          /**.
  destr (\[a] =? 0); steps. zset_solver.
Qed.

(* Note: inability to break out of loop is cumbersome, because it complicates pre:
   - it has to incorporate almost all of post for the res=true case
     ==> not too bad though, in these examples
   - and even if we are done, we still have to decrease the termination measure
     ==> trick: separate variable for termination measure, and only link it to sep
         clauses in pre if done flag is false *)

End LiveVerif. Comments .**/ //.
