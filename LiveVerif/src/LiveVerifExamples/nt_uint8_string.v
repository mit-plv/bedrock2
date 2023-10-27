(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

(* TODO move *)

Import coqutil.Tactics.autoforward.

#[export] Instance notin_nil[A: Type](a: A): autoforward (~ List.In a (@nil A)) True.
Proof. intros ?. constructor. Qed.

#[export] Instance notin_app[A: Type](a: A)(l1 l2: list A):
  autoforward (~ List.In a (l1 ++ l2)) (~ List.In a l1 /\ ~ List.In a l2).
Proof.
  intros ?. split; intro C; apply H; apply List.in_app_iff; auto.
Qed.

#[export] Instance notin_singleton[A: Type](x y: A):
  autoforward (~ List.In x (cons y nil)) (x <> y).
Proof. intros ? C. apply H. subst. constructor. reflexivity. Qed.

Module List.
  Section WithA.
    Context [A: Type].

    Lemma notin_from: forall (a: A) (i: Z) (l: list A),
        ~ List.In a l ->
        ~ List.In a (List.from i l).
    Proof.
      unfold List.from. intros. rewrite <- (List.firstn_skipn (Z.to_nat i) l) in H.
      intro C. apply H. apply List.in_or_app. right. assumption.
    Qed.

    Lemma notin_upto: forall (a: A) (i: Z) (l: list A),
        ~ List.In a l ->
        ~ List.In a (List.upto i l).
    Proof.
      unfold List.from. intros. rewrite <- (List.firstn_skipn (Z.to_nat i) l) in H.
      intro C. apply H. apply List.in_or_app. left. assumption.
    Qed.

    Lemma get_inj{inh: inhabited A}: forall (l1 l2: list A) (n: Z),
        Z.of_nat (List.length l1) = n ->
        Z.of_nat (List.length l2) = n ->
        (forall i, 0 <= i < n -> List.get l1 i = List.get l2 i) ->
        l1 = l2.
    Proof.
      intros. apply List.nth_inj with (n := Z.to_nat n) (d := default); try lia.
      intros. specialize (H1 (Z.of_nat i) ltac:(lia)).
      unfold List.get in *.
      destruct_one_match_hyp. 1: exfalso; lia.
      rewrite Nat2Z.id in *.
      assumption.
    Qed.
  End WithA.

  (* alternative: Coq.Structures.OrdersEx.String_as_OT.compare, but that's on strings,
     not on list of byte *)
  Section Lexicographic.
    Context {T: Type} (compare_elem: T -> T -> comparison).

    Fixpoint compare(a b: list T): comparison :=
      match a, b with
      | nil, nil => Eq
      | nil, _ => Lt
      | cons _ _, nil => Gt
      | cons a_head a_tail, cons b_head b_tail =>
          match compare_elem a_head b_head with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare a_tail b_tail
          end
      end.

    Import ZList.List.ZIndexNotations.
    Local Open Scope zlist_scope.

    Lemma compare_cons_cons_same{inh: inhabited T}: forall (l1 l2: list T),
        0 < len l1 ->
        0 < len l2 ->
        compare_elem l1[0] l2[0] = Eq ->
        compare l1 l2 = compare l1[1:] l2[1:].
    Proof.
      intros. destruct l1. 1: discriminate. destruct l2. 1: discriminate.
      cbn in H1. simpl (compare (_ :: _) _). rewrite H1. reflexivity.
    Qed.

  End Lexicographic.
End List.

Load LiveVerif.

Section Array.
  Context [T: Type] (elem: T -> word -> mem -> Prop) {sz: PredicateSize elem}.

  Lemma array1_to_elem'{inh: Inhabited.inhabited T}: forall addr l n m,
      n = 1 ->
      with_mem m (array elem n l addr) ->
      with_mem m (elem l[0] addr).
  Proof. intros * ->. eapply array1_to_elem. Qed.
End Array.

Local Ltac step_hook ::= solve [auto using List.notin_from].

Definition nt_str(s: list Z)(a: word): mem -> Prop :=
  sep (array (uint 8) (len s + 1) (s ++ [| 0 |]) a)
      (emp (~ List.In 0 s)).

#[local] Hint Unfold nt_str : heapletwise_always_unfold.

#[export] Instance str_cmp: fnspec :=                                           .**/

uintptr_t strcmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list Z) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare Z.compare s1 s2 = Z.compare (word.signed res) 0 /\
                       <{ * nt_str s1 p1
                          * nt_str s2 p2
                          * R }> m' #**/                                   /**.
Derive strcmp SuchThat (fun_correct! strcmp) As strcmp_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t c1 = 0;                                                        /**. .**/
  uintptr_t c2 = 0;                                                        /**.

  delete #(c1 = ??).
  delete #(c2 = ??).
  loop invariant above c1.
  (* Local Arguments ready : clear implicits. *)
  set (p1_pre := p1). change p1_pre with p1 at 1.
  pose proof (eq_refl: p1_pre = p1). clearbody p1_pre. move p1_pre before t.
  set (p2_pre := p2). change p2_pre with p2 at 1.
  pose proof (eq_refl: p2_pre = p2). clearbody p2_pre. move p2_pre before p1_pre.
  move p1 after c2. move p2 after p1.
                                                                                .**/
  do /* initial_ghosts(s1, s2, p1_pre, p2_pre, R); decreases (len s1) */ { /**. .**/
    c1 = deref8(p1);                                                       /**. .**/
    c2 = deref8(p2);                                                       /**. .**/
    p1 = p1 + 1;                                                           /**. .**/
    p2 = p2 + 1;                                                           /**. .**/
  } while (c1 == c2 && c1 != 0);                                           /**.

    new_ghosts(s1[1:], s2[1:], p1, p2, _).

    assert (len s1 <> 0) by (intro; bottom_up_simpl_in_hyps; congruence).
    assert (len s2 <> 0) by (intro; bottom_up_simpl_in_hyps; congruence).

    steps.

    unfold don't_know_how_to_prove.
    erewrite List.compare_cons_cons_same; try lia; try assumption.
    eapply Z.compare_eq_iff.
    repeat match goal with
           | H: with_mem _ (array _ _ _ _) |- _ =>
               eapply array1_to_elem' in H;
               [ new_mem_hyp H | zify_goal; xlia zchecker ]
           end.
    bottom_up_simpl_in_hyps.
    zify_hyps.
    xlia zchecker.

                                                                                .**/
  uintptr_t res = c1 - c2;                                                 /**. .**/
  return res;                                                              /**. .**/
}                                                                          /**.
  unzify.
  unfold don't_know_how_to_prove.

  do 2 (let A := constr:(#array) in
        eapply purify_array_ith_elem in A;
        [ | typeclasses eauto with purify ];
        specialize (A 0); cbv beta in A;
        bottom_up_simpl_in_hyp A;
        specialize (A ltac:(lia))).

  destruct s1; destruct s2; simpl; symmetry; fwd; bottom_up_simpl_in_hyps.
  - eapply Z.compare_eq_iff. steps.
  - eapply Z.compare_lt_iff. zify_hyps. steps.
  - eapply Z.compare_gt_iff. zify_hyps. steps.
  - destruct_one_match.
    + eapply Z.compare_eq_iff in E. zify_hyps. steps.
    + eapply (proj1 (Z.compare_lt_iff _ _)) in E.
      eapply Z.compare_lt_iff.
      zify_hyps. steps.
    + eapply (proj1 (Z.compare_gt_iff _ _)) in E.
      eapply Z.compare_gt_iff.
      zify_hyps. steps.
Qed.

End LiveVerif. Comments .**/ //.
