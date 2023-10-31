(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

(* TODO move to fwd_list_hints *)

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


(* TODO move to fwd_arith_hints *)

#[export] Instance Z_compare_eq(n m: Z): autoforward ((n ?= m) = Eq) (n = m).
Proof. unfold autoforward. apply Z.compare_eq_iff. Qed.

#[export] Instance Z_compare_lt(n m: Z): autoforward ((n ?= m) = Lt) (n < m).
Proof. unfold autoforward. apply Z.compare_lt_iff. Qed.

#[export] Instance Z_compare_gt(n m: Z): autoforward ((n ?= m) = Gt) (m < n).
Proof. unfold autoforward. apply Z.compare_gt_iff. Qed.

(* TODO move *)

Lemma Z_compare_eq_impl(n m: Z): safe_implication (n = m) ((n ?= m) = Eq).
Proof. unfold safe_implication. apply Z.compare_eq_iff. Qed.

Lemma Z_compare_lt_impl(n m: Z): safe_implication (n < m) ((n ?= m) = Lt).
Proof. unfold safe_implication. apply Z.compare_lt_iff. Qed.

Lemma Z_compare_gt_impl(n m: Z): safe_implication (m < n) ((n ?= m) = Gt).
Proof. unfold safe_implication. apply Z.compare_gt_iff. Qed.

#[export] Hint Resolve Z_compare_eq_impl Z_compare_lt_impl Z_compare_gt_impl
  : safe_implication.

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

#[export] Instance strCmp_spec: fnspec :=                                       .**/

uintptr_t strCmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list Z) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare Z.compare s1 s2 = Z.compare (word.signed res) 0 /\
                       <{ * nt_str s1 p1
                          * nt_str s2 p2
                          * R }> m' #**/                                   /**.
Derive strCmp SuchThat (fun_correct! strCmp) As strCmp_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t c1 = 0;                                                        /**. .**/
  uintptr_t c2 = 0;                                                        /**.

  delete #(c1 = ??).
  delete #(c2 = ??).
  loop invariant above c1.
  (* Local Arguments ready : clear implicits. *)
  do 2 let h := constr:(#List.In) in move h before t.
  set (p1_pre := p1) in *. change p1_pre with p1 at 1. move p1_pre before t.
  set (p2_pre := p2) in *. change p2_pre with p2 at 1. move p2_pre before p1_pre.
  prove (\[p1 ^- p1_pre] <= len s1).
  prove (\[p2 ^- p2_pre] <= len s2).
  prove (\[p1 ^- p1_pre] = \[p2 ^- p2_pre]).
  prove (s1[:\[p1 ^- p1_pre]] = s2[:\[p2 ^- p2_pre]]).
  clearbody p1_pre p2_pre.

  move p1 after c2. move p2 after p1.
                                                                                .**/
  do /* decreases (len s1 - \[p1 ^- p1_pre]) */ {                          /**. .**/
    c1 = deref8(p1);                                                       /**. .**/
    c2 = deref8(p2);                                                       /**. .**/
    p1 = p1 + 1;                                                           /**. .**/
    p2 = p2 + 1;                                                           /**. .**/
  } while (c1 == c2 && c1 != 0);                                           /**.

  1-4: assert (\[p1' ^- p1_pre] <> len s1)
         by (zify_goal; intro; bsimpl_in_hyps; congruence).
  1-4: assert (\[p2' ^- p2_pre] <> len s2)
         by (zify_goal; intro; bsimpl_in_hyps; congruence).
  1: solve [steps].
  1: solve [zify_hyps; steps].

  (* TODO include in purification of array? *)
  all: assert (len s1 < 2^32) by admit.
  all: assert (len s2 < 2^32) by admit.

  { rewrite (List.split_at_index (s1[:\[p1 ^- p1_pre]]) (\[p1' ^- p1_pre])).
    step. step. congruence.
    (* TODO diff between slice start and end is 1 *)
    admit. }

  solve [step].

                                                                                .**/
  uintptr_t res = c1 - c2;                                                 /**. .**/
  return res;                                                              /**. .**/
}                                                                          /**.

  unzify.

  let A := constr:(#array) in
  eapply purify_array_ith_elem in A;
  [ | once (typeclasses eauto with purify) ];
  specialize (A \[p2' ^- p2_pre]); cbv beta in A;
  bottom_up_simpl_in_hyp A;
  specialize (A ltac:(zify_hyps; zify_goal; xlia zchecker)).

  let A := constr:(#array) in
  eapply purify_array_ith_elem in A;
  [ | once (typeclasses eauto with purify) ];
  specialize (A \[p1' ^- p1_pre]); cbv beta in A;
  bottom_up_simpl_in_hyp A;
  specialize (A ltac:(zify_hyps; zify_goal; xlia zchecker)).

  destr (\[p1' ^- p1_pre] =? len s1);
  destr (\[p2' ^- p2_pre] =? len s2);
  fwd; zify_hyps; bsimpl_in_hyps.
  - subst s1. admit. (* List.compare_refl *)
  - unzify. rewrite (List.split_at_index s2 \[p2' ^- p2_pre]).
    let h := constr:(#(s1 = ??)) in rewrite <- h.
    admit. (* List.compare_l_is_prefix *)
  - unzify. rewrite (List.split_at_index s1 \[p1' ^- p1_pre]).
    let h := constr:(#(?? = s2)) in rewrite h.
    admit. (* List.compare_r_is_prefix *)
  - unzify.
    rewrite (List.split_at_index s2 \[p2' ^- p2_pre]).
    rewrite (List.split_at_index s1 \[p1' ^- p1_pre]).
    admit. (* List.compare_common_prefix *)
Abort.

#[export] Instance strcmp_spec: fnspec :=                                       .**/

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

    assert (len s1 <> 0) by (intro; bsimpl_in_hyps; congruence).
    assert (len s2 <> 0) by (intro; bsimpl_in_hyps; congruence).

    steps.

    erewrite List.compare_cons_cons_same; try lia; try assumption.
    repeat match goal with
           | H: with_mem _ (array _ _ _ _) |- _ =>
               eapply array1_to_elem' in H;
               [ new_mem_hyp H | zify_goal; xlia zchecker ]
           end.
    bsimpl_in_hyps.
    steps.

                                                                                .**/
  uintptr_t res = c1 - c2;                                                 /**. .**/
  return res;                                                              /**. .**/
}                                                                          /**.
  unzify.

  do 2 (let A := constr:(#array) in
        eapply purify_array_ith_elem in A;
        [ | typeclasses eauto with purify ];
        specialize (A 0); cbv beta in A;
        bottom_up_simpl_in_hyp A;
        specialize (A ltac:(lia))).

  destruct s1; destruct s2; simpl; symmetry; fwd; bsimpl_in_hyps;
    zify_hyps; steps.
  destruct_one_match; zify_hyps; steps.
Qed.

End LiveVerif. Comments .**/ //.
