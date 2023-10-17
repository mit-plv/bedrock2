(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

(* TODO move *)

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
  unfold ready.
  set (p1_pre := p1). change p1_pre with p1 at 1.
  pose proof (eq_refl: p1_pre = p1). clearbody p1_pre. move p1_pre before t.
  set (p2_pre := p2). change p2_pre with p2 at 1.
  pose proof (eq_refl: p2_pre = p2). clearbody p2_pre. move p2_pre before p1_pre.
  move p1 after c2. move p2 after p1.
  (* pattern out ghost vars from functionpost to get post of do-while lemma: *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern s1, s2, p1_pre, p2_pre, R, (len s1) in P with
      | ?f s1 s2 p1_pre p2_pre R (len s1) =>
          change (exec fs body t m l ((fun (g: list Z * list Z * word * word * (mem -> Prop)) (v: Z) =>
          let (g, R) := g in
          let (g, p2_pre) := g in
          let (g, p1_pre) := g in
          let (s1, s2) := g in
          ltac:(let r := eval cbv beta in (f s1 s2 p1_pre p2_pre R v) in exact r))
                (s1, s2, p1_pre, p2_pre, R) (len s1)))
      end
  end.
  eapply wp_dowhile_tailrec_use_functionpost.
  { eauto with wf_of_type. }
  {  Ltac log_packaged_context P ::= idtac P.
    package_heapletwise_context. }
  start_loop_body.
  steps.

  .**/
  c1 = deref8(p1);                                                         /**. .**/
  c2 = deref8(p2);                                                         /**. .**/
  p1 = p1 + 1;                                                             /**. .**/
  p2 = p2 + 1;                                                             /**.

  unfold ready.

  let e := constr:(live_expr:(c1 == c2 && c1 != 0)) in
  lazymatch goal with
  (* from hypothesis of do-while lemma: *)
  | |- exec _ _ ?t ?m ?l (fun t' m' l' =>
     exists b, dexpr_bool3 _ _ ?condEvar _ _ _ _) => unify condEvar e
  end.
  step. step.

  .**/ } /**. new_ghosts(s1[1:], s2[1:], p1, p2, _).

  assert (0 < len s1). {
    assert (len s1 <> 0). {
      intro C. destruct s1.
      - bottom_up_simpl_in_hyps. congruence.
      - discriminate C.
    }
    lia.
  }

  assert (0 < len s2). {
    assert (len s2 <> 0). {
      intro C. destruct s2.
      - bottom_up_simpl_in_hyps. congruence.
      - discriminate C.
    }
    lia.
  }

step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step.

clear_heapletwise_hyps.
clear_mem_split_eqs.
clear_heaplets.

(* function post with small ghosts implies function post with bigger ghosts: *)

intros t'' m'' l'' EE. inversion EE. clear EE. eapply mk_expect_1expr_return.
1: eassumption.

step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step.

{
  erewrite List.compare_cons_cons_same; try assumption.
  eapply Z.compare_eq_iff.
  subst p1 p2.
  bottom_up_simpl_in_hyps.
  let h := constr:(#(s1[:1])) in eapply array1_to_elem in h; purify_hyp h.
  let h := constr:(#(s2[:1])) in eapply array1_to_elem in h; purify_hyp h.
  bottom_up_simpl_in_hyps.
  zify_hyps.
  xlia zchecker.
}

(* Need to join the char at p1' (coming from bigger frame of smaller post)
   with its tail at p1 (coming from smaller post) in order to satisfy
   bigger post.
   Or split what we have in the goal: *)

step. step. step. step. step. step. step. step. step. step. step.

step. rewrite List.app_assoc. step. subst p1. step.
symmetry. apply List.split_at_index.

step. step. step. step. step. step. step. step. step. step. step. step.

step. rewrite List.app_assoc. step. subst p2. step.
symmetry. apply List.split_at_index.

step. step. step. step.

clear Scope2. (* not in loop body any more *)

.**/
  uintptr_t res = c1 - c2;                                                 /**. .**/
  return res;                                                              /**. .**/
}                                                                          /**.
unzify.
unfold don't_know_how_to_prove.

destruct s1; destruct s2; simpl; symmetry.
- eapply Z.compare_eq_iff.
  bottom_up_simpl_in_hyps. subst res.
  apply word.signed_of_Z_nowrap. lia.
- eapply Z.compare_lt_iff.
  bottom_up_simpl_in_hyps. subst res.
  assert (0 <= z < 2 ^ 8). {
    let h := constr:(#((z :: s2) ++ [|0|])) in rename h into A.
    eapply purify_array_ith_elem in A.
    2: typeclasses eauto with purify.
    specialize (A 0). cbv beta in A.
    bottom_up_simpl_in_hyp A.
    lia.
  }
  assert (z <> 0). {
    intro C. subst z. let h := constr:(#(~List.In 0 (0 :: ??))) in apply h.
    constructor. reflexivity.
  }
  rewrite word.signed_opp. rewrite word.signed_eq_swrap_unsigned.
  rewrite word.unsigned_of_Z_nowrap by lia.
  rewrite (word.swrap_inrange z) by lia.
  unfold word.swrap. zify_goal. xlia zchecker.
- eapply Z.compare_gt_iff.
  bottom_up_simpl_in_hyps. subst res.
  assert (0 <= z < 2 ^ 8). {
    let h := constr:(#((z :: s1) ++ [|0|])) in rename h into A.
    eapply purify_array_ith_elem in A.
    2: typeclasses eauto with purify.
    specialize (A 0). cbv beta in A.
    bottom_up_simpl_in_hyp A.
    lia.
  }
  assert (z <> 0). {
    intro C. subst z. let h := constr:(#(~List.In 0 (0 :: ??))) in apply h.
    constructor. reflexivity.
  }
  rewrite word.signed_eq_swrap_unsigned.
  rewrite word.unsigned_of_Z_nowrap by lia.
  rewrite (word.swrap_inrange z) by lia. lia.
- bottom_up_simpl_in_hyps.
  assert (0 <= z < 2 ^ 8). {
    let h := constr:(#((z :: s1) ++ [|0|])) in rename h into A.
    eapply purify_array_ith_elem in A.
    2: typeclasses eauto with purify.
    specialize (A 0). cbv beta in A.
    bottom_up_simpl_in_hyp A.
    lia.
  }
  assert (z <> 0). {
    intro C. subst z. let h := constr:(#(~List.In 0 (0 :: ??))) in apply h.
    constructor. reflexivity.
  }
  assert (0 <= z0 < 2 ^ 8). {
    let h := constr:(#((z0 :: s2) ++ [|0|])) in rename h into A.
    eapply purify_array_ith_elem in A.
    2: typeclasses eauto with purify.
    specialize (A 0). cbv beta in A.
    bottom_up_simpl_in_hyp A.
    lia.
  }
  assert (z0 <> 0). {
    intro C. subst z0. let h := constr:(#(~List.In 0 (0 :: ??))) in apply h.
    constructor. reflexivity.
  }
  assert (z = \[c1]) by (zify_hyps; zify_goal; xlia zchecker).
  assert (z0 = \[c2]) by (zify_hyps; zify_goal; xlia zchecker).
  subst z z0 res.
  destruct_one_match.
  + eapply Z.compare_eq_iff in E.
    exfalso.
    assert (c1 = /[0]) by (zify_hyps; zify_goal; xlia zchecker).
    subst c1.
    eapply H4. constructor. bottom_up_simpl_in_goal. reflexivity.
  + eapply (proj1 (Z.compare_lt_iff _ _)) in E.
    eapply Z.compare_lt_iff.
    rewrite 2word.of_Z_unsigned.
    rewrite word.signed_sub.
    rewrite 2word.signed_eq_swrap_unsigned.
    unfold word.swrap. zify_goal. xlia zchecker.
  + eapply (proj1 (Z.compare_gt_iff _ _)) in E.
    eapply Z.compare_gt_iff.
    rewrite 2word.of_Z_unsigned.
    rewrite word.signed_sub.
    rewrite 2word.signed_eq_swrap_unsigned.
    unfold word.swrap. zify_goal. xlia zchecker.
Unshelve.
all: typeclasses eauto.
Qed.

End LiveVerif. Comments .**/ //.
