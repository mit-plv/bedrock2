(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

Load LiveVerif.

Section Array.
  Context [T: Type] (elem: T -> word -> mem -> Prop) {sz: PredicateSize elem}.

  Lemma array1_to_elem'{inh: Inhabited.inhabited T}: forall addr l n m,
      n = 1 ->
      with_mem m (array elem n l addr) ->
      with_mem m (elem l[0] addr).
  Proof. intros * ->. eapply array1_to_elem. Qed.
End Array.

Local Ltac step_hook ::= solve [auto using List.notin_from with nocore safe_core].

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
  return c1 - c2;                                                          /**. .**/
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

Ltac provide_new_ghosts_hook ::= manual_new_ghosts.

#[export] Instance Strcmp_spec: fnspec :=                                       .**/

uintptr_t Strcmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list Z) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare Z.compare s1 s2 = Z.compare (word.signed res) 0 /\
                       <{ * nt_str s1 p1
                          * nt_str s2 p2
                          * R }> m' #**/                                   /**.
Derive Strcmp SuchThat (fun_correct! Strcmp) As Strcmp_ok.                      .**/
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
  return c1 - c2;                                                          /**. .**/
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
