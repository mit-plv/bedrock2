(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import bedrock2Examples.LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.let_binding_to_eq.

Load LiveVerif.

Fixpoint fib_nat(n: nat): nat :=
  match n with
  | O => O
  | S m => match m with
           | O => 1
           | S k => fib_nat k + fib_nat m
           end
  end.

Definition fib(n: word): word := /[Z.of_nat (fib_nat (Z.to_nat \[n]))].

Set Default Proof Mode "Classic".

Lemma fib_recursion: forall n,
    0 < \[n] ->
    \[n] + 1 < 2 ^ 32 ->
    fib (n ^+ /[1]) = fib (n ^- /[1]) ^+ fib n.
Proof.
  unfold fib. intros.
  replace (Z.to_nat \[n ^+ /[1]]) with (S (S (pred (Z.to_nat \[n])))) by ZnWords.
  replace (Z.to_nat \[n ^- /[1]]) with (pred (Z.to_nat \[n])) by ZnWords.
  replace (Z.to_nat \[n]) with (S (pred (Z.to_nat \[n]))) at 3 by ZnWords.
  forget (pred (Z.to_nat \[n])) as m.
  change (fib_nat (S (S m))) with (fib_nat m + fib_nat (S m))%nat.
  ZnWords.
Qed.

Set Default Proof Mode "Ltac2".

#[export] Instance spec_of_fibonacci: fnspec :=                                 .**/

uintptr_t fibonacci(uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep (emp True) R m;
  ensures t' m' res := t' = t /\ sep (emp True) R m' /\ res = fib n #**/   /**.
Derive fibonacci SuchThat (fun_correct! fibonacci) As fibonacci_ok.             .**/
{                                                                          /**. .**/
  uintptr_t b = 0;                                                         /**. .**/
  if (n == 0) {                                                            /**. .**/
  } else {                                                                 /**. .**/
    uintptr_t a = 0;                                                       /**. .**/
    b = 1;                                                                 /**. .**/
    uintptr_t i = 1;                                                       /**.

    1: ltac1:(
    let_bindings_to_eqs;
    replace /[0] with (fib (i ^- /[1])) in Ha by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity);
    replace /[1] with (fib i) in Hb by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity);
    assert (1 <= \[i] <= \[n]) by ZnWords;
    eqs_to_let_bindings;
    clearbody i; move b after a).

    loop invariant above i.                                                     .**/

    while (i < n) /* decreases (\[n]-\[i]) */ {                            /**. .**/
      uintptr_t t = a + b;                                                 /**. .**/
      a = b;                                                               /**. .**/
      b = t;                                                               /**. .**/
      i = i + 1;                                                           /**.

{
unfold ready.

Proof Mode "Classic".

Ltac list_map_ignoring_failures f l :=
  lazymatch l with
  | nil => open_constr:(@nil _)
  | cons ?h ?t =>
      let r := list_map_ignoring_failures f t in
      match constr:(Set) with
      | _ => let h' := f h in constr:(cons h' r)
      | _ => r
      end
  end.

Ltac key_of_pair_if_not_in term pair :=
  lazymatch pair with
  | (?key, _) =>
      lazymatch term with
      | context[(key, _)] => fail
      | _ => key
      end
  end.

Ltac unset_vars vars :=
  lazymatch vars with
  | cons ?h ?t => eapply (wp_unset _ h); unset_vars t
  | nil => idtac
  end.

lazymatch goal with
| |- wp_cmd _ _ _ _ (map.of_list ?current) ?post =>
    let newvars := list_map_ignoring_failures ltac:(key_of_pair_if_not_in post) current in
    unset_vars newvars;
    normalize_locals
end.


Ltac run_steps_hook ::= idtac.

{
unfold ready.
          eapply wp_skip.
          ltac:(lazymatch goal with
                 | |- exists _, _ /\ _ => eexists; split
                 end).
{ exists i.
          1: ltac:(repeat lazymatch goal with
                      | |- exists _, _ => eexists
                 | |- dlet _ (fun x => _) => eapply let_to_dlet; make_fresh x; intro x
                 end).
Import syntactic_unify.
1: ltac:(lazymatch goal with
       | |- ?P /\ ?Q =>
           split;
           [ match P with
             | ?l = ?r => _syntactic_unify_deltavar l r; reflexivity
             | _ => ZnWords
             end
           | ]
       end).

{ split; [reflexivity| ].

split. {
repeat match goal with
       | x := _ |- _ => subst x
       end.
bottom_up_simpl_in_goal.
rewrite fib_recursion by ZnWords.
reflexivity.
}
repeat step.
}
}
ZnWords.
}
}

1: lazymatch goal with
   | H: scope_marker LoopBody |- _ => clear H
   end.

(* Proof Mode "Ltac2". *)
{
  close_block.
}

(* .**/ } /**. *)

clear Scope1.

  purify_heapletwise_hyps_instead_of_clearing;
  intros ? ? ? ? ?;
  repeat pull_dlet_and_exists_step;
  repeat merge_and_pair constr_eqb merge_ands_at_indices_same_prop;
  repeat merge_and_pair neg_prop merge_ands_at_indices_neg_prop;
  repeat merge_and_pair same_lhs merge_ands_at_indices_same_lhs;
  repeat merge_and_pair seps_about_same_mem merge_ands_at_indices_seps_same_mem;
  repeat merge_sep_pair_step;
  cbn [seps] in *;
  try match goal with
    | H: if _ then ands nil else ands nil |- _ => clear H
    end;
  subst_small_rhses
(*;
  lazymatch goal with
  | H: ?l = _ |- wp_cmd _ _ _ _ ?l _ =>
      repeat (rewrite ?push_if_into_cons_tuple_same_key,
                      ?if_same,
                      ?push_if_into_arg1,
                      ?push_if_into_arg2 in H);
      subst l
  end;
  letbind_locals 0%nat*)
.

Set Nested Proofs Allowed.
Import coqutil.Tactics.destr.

Set Default Proof Mode "Classic".

Lemma remove_many_remove_commute: forall (m: locals) k ks,
    map.remove_many (map.remove m k) ks = map.remove (map.remove_many m ks) k.
Proof.
  intros. eapply map.map_ext. intro k'.
  rewrite ?map.get_remove_many_dec, ?map.get_remove_dec, ?map.get_remove_many_dec.
  destr (String.eqb k k'). 2: reflexivity. destr (List.find (eqb k') ks); reflexivity.
Qed.

Definition unset_many: list string -> cmd :=
  List.fold_right (fun v c => (cmd.seq (cmd.unset v) c)) cmd.skip.

  Lemma wp_unset_many0: forall fs t m vars l (post: trace -> mem -> locals -> Prop),
      post t m (map.remove_many l vars) ->
      wp_cmd fs (unset_many vars) t m l post.
  Proof.
    induction vars; intros.
    - eapply wp_skip. assumption.
    - eapply wp_unset. eapply IHvars. rewrite remove_many_remove_commute. assumption.
  Qed.

  Lemma wp_unset_many: forall vars fs t m l rest post,
      wp_cmd fs rest t m (map.remove_many l vars) post ->
      wp_cmd fs (cmd.seq (unset_many vars) rest) t m l post.
  Proof. intros. eapply wp_seq. eapply wp_unset_many0. assumption. Qed.

  Lemma wp_unset_many_after_if: forall vars (b: bool) fs t m l1 l2 l' l1' l2' rest post,
      map.remove_many l1 vars = l1' ->
      map.remove_many l2 vars = l2' ->
      (if b then l1' else l2') = l' ->
      wp_cmd fs rest t m l' post ->
      wp_cmd fs (cmd.seq (unset_many vars) rest) t m (if b then l1 else l2) post.
  Proof.
    intros. eapply wp_unset_many. subst. destruct b; assumption.
  Qed.

  lazymatch goal with
  | H: ?l = (if _ then map.of_list ?l1 else map.of_list ?l2) |- wp_cmd _ _ _ _ ?l _ =>
      let only_in_l1 := list_map_ignoring_failures ltac:(key_of_pair_if_not_in l2) l1 in
      let only_in_l2 := list_map_ignoring_failures ltac:(key_of_pair_if_not_in l1) l2 in
      subst l;
      eapply (wp_unset_many_after_if (List.app only_in_l1 only_in_l2))
  end.

Ltac normalize_locals_expr l :=
  let keys := eval lazy in (map.keys l) in
  let values := eval hnf in
    (match map.getmany_of_list l keys with
     | Some vs => vs
     | None => nil
     end) in
  let kvs := eval unfold List.combine in (List.combine keys values) in
  constr:(map.of_list kvs).

Ltac normalize_locals_wp :=
  lazymatch goal with
  | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
      let l' := normalize_locals_expr l in change (wp_cmd call c t m l' post)
  end.

Ltac normalize_locals_eq :=
  lazymatch goal with
  | |- ?l = ?r => let l' := normalize_locals_expr l in change (l' = r)
  end.

{ normalize_locals_eq. reflexivity. }
{ normalize_locals_eq. reflexivity. }
{
idtac.

repeat first [ rewrite push_if_into_cons_tuple_same_key
      | rewrite if_same
      | rewrite push_if_into_arg1
      | rewrite push_if_into_arg2 ].

reflexivity.
}
  letbind_locals 0%nat.

ltac2:(.**/ return b; /**).
repeat step.
ltac2:(.**/ } /**).
{ unfold fib. bottom_up_simpl_in_goal. reflexivity. }
{ replace i with n by ZnWords. reflexivity. }
Qed.

End LiveVerif. Comments .**/ //.
