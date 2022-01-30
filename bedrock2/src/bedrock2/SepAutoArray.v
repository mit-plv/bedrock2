Require Import bedrock2.SepAuto.
Require Import bedrock2.Array.

Section SepLog32. (* TODO try to generalize to any width without breaking automation *)
  Context {word: word.word 32} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition word_array(vs: list word)(addr: word): mem -> Prop :=
    array Scalars.scalar (word.of_Z 4) addr vs.

  Lemma access_scalar_in_word_array: forall a a',
      word.unsigned (word.sub a' a) mod 4 = 0 ->
      split_sepclause a word_array a' scalar
        (let i := Z.to_nat (word.unsigned (word.sub a' a) / 4) in
         forall vs vs1 v vs2,
           (* connected with /\ because it needs to be solved by considering both at once *)
           vs = vs1 ++ [v] ++ vs2 /\ List.length vs1 = i ->
           iff1 (seps [a |-> word_array vs1;
                       a' |-> scalar v;
                       word.add a (word.of_Z (4 * Z.of_nat (S i))) |-> word_array vs2])
                (a |-> word_array vs)).
  Proof.
    unfold split_sepclause.
    unfold word_array, scalar, truncated_word, Scalars.scalar, at_addr, seps.
    intros. destruct H0. subst vs.
    cbn [List.app].
    symmetry.
    etransitivity.
    1: eapply array_append.
    cbn [array].
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. ZnWords.
    }
    reflexivity.
  Qed.
End SepLog32.

Section WithA.
  Context {A: Type}.

  Lemma list_expose_nth{inhA: inhabited A}: forall (vs: list A) i,
      (i < List.length vs)%nat ->
      vs = List.firstn i vs ++ [List.nth i vs default] ++ List.skipn (S i) vs /\
        List.length (List.firstn i vs) = i.
  Proof.
    intros. rewrite List.firstn_nth_skipn by assumption.
    rewrite List.firstn_length_le by Lia.lia. auto.
  Qed.
End WithA.

Ltac destruct_bool_vars :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             is_var b; let t := type of b in constr_eq t bool; destruct b
         end.

(* Three hints in three different DBs indicating how to find the rewrite lemma,
   how to solve its sideconditions for the split direction, and how to solve its
   sideconditions for the merge direction: *)

#[export] Hint Extern 1 (split_sepclause _ word_array _ scalar _) =>
  eapply access_scalar_in_word_array; destruct_bool_vars; ZnWords
: split_sepclause_goal.

#[export] Hint Extern 1 (_ = ?l ++ [_] ++ _ /\ List.length ?l = _) =>
  eapply list_expose_nth; destruct_bool_vars; ZnWords
: split_sepclause_sidecond.

#[export] Hint Extern 1 (@eq (list _) ?listL ?listR /\ @eq nat ?lenL ?lenR) =>
  assert_fails (has_evar lenL);
  assert_fails (has_evar lenR);
  is_evar listL; split; [reflexivity|destruct_bool_vars; ZnWords]
: merge_sepclause_sidecond.


(* Hints to simplify/cleanup the expressions that were created by repeated
   splitting and merging of sep clauses: *)
#[export] Hint Rewrite
  List.firstn_all2
  List.skipn_all2
  List.firstn_eq_O
  List.skipn_eq_O
  Nat.min_l
  Nat.min_r
using ZnWords : fwd_rewrites.
