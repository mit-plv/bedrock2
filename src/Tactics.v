Require Import lib.fiat_crypto_tactics.Not.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
      is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ] =>
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[if ?e then _ else _] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[match ?e with _ => _ end] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  | H: context[if ?e then _ else _] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac inversionss :=
  repeat match goal with
  | H: ?a = ?b |- _ => inversion H; subst; clear H;
                       match goal with
                       | H': a = b |- _ => fail 1
                       | _ => idtac
                       end
  end.

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac destruct_pair_eqs := repeatplus match goal with
  | H: (_, _) = (_, _) |- _ => inversion H; clear H
  end.

Ltac ensure_new H :=
  let t := type of H in
  not (clear H; match goal with
                | A: t |- _ => idtac
                end).

