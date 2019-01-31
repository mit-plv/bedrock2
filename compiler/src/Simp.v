Require Import Coq.ZArith.ZArith.

Ltac head_of_app e :=
  match e with
  | ?f ?a => head_of_app f
  | _ => e
  end.

Ltac destruct_unique_match :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
    match goal with
    | |- _ => is_var e; destruct e
    | |- _ => let N := fresh "E" in destruct e eqn: N
    end;
    try (exfalso; (contradiction || discriminate || congruence));
    let n := numgoals in guard n <= 1
  end.

Ltac unique_inversion :=
  match goal with
  | H: ?P |- _ =>
    (let h := head_of_app P in is_constructor h || constr_eq h @eq);
    inversion H;
    (let n := numgoals in guard n <= 1);
    subst;
    clear H;
    match goal with
    | H': ?P' |- _ => unify P P'; fail 1 (* inversion didn't do anything except simplifying *)
    | |- _ => idtac
    end
  end.

Ltac simpl_Z_eqb :=
  match goal with
  | H: _ =? _ = true  |- _ => apply Z.eqb_eq in H; subst
  | H: _ =? _ = false |- _ => apply Z.eqb_neq in H
  end.

Ltac simp_step :=
  destruct_unique_match
  || unique_inversion
  || simpl_Z_eqb.

Ltac simp := repeat simp_step.
