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
    [> ] (* "(let n := numgoals in guard n = 1)" would not be executed if 0 goals *)
  end.

Definition protected(P: Prop) := P.

Ltac protect_equalities :=
  repeat match goal with
         | H: ?a = ?b |- _ => change (protected (a = b)) in H
         end.

Ltac unprotect_equalities :=
  repeat match goal with
         | H: protected (?a = ?b) |- _ => change (a = b) in H
         end.

Ltac invert_hyp H := protect_equalities; inversion H; clear H; subst; unprotect_equalities.

Ltac has_several_constructors T :=
  assert_succeeds (
    let dummy := fresh "dummy" in assert T as dummy;
    [|destruct dummy; [ idtac | idtac | .. ] ]).

Ltac unique_inversion :=
  match goal with
  | H: ?P |- _ =>
    (let h := head_of_app P in is_ind h);
    protect_equalities;
    lazymatch P with
    | ?LHS = ?RHS =>
      (* don't simpl if user didn't simpl *)
      let h1 := head_of_app LHS in is_constructor h1;
      let h2 := head_of_app RHS in is_constructor h2;
      inversion H; clear H
    | _ * _  => destruct H
    | _ /\ _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
    | exists y, _ => let yf := fresh y in destruct H as [yf H]
    | _ => (* By default, we don't want to destruct types with only one constructor
              (in particular, Class and Record are simpler if not destructed).
              The exceptions (ie types with only one constructor which we still want to
              destruct) are treated above). *)
           has_several_constructors P;
           inversion H; clear H
    end;
    [> (* require exactly one goal *)
     match goal with
     | H': ?P' |- _ => unify P P'; fail 1 (* inversion didn't do anything except simplifying *)
     | |- _ => idtac
     end;
     subst;
     unprotect_equalities]
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
