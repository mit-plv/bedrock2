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
    [|case dummy; [ idtac | idtac | .. ] ]).

(* Given a hypothesis H, returns the induction principle for it *)
Ltac get_ind_principle H :=
  let T := type of H in
  let r := constr:(ltac:(induction H; intros; exact I) : T -> True) in
  head_of_app r.

(* Checks if all indices of term t are vars.
   ip should be the induction principle for the type of t, which we use
   to check whether an argument in t is a parameter (then ip can be specialized with it)
   or an index (then it cannot).
   Returns the partially specialized ip if we're still processing parameters, tt if we're
   processing indices and all of them so far were variables, or fails if any non-var indices
   have been encountered. *)
Ltac all_indices_are_vars ip t :=
  lazymatch t with
  | ?f ?a => lazymatch all_indices_are_vars ip f with
             | tt => let __ := lazymatch constr:(Set) with _ => is_var a end in constr:(tt)
             | ?ip' =>
               match constr:(Set) with
               | _ => constr:(ip' a)
               | _ => let __ := lazymatch constr:(Set) with _ => is_var a end in constr:(tt)
               end
             end
  | ?c => let __ := lazymatch constr:(Set) with _ => is_ind c end in constr:(ip)
  end.

(* Checks if the type of hypothesis H is of the form
   "Ind p1 p2 ... pn i1 i2 ... im",
   where Ind is an inductive type (as in, "is_ind Ind" succeeds),
   p1 p2 ... pn are parameters of the inductive and are allowed to have any shape, while
   i1 i2 ... im are indices of the inductive and must be a variable.
   If this test succeeds and Ind has more than one constructor, then we know that
   "inversion H" will generate more than one subgoal. *)
Ltac all_indices_of_hyp_are_var H :=
  let ip := get_ind_principle H in
  let t := type of H in
  match all_indices_are_vars ip t with
  | ?res => idtac (* ignore res as long as it's not a failure *)
  end.

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
           tryif all_indices_of_hyp_are_var H then (
               (* idtac "no need to invert" P; *)
               fail "will definitely get more than one subgoal"
           ) else (
               (* idtac "gonna invert" P; *)
               inversion H; clear H
           )
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
