(* Provides the notation `find! p`, which finds a hypothesis containing pattern p,
   where p has to use ?? instead of underscore or named question mark variables like ?x. *)

Require Import coqutil.Macros.subst.

Ltac matches t p :=
  lazymatch p with
  | t => constr:(tt)
  | match _ with end => constr:(tt)
  | ?Ap ?Bp =>
      lazymatch t with
      | ?At ?Bt =>
          let _ := matches At Ap in
          let _ := matches Bt Bp in
          constr:(tt)
      end
  | ?Ap -> ?Bp =>
      lazymatch t with
      | ?At -> ?Bt =>
          let _ := matches At Ap in
          let _ := matches Bt Bp in
          constr:(tt)
      end
  end.

Ltac beta1 func arg :=
  lazymatch func with
  | (fun a => ?f) => constr:(subst! arg for a in f)
  end.

Ltac find_hyp_by_pat patfun :=
  match goal with
  | H: context[?x] |- _ =>
      let _ := constr:(fun fff: False => ltac:(
        let b := beta1 patfun fff in
        let _ := matches x b in
        exact fff))
      in exact H
  end.

Notation "??" := ltac:(match goal with ff: False |- _ => case ff end) (only parsing).

Declare Custom Entry pat.
Notation "b" := (fun ff: False => b) (in custom pat at level 0, b constr at level 200).

Notation "'find!' p" := ltac:(find_hyp_by_pat p)
  (at level 10, p custom pat at level 0, only parsing).

Goal forall a b: nat, a = 5 -> a < b -> a < 3 /\ 1 <= a -> a < 4 /\ b < 4 -> False.
  intros.
  pose proof (find! (?? < b)).
  eassert (_) by exact (find! (1 <= ??)).
  pose proof (find! (a < ?? /\ ?? < 4)).
  let HH := constr:(find! (a < b)) in rewrite (find! (a = ??)) in HH.
  let rew := (fun Heq Hwhere => rewrite Heq in Hwhere) in
  rew (find! (a = ??)) (find! (1 <= ??)).
Abort.
