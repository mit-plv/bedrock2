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

Ltac find_hyp_by_pat_TOO_SLOW_1 patfun :=
  let does_match t :=
    let _ := constr:(fun fff: False => ltac:(
        let b := beta1 patfun fff in
        let _ := matches t b in
        exact fff)) in
    idtac in
  match goal with
  | H1: context[?x1] |- _ =>
      does_match x1;
      tryif match goal with
            | H2: context[?x2] |- _ =>
                tryif constr_eq H1 H2 then fail
                else (does_match x2; fail 3 "non-unique pattern matches both" H1 "and" H2)
            end
      then fail 1000 "whoops, should already have failed earlier"
      else exact H1
  end.

Ltac multi_find_hyp_by_pat patfun :=
  multimatch goal with
  | H: context[?x] |- _ =>
      let _ := constr:(fun fff: False => ltac:(
        let b := beta1 patfun fff in
        let _ := matches x b in
        exact fff))
      in exact H
  end.

(* Note: imprecise error message "This tactic has more than one success", would be
   better to report "non-unique pattern matches both H1 and H2" *)
Ltac find_hyp_by_pat_TOO_SLOW_2 patfun := exactly_once (idtac; multi_find_hyp_by_pat patfun).

(* TODO can we raise an error if more than one hypothesis match, but without too
   much slowdown? *)
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
Notation "b" := (fun ff: False => b) (in custom pat at level 0, b constr at level 0).

Notation "# p" := ltac:(find_hyp_by_pat p)
  (at level 6, p custom pat at level 0, only parsing).

Goal forall a b: nat, a = 5 -> a < b -> a < 3 /\ 1 <= a -> a < 4 /\ b < 4 -> False.
  intros.
  pose proof #(?? < b) as AB.
  pose proof #(?? < b). (* this should fail with non-uniqueness error *)
  clear AB.
  eassert (_) as P by exact #(1 <= ??).
  clear P.
  pose proof #(a < ?? /\ ?? < 4).
  let HH := constr:(#(a < b)) in rewrite #(a = ??) in HH.
  let rew := (fun Heq Hwhere => rewrite Heq in Hwhere) in
  rew #(a = ??) #(1 <= ??).
Abort.
