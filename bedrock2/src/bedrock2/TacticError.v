Require Import Coq.Strings.String.
(* Almost everyone importing this file will need strings in their error messages *)
Export Coq.Strings.String.StringSyntax.
Require Import coqutil.Datatypes.dlist.

Declare Custom Entry ne_space_sep_dlist.
Notation "x" := (dcons x dnil)
  (in custom ne_space_sep_dlist at level 0, x constr at level 0).
Notation "h t" := (dcons h t)
  (in custom ne_space_sep_dlist at level 0,
   h constr at level 0, t custom ne_space_sep_dlist at level 0).

(* Intended to be used with (pose proof (mk_tactic_error msg)), so that it
   displays "ErrorHypName: msg", so the error needs to appear in the type *)
Inductive tactic_error(msg: dlist): Prop := mk_tactic_error.

(* Intended to be printed with idtac, so we only need term-level notations *)
Inductive tactic_info := mk_tactic_info(msg: dlist).

Declare Scope tactic_error_scope.
Open Scope tactic_error_scope.

(* Don't do this because even though it's only printing, it will conflict with
   other "x" notations that use a different custom entry or constr for x
Notation "x" := (tactic_error x)
  (at level 0, x custom ne_space_sep_dlist at level 0, only printing)
: tactic_error_scope. *)

Notation "x !" := (tactic_error x%string)
  (at level 0, x custom ne_space_sep_dlist at level 0, format "'[' x  ! ']'", only printing)
: tactic_error_scope.

Notation "'Error:(' msg )" := (mk_tactic_error msg%string)
  (at level 0, msg custom ne_space_sep_dlist at level 0, format "'Error:(' msg )")
  : tactic_error_scope.

Notation "'Info:(' msg )" := (mk_tactic_info msg%string)
  (at level 0, msg custom ne_space_sep_dlist at level 0, only parsing)
  : tactic_error_scope.

Notation "'Info:' msg" := (mk_tactic_info msg%string)
  (at level 0, msg custom ne_space_sep_dlist at level 0, format "'Info:'  msg",
   only printing)
  : tactic_error_scope.

Ltac pose_err_silent e := let n := fresh "Error" in pose proof e as n.

Ltac pose_err e :=
  let n := fresh "Error" in
  pose proof e as n;
  let T := type of n in
  idtac "Error:" T.

Goal False.
  pose_err_silent Error:("Here's a very long error message that will take more than one line to display and I wonder how it will be rendered").
  pose_err_silent Error:("Here's a very long" (cons "really long" (cons "error message that" (cons "will take mooooooooooooooooooore than one line" nil))) "to display and I wonder how it will be rendered").
  pose_err_silent Error:(4 "is not a" bool).
  pose_err_silent Error:("just one string").
  pose Info:("Test" 1 "info message").
  let r := constr:(Info:("one string")) in idtac (*r*).
Abort.

(* Alternative way of optionally printing info messages with nicer output
   but less nice usage: *)

Ltac run_logger_thunk f := f tt.
Ltac ignore_logger_thunk f := idtac.

Ltac sample_tactic logger :=
  lazymatch goal with
  | va: nat, vb: nat |- _ =>
      logger ltac:(fun _ => idtac "Going to clear" va "and" vb);
      clear va vb
  end.

Goal forall a b: nat, True.
  intros.
  (* sample_tactic run_logger_thunk. *)
  sample_tactic ignore_logger_thunk.
Abort.

Ltac assert_no_error :=
  lazymatch goal with
  | _: tactic_error _ |- _ => fail "You need to fix the error before continuing"
  | |- _ => idtac
  end.

Ltac test_error e :=
  let expected := type of e in
  lazymatch goal with
  | H: tactic_error ?l |- _ => unify (tactic_error l) expected
  end.
