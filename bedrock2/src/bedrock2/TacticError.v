(* Almost everyone importing this file will need strings in their error messages *)
Require Import Coq.Strings.String. Open Scope string_scope.

(* TODO The definition of dlist could/should be shared with compiler.util.Result *)
Inductive dlist: Type :=
| dnil
| dcons{T: Type}(head: T)(tail: dlist).

Declare Custom Entry ne_space_sep_dlist.
Notation "x" := (dcons x dnil)
  (in custom ne_space_sep_dlist at level 0, x constr at level 0).
Notation "h t" := (dcons h t)
  (in custom ne_space_sep_dlist at level 0,
   h constr at level 0, t custom ne_space_sep_dlist at level 0).

Inductive tactic_error(msg: dlist): Prop := mk_tactic_error.

Declare Scope tactic_error_scope.
Open Scope tactic_error_scope.

(* Don't do this because even though it's only printing, it will conflict with
   other "x" notations that use a different custom entry or constr for x
Notation "x" := (tactic_error x)
  (at level 0, x custom ne_space_sep_dlist at level 0, only printing)
: tactic_error_scope. *)

Notation "x !" := (tactic_error x)
  (at level 0, x custom ne_space_sep_dlist at level 0, format "'[' x  ! ']'", only printing)
: tactic_error_scope.

Notation "'Error:(' msg )" := (mk_tactic_error msg)
  (at level 0, msg custom ne_space_sep_dlist at level 0, format "'Error:(' msg )")
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
Abort.

Ltac assert_no_error :=
  lazymatch goal with
  | _: tactic_error _ |- _ => fail "You need to fix the error before continuing"
  | |- _ => idtac
  end.
