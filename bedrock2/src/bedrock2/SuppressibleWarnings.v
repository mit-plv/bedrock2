Declare Scope message_scope.
Definition warning_marker{T: Type}(msg: T) := msg.
Arguments warning_marker {T} msg%message_scope.

(* Call this tactic to obtain a pattern-matchable representation of the warning *)
Ltac unexplain := unfold warning_marker in *.

Notation "x" := (warning_marker x) (at level 100, only printing).

(* Convention: All warnings whose type can be proved by `eauto with suppressed_warnings`
   will be suppressed.
   This has the nice side effect that warnings which already appear in the context
   will not be posed again. *)
Create HintDb suppressed_warnings.

Ltac pose_warning w :=
  let t := type of w in
  tryif (let __ := constr:(ltac:(eauto with suppressed_warnings): t) in idtac)
  then idtac (*suppressed*)
  else let name := fresh "Warning" in pose proof (w : warning_marker t) as name.

Ltac continue_if_warning := idtac.
Ltac stop_if_warning :=
  lazymatch goal with
  | _: warning_marker _ |- _ =>
      fail "There's a warning to be fixed or suppressed before you can continue"
        "(or use" "'Ltac check_for_warnings_hook ::= continue_if_warning.'"
        "to continue anyways)"
  | |- _ => idtac
  end.

Ltac check_for_warnings_hook := stop_if_warning.

Module Examples.
  Inductive no_frobnicator_found(terms: list nat)(T: Type)(x: T): Set :=
    mk_sample_no_frobnicator_found.

  Notation "'At' 'least' 'one' 'of' 'the' 'terms' t1 , .. , tn 'should' 'have' 'a' 'frobnicator' 'that' 'works' 'under' x 'of' 'type' T" :=
  (no_frobnicator_found (cons t1 .. (cons tn nil) ..) T x)
  (at level 1, t1 at level 0, tn at level 0, only printing)
  : message_scope.

  Ltac sample_tac b :=
    lazymatch goal with
    | |- ?n = _ =>
        pose_warning (mk_sample_no_frobnicator_found
                        (cons (1 + 1) (cons (4 - 2) nil)) (nat * bool) (n, b))
    end.

  Goal exists (n: nat), n = n.
    eexists.
    sample_tac true. (* displays a warning *)
    assert_fails (idtac; check_for_warnings_hook).
    sample_tac true. (* doesn't duplicate the same warning *)
    unexplain. (* displays the warning in a pattern-matchable way *)

    (* Example: Let's say it's ok if a true-pair frobnicator can't be found: *)
    Local Hint Extern 1 (no_frobnicator_found _ (_ * _) (_, true)) =>
      constructor : suppressed_warnings.

    clear Warning.

    sample_tac true. (* no warning any more *)
    check_for_warnings_hook.
    sample_tac false. (* but this one is still shown *)
    assert_fails (idtac; check_for_warnings_hook).
  Abort.
End Examples.
