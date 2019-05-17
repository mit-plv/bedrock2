Local Set Universe Polymorphism.
Section WithT.
  Context {T : Type}.
  Implicit Types x : T.
  Definition intro x := x.
  Definition split x := x.
  Definition esplit x := x.
  Definition econstructor x := x.
  Definition exact_eq_refl x := x.
  Definition exfalso x := x.

  Definition unique x := x.
  Definition left x := x.
  Definition right x := x.
End WithT.

Module Notations.
  (* Declare Scope hide_markers. *) (* COMPAT(coq-v8.8) *)
  Notation "x" := (intro x) (only printing, at level 3) : hide_markers.
  Notation "x" := (split x) (only printing, at level 3) : hide_markers.
  Notation "x" := (esplit x) (only printing, at level 3) : hide_markers.
  Notation "x" := (econstructor x) (only printing, at level 3) : hide_markers.
  Notation "x" := (exfalso x) (only printing, at level 3) : hide_markers.

  Notation "x" := (unique x) (only printing, at level 3) : hide_markers.
  Notation "x" := (left x) (only printing, at level 3) : hide_markers.
  Notation "x" := (right x) (only printing, at level 3) : hide_markers.
End Notations.

Module hide.
  Export Notations.
  Global Open Scope hide_markers.
End hide.
