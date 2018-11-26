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