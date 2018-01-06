Require Export Coq.omega.Omega.

Ltac unfold_Z_or_nat a := let t := type of a in first [unify t nat | unify t Z]; unfold a in *.

Ltac Omega :=
  repeat match goal with
  | _: context [?a] |- _ => unfold_Z_or_nat a
  | |- context [?a]      => unfold_Z_or_nat a
  end;
  omega.
