Ltac rdelta x :=
  match constr:(Set) with
  | _ => let x := eval unfold x in x in x
  | _ => x
  end.
