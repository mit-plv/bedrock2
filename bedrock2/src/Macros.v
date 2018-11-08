Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

Notation "'unique!' cls" := (ltac:(
  match constr:(Set) with
  | _ => let __ := constr:(_:cls) in fail 1 "unique!: already have an instance of" cls
  | _ => exact cls%type
  end))
  (at level 10, only parsing).
