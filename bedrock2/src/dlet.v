Definition dlet {A P} (x : A) (f : forall a : A, P a) : P x
  := let y := x in f y.
Notation "'dlet!' x .. y := v 'in' f" :=
  (dlet v (fun x => .. (fun y => f) .. ))
    (at level 200, x binder, y binder, f at level 200,
     format "'dlet!'  x .. y  :=  v  'in' '//' f").