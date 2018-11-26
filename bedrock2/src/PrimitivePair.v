Module pair.
  Local Set Universe Polymorphism.
  Local Set Primitive Projections.
  Record pair {A B} := mk { _1 : A; _2 : B _1 }.
  Arguments pair : clear implicits.
  Arguments mk {A B} _ _.

  (* TODO: make * right-associative like /\ *)
  Notation "A * B" := (pair A%type (fun _ => B%type)) : type_scope.

  Notation "{ x  &  P }" := (pair _ (fun x => P)) : type_scope.
  Notation "{ ' pat  &  P }" := (pair _ (fun pat => P)) : type_scope.

  Notation "{ x : A  &  P }" := (pair A (fun x => P)) : type_scope.
  Notation "{ ' pat : A  &  P }" := (pair A (fun pat => P)) : type_scope. 

  Notation "( x , y , .. , z )" := (mk .. (mk x y) .. z) : core_scope.

  Notation "x '.(1)'" := (_1 x) (at level 1, left associativity) : core_scope.
  Notation "x '.(2)'" := (_2 x) (at level 1, left associativity) : core_scope.
End pair. Notation pair := pair.pair.
