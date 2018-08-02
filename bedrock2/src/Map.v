Module map.
  Class map {K V : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> K -> option V;
    put : rep -> K -> V -> rep;
  }.
  Arguments map : clear implicits.

  Section ListOperations.
    Context {K V} {map : map K V}.
    Fixpoint putmany (keys : list K) (values : list V) (m : rep) {struct keys} : option rep :=
      match keys, values with
      | nil, nil => Some m
      | cons b binders, cons v values =>
        match putmany binders values m with
        | Some m => Some (put m b v)
        | None => None
        end
      | _, _ => None
      end.
  End ListOperations.

End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.