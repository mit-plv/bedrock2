Module map.
  Class map {key value : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> key -> option value;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    union : rep -> rep -> rep; (* rightmost takes priority *)
  }.
  Arguments map : clear implicits.

  Class ok {key value} (map : map key value) := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_remove_same : forall m k, get (remove m k) k = None;
    get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
    get_union_left : forall m1 m2 k, get m2 k = None -> get (union m1 m2) k = get m1 k;
    get_union_right : forall m1 m2 k v, get m2 k = Some v -> get (union m1 m2) k = Some v;
  }.

  Section ListOperations.
    Context {key value} {map : map key value}.
    Fixpoint putmany (keys : list key) (values : list value) (m : rep) {struct keys} : option rep :=
      match keys, values with
      | nil, nil => Some m
      | cons b binders, cons v values =>
        putmany binders values (put m b v)
      | _, _ => None
      end.
  End ListOperations.

  Section Decomp.
    Context {key value} {map : map key value}.
    Definition disjoint (a b : rep) : Prop :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition split m m1 m2 : Prop :=
      m = (union m1 m2) /\ disjoint m1 m2.
  End Decomp.
End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.
