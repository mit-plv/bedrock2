Require Import compiler.util.Set.
Require Import compiler.Decidable.

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;

  empty_map: map;
  get: map -> K -> option V;
  put: map -> K -> V -> map;
  restrict: map -> set K -> map;
  domain: map -> set K;
  range: map -> set V;

  reverse_get: map -> V -> option K;
  intersect_map: map -> map -> map;
  remove_by_value: map -> V -> map;
  remove_values: map -> set V -> map;
  update_map: map -> map -> map; (* rhs overrides lhs *)

  get_put_same: forall (m: map) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: map) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;
  empty_is_empty: forall (k: K), get empty_map k = None

  (* TODO probably needs some more properties *)
}.

Arguments map _ _ {_}.
