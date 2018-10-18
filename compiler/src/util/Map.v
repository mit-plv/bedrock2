Require Import compiler.util.Set.
Require Import compiler.Decidable.

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;

  (* fundamental operation, all others are axiomatized in terms of this one *)
  get: map -> K -> option V;

  empty_map: map;
  empty_is_empty: forall (k: K), get empty_map k = None;

  remove: map -> K -> map;
  get_remove_same: forall m k, get (remove m k) k = None;
  get_remove_diff: forall m k1 k2, k1 <> k2 -> get (remove m k1) k2 = get m k2;

  put: map -> K -> V -> map;
  get_put_same: forall (m: map) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: map) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;

  restrict: map -> set K -> map;
  get_restrict_in: forall m k ks, k \in ks -> get (restrict m ks) k = get m k;
  get_restrict_notin: forall m k ks, ~ k \in ks -> get (restrict m ks) k = None;

  domain: map -> set K;
  domain_spec: forall m k, k \in (domain m) <-> exists v, get m k = Some v;

  range: map -> set V;
  range_spec: forall m v, v \in (range m) <-> exists k, get m k = Some v;

  reverse_get: map -> V -> option K;
  reverse_get_Some: forall m k v, reverse_get m v = Some k -> get m k = Some v;
  reverse_get_None: forall m v, reverse_get m v = None -> forall k, get m k <> Some v;

  intersect_map: map -> map -> map;
  intersect_map_spec: forall k v m1 m2,
      get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v;

  remove_keys: map -> set K -> map;
  remove_keys_never_there: forall m k ks,
      get m k = None ->
      get (remove_keys m ks) k = None;
  remove_keys_removed: forall m k v ks,
      get m k = Some v ->
      k \in ks ->
      get (remove_keys m ks) k = None;
  remove_keys_not_removed: forall m k v ks,
      get m k = Some v ->
      ~ k \in ks ->
      get (remove_keys m ks) k = Some v;

  remove_by_value: map -> V -> map;
  remove_by_value_same: forall k v m,
      get m k = Some v -> get (remove_by_value m v) k = None;
  remove_by_value_diff: forall k v m,
      get m k <> Some v -> get (remove_by_value m v) k = get m k;

  remove_values: map -> set V -> map;
  remove_values_never_there: forall m k vs,
      get m k = None ->
      get (remove_values m vs) k = None;
  remove_values_removed: forall m k v vs,
      get m k = Some v ->
      v \in vs ->
      get (remove_values m vs) k = None;
  remove_values_not_removed: forall m k v vs,
      get m k = Some v ->
      ~ v \in vs ->
      get (remove_values m vs) k = Some v;

  update_map: map -> map -> map;
  get_update_map_l: forall m1 m2 k,
      get m2 k = None ->
      get (update_map m1 m2) k = get m1 k;
  get_update_map_r: forall m1 m2 k v,
      get m2 k = Some v ->
      get (update_map m1 m2) k = Some v;

}.

Arguments map _ _ {_}.
