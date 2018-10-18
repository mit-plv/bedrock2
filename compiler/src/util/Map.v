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

Existing Instance map_domain_set.
Existing Instance map_range_set.

Section MapDefinitions.

  Context {K V: Type}.
  Context {KVmap: MapFunctions K V}.

  Definition extends(s1 s2: map K V) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition only_differ(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs \/ get s1 x = get s2 x.

  Definition agree_on(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs -> get s1 x = get s2 x.

  Definition undef_on(s: map K V)(vs: set K) := forall x, x \in vs -> get s x = None.

  Lemma get_put: forall (s: map K V) (x y: K) (v: V),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof.
    intros. destruct (dec (x = y)).
    - subst. rewrite get_put_same. reflexivity.
    - rewrite get_put_diff by assumption. reflexivity.
  Qed.

  Lemma get_remove: forall (m: map K V) (x y: K),
    get (remove m x) y = if dec (x = y) then None else get m y.
  Proof.
    intros. destruct (dec (x = y)).
    - subst. rewrite get_remove_same. reflexivity.
    - rewrite get_remove_diff by assumption. reflexivity.
  Qed.

  Lemma get_restrict: forall m k ks,
      get (restrict m ks) k = if dec (k \in ks) then get m k else None.
  Proof.
    intros. destruct (dec (k \in ks)).
    - subst. rewrite get_restrict_in; auto.
    - rewrite get_restrict_notin by assumption. reflexivity.
  Qed.

  Lemma get_intersect_map: forall k m1 m2,
      get (intersect_map m1 m2) k =
      match get m1 k, get m2 k with
      | Some v1, Some v2 => if dec (v1 = v2) then Some v1 else None
      | _, _ => None
      end.
  Proof.
    intros.
    destruct (get (intersect_map m1 m2) k) eqn: E.
    - apply intersect_map_spec in E. destruct E as [E1 E2].
      rewrite E1. rewrite E2. destruct (dec (v = v)); congruence.
    - destruct (get m1 k) eqn: E1; destruct (get m2 k) eqn: E2; auto.
      destruct (dec (v = v0)); auto.
      subst v0.
      pose proof (intersect_map_spec k v m1 m2) as P.
      firstorder congruence.
  Qed.

  Lemma get_remove_keys: forall m k ks,
      get (remove_keys m ks) k =
      match get m k with
      | Some v => if dec (k \in ks) then None else Some v
      | None => None
      end.
  Proof.
    intros.
    destruct (get m k) eqn: E.
    - destruct (dec (k \in ks)).
      + eauto using remove_keys_removed.
      + eauto using remove_keys_not_removed.
    - eauto using remove_keys_never_there.
  Qed.

  Lemma get_remove_by_value: forall m k v,
      get (remove_by_value m v) k =
      if dec (get m k = Some v) then None else get m k.
  Proof.
    intros. destruct (dec (get m k = Some v)).
    - eauto using remove_by_value_same.
    - eauto using remove_by_value_diff.
  Qed.

  Lemma get_remove_values: forall m k vs,
      get (remove_values m vs) k =
      match get m k with
      | Some v => if dec (v \in vs) then None else Some v
      | None => None
      end.
  Proof.
    (*
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
*)
  Abort.


End MapDefinitions.

Hint Unfold extends only_differ agree_on undef_on : unf_map_defs.

Hint Rewrite
     @get_remove
     @get_put


     @domain_spec
     @range_spec

  (* TODO operations without a rewrite lemma here:
     - reverse_get
  *).