Require Import lib.fiat_crypto_tactics.Not.
Require Import compiler.util.Set.
Require Import compiler.util.Tactics.
Require Import compiler.Decidable.

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;

  (* fundamental operation, all others are axiomatized in terms of this one *)
  get: map -> K -> option V;

  empty_map: map;
  empty_is_empty: forall (k: K), get empty_map k = None;

  remove_key: map -> K -> map;
  get_remove_same: forall m k, get (remove_key m k) k = None;
  get_remove_diff: forall m k1 k2, k1 <> k2 -> get (remove_key m k1) k2 = get m k2;

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


Hint Resolve
  empty_is_empty
  get_remove_same
  get_remove_diff
  get_put_same
  get_put_diff
  get_restrict_in
  get_restrict_notin
  domain_spec
  range_spec
  reverse_get_Some
  reverse_get_None
  intersect_map_spec
  remove_keys_never_there
  remove_keys_removed
  remove_keys_not_removed
  remove_by_value_same
  remove_by_value_diff
  remove_values_never_there
  remove_values_removed
  remove_values_not_removed
  get_update_map_l
  get_update_map_r
: map_spec_hints_separate.


Section MapDefinitions.

  Context {K V: Type}.
  Context {KVmap: MapFunctions K V}.

  (* Note: not reusing set_elem_eq_dec, map_domain_set and map_range_set here,
     because we want the client of these lemmas to be able to choose the instance *)
  Context {keq: DecidableEq K}.
  (* Context {veq: DecidableEq V}. *)
  Context {Kset: SetFunctions K}.
  Context {Vset: SetFunctions V}.

  (* however, "rewrite get_intersect_map" (and probably others) won't pick up a veq typeclass
     in scope, and the rewrite will fail, so we prefer to hardcode an instance derived from
     KVMap: *)
  Local Instance veq: DecidableEq V := @set_elem_eq_dec V map_range_set.

  Definition extends(s1 s2: map K V) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition bw_extends(s1 s2: map K V) := forall k v,
      reverse_get s2 v = Some k -> reverse_get s1 v = Some k.

  Definition only_differ(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs \/ get s1 x = get s2 x.

  Definition agree_on(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs -> get s1 x = get s2 x.

  Definition undef_on(s: map K V)(vs: set K) := forall x, x \in vs -> get s x = None.

  Ltac prover :=
    intros;
    repeat match goal with
    | |- context[match ?d with _ => _ end] =>
      match type of d with
      | {_} + {_} => destruct d
      | _ => let E := fresh "E" in destruct d eqn: E
      end
    end;
    subst;
    eauto with map_spec_hints_separate.

  Lemma get_empty: forall (k: K),
      get empty_map k = None.
  Proof. prover. Qed.

  Lemma get_remove_key: forall (m: map K V) (x y: K),
    get (remove_key m x) y = if dec (x = y) then None else get m y.
  Proof. prover. Qed.

  Lemma get_put: forall (s: map K V) (x y: K) (v: V),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof. prover. Qed.

  Lemma get_restrict: forall m k ks,
      get (restrict m ks) k = if dec (k \in ks) then get m k else None.
  Proof. prover. Qed.

  Lemma get_intersect_map: forall k m1 m2,
      get (intersect_map m1 m2) k =
      match get m1 k, get m2 k with
      | Some v1, Some v2 => if dec (v1 = v2) then Some v1 else None
      | _, _ => None
      end.
  Proof.
    clear keq. (* The proof term does not contain keq it even if we keep it, but after closing
      the section, it's added as a section var. And with "Proof using .", it seems it's used
      when attempting to Qed. Why?? *)
    (* Challenge: what's the minimal change to "prover" needed to make it work here too? *)
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
  Proof. prover. Qed.

  Lemma get_remove_by_value: forall m k v,
      get (remove_by_value m v) k =
      if dec (get m k = Some v) then None else get m k.
  Proof. prover. Qed.

  Lemma get_remove_values: forall m k vs,
      get (remove_values m vs) k =
      match get m k with
      | Some v => if dec (v \in vs) then None else Some v
      | None => None
      end.
  Proof. prover. Qed.

  Lemma get_update_map: forall m1 m2 k,
      get (update_map m1 m2) k =
      match get m2 k with
      | Some v => Some v
      | None => get m1 k
      end.
  Proof. prover. Qed.

End MapDefinitions.

Hint Unfold extends bw_extends only_differ agree_on undef_on : unf_map_defs.

Ltac rew_set_op_map_specs H :=
  let t lemma := rewrite lemma in H in
      repeat match type of H with
             (* rew_map_specs *)
             | context[get ?m] =>
                 lazymatch m with
                 | remove_key _ _ => t (get_remove_key (keq := _))
                 | put _ _ => t get_put
                 | restrict _ _ => t get_restrict
                 | intersect_map _ _ => t get_intersect_map
                 | remove_keys _ _ => t get_remove_keys
                 | remove_by_value _ _ => t get_remove_by_value
                 | remove_values _ _ => t get_remove_values
                 | update_map _ _ => t get_update_map
                 end
             | context[_ \in domain _] => t domain_spec
             | context[_ \in range _] => t range_spec

             (* rew_set_op_specs *)
             | context[_ \in empty_set] => t empty_set_spec
             | context[_ \in singleton_set _] => t singleton_set_spec
             | context[_ \in union _ _] => t union_spec
             | context[_ \in intersect _ _] => t intersect_spec
             | context[_ \in diff _ _] => t diff_spec
             end.

Hint Rewrite
     @get_empty
     @get_remove_key
     @get_put
     @get_restrict
     @get_intersect_map
     @get_remove_keys
     @get_remove_by_value
     @get_remove_values
     @get_update_map
     @domain_spec
     @range_spec
     (* Note: reverse_get doesn't have a one-lemma spec, so map_solver will not
        automatically figure out that it should destruct this option *)
     (*@reverse_get_Some <-- will not replace reverse_get *)
     (*@reverse_get_None <-- not usable for rewrite *)
  : rew_map_specs.


Ltac rewrite_get_put K V :=
  first [ let keq := constr:(_: DecidableEq K) in (* <-- fails if no typeclass found *)
          rewrite? (@get_put K V _ keq) in *      (* <-- never fails because of "?" *)
        | fail 10000 "Could not find DecidableEq for" K ].

Ltac canonicalize_map_hyp H :=
  rew_set_op_map_specs H;
  try exists_to_forall H;
  try specialize (H eq_refl).

Ltac canonicalize_all K V :=
  repeat match goal with
         | H: _ |- _ => progress canonicalize_map_hyp H
         end;
  invert_Some_eq_Some;
  repeat (autorewrite with rew_set_op_specs rew_map_specs || rewrite_get_put K V).

Ltac map_solver_should_destruct K V d :=
  let T := type of d in
  first [ unify T (option K)
        | unify T (option V)
        | match T with
          | {?x \in ?A} + {~ ?x \in ?A} => idtac
          | {?x1 = ?x2} + {?x1 <> ?x2} =>
            let T' := type of x1 in
            first [ unify T' K
                  | unify T' V
                  | unify T' (option K)
                  | unify T' (option V) ]
          end ].

Ltac destruct_one_map_match K V :=
  destruct_one_match_hyporgoal_test ltac:(map_solver_should_destruct K V) ltac:(fun H => rew_set_op_map_specs H).

Ltac propositional :=
  repeat match goal with
         | |- forall _, _ => progress intros until 0
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         | [ H: _ /\ _ |- _ ] =>
           let H1 := fresh H "_l" in
           let H2 := fresh H "_r" in
           destruct H as [H1 H2]
         | [ H: _ <-> _ |- _ ] =>
           let H1 := fresh H "_fwd" in
           let H2 := fresh H "_bwd" in
           destruct H as [H1 H2]
         | [ H: False |- _ ] => solve [ destruct H ]
         | [ H: True |- _ ] => clear H
         | [ H: exists (varname : _), _ |- _ ] =>
           let newvar := fresh varname in
           destruct H as [newvar H]
         | [ H: ?P |- ?P ] => exact H
         | |- _ /\ _ => split
         | [ H: ?P -> _, H': ?P |- _ ] =>
           match type of P with
           | Prop => specialize (H H')
           end
         | |- _ => progress subst *
         end.

Ltac propositional_ors :=
  repeat match goal with
         | [ H: _ \/ _ |- _ ] => destruct H as [H | H]
         | [ |- _ \/ _ ] => (left + right); congruence
         end.

Ltac ensure_no_body H := not (clearbody H).

Ltac pick_one_existential :=
  multimatch goal with
  | x: ?T |- exists (_: ?T), _ => exists x
  end.

Ltac map_solver K V :=
  assert_is_type K;
  assert_is_type V;
  repeat autounfold with unf_map_defs unf_set_defs in *;
  destruct_products;
  repeat match goal with
         | |- forall _, _ => progress intros until 0
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         end;
  canonicalize_all K V;
  let RGN := fresh "RGN" in pose proof (@reverse_get_None K V _) as RGN;
  let RGS := fresh "RGS" in pose proof (@reverse_get_Some K V _) as RGS;
  repeat match goal with
  | H: forall (x: ?E), _, y: ?E |- _ =>
    first [ unify E K | unify E V ];
    ensure_no_body H;
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in
           pose proof (H y) as H';
           canonicalize_map_hyp H';
           ensure_new H'
    end
  | H: forall (x: _), _, y: ?E |- _ =>
    let T := type of E in unify T Prop;
    ensure_no_body H;
    let H' := fresh H y in
    pose proof H as H';
    specialize H' with (1 := y); (* might instantiate a few universally quantified vars *)
    canonicalize_map_hyp H';
    ensure_new H'
  | H: ?P -> _ |- _ =>
    let T := type of P in unify T Prop;
    let F := fresh in
    assert P as F by eauto;
    let H' := fresh H "_eauto" in
    pose proof (H F) as H';
    clear F;
    canonicalize_map_hyp H';
    ensure_new H'
  end;
  let solver := congruence || auto || (exfalso; eauto) ||
                match goal with
                | H: ~ _ |- False => solve [apply H; intuition (auto || congruence || eauto)]
                end in
  let fallback := (destruct_one_map_match K V || pick_one_existential);
                  canonicalize_all K V in
  repeat (propositional;
          propositional_ors;
          try solve [ solver ];
          try fallback).
