Require Export Coq.omega.Omega.
Require Export bbv.Word.
Require Export compiler.Monad.
Require Export compiler.Decidable.
Require Export compiler.Tactics.
Require Export compiler.Set.
Require Export lib.fiat_crypto_tactics.UniquePose.
Require Export Coq.Logic.FunctionalExtensionality.

Class Map(T K V: Type) := mkMap {
  empty: T;
  get: T -> K -> option V;
  put: T -> K -> V -> T;

  get_put_same: forall (m: T) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: T) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;
  map_extensionality: forall m1 m2, (forall (k: K), get m1 k = get m2 k) <-> m1 = m2
  (* TODO probably needs some more properties *)
}.

Instance Function_Map(K V: Type){decK: DecidableEq K}: Map (K -> option V) K V := {|
  empty := fun _ => None;
  get := id;
  put := fun (m: K -> option V) (k: K) (v: V) =>
           fun (k': K) => if dec (k = k') then Some v else m k'
|}.
- intros. cbv. destruct_one_match; reflexivity || contradiction.
- intros. cbv. destruct_one_match; reflexivity || contradiction.
- intros. cbv. split; intros.
  + extensionality x. apply H.
  + congruence.
Defined.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.
