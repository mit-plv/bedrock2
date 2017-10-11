Require Export Coq.omega.Omega.
Require Export bbv.Word.
Require Export compiler.Monad.
Require Export compiler.Decidable.
Require Export compiler.Tactics.

Class Map(T K V: Type) := mMap {
  empty: T;
  get: T -> K -> option V;
  put: T -> K -> V -> T;

  get_put_same: forall (m: T) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: T) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2
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
Defined.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.

(* We want assign ranges of variables for certain purposes, so we need a total order,
   and we want S for to generate a fresh variable, so let's just use nat. *)
Definition var := nat.
