Require Export compiler.Monad.
Require Export compiler.Decidable.
Require Export bbv.Word.

Class Map(T K V: Type) := mMap {
  empty: T;
  get: T -> K -> option V;
  put: T -> K -> V -> T;
  (* TODO probably needs some properties *)
}.

Instance Function_Map(K V: Type){decK: DecidableEq K}: Map (K -> option V) K V := {|
  empty := fun _ => None;
  get := id;
  put := fun (m: K -> option V) (k: K) (v: V) =>
           fun (k': K) => if dec (k = k') then Some v else m k'
|}.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.

Inductive binop: Set := OPlus | OMinus | OTimes.
