Require Import riscv.Decidable.
Require Import compiler.Tactics.

Class TotalMap(T K V: Type) := mkTotalMap {
  get: T -> K -> V;
  put: T -> K -> V -> T;

  get_put_same: forall (m: T) (k: K) (v: V), get (put m k v) k = v;
  get_put_diff: forall (m: T) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;
}.

Instance Function_TotalMap(K V: Type){decK: DecidableEq K}: TotalMap (K -> V) K V := {|
  get := id;
  put := fun (m: K -> V) (k: K) (v: V) =>
           fun (k': K) => if dec (k = k') then v else m k'
|}.
all: abstract (intros; unfold id; destruct_one_match; congruence).
Defined.
