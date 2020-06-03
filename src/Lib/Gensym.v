Require Import Rupicola.Lib.Core.

Inductive Counter (n : nat) : Type :=
| ofNat : Counter n
.

Ltac gen_sym_inc :=
  lazymatch goal with
  | H : Counter ?n |- _ =>
    pose proof (ofNat (S n)); clear H
  | _ => pose proof (ofNat 0)
  end.

Ltac gen_sym_fetch prefix :=
  lazymatch goal with
  | H : Counter ?n |- _ =>
    let x := constr:((prefix ++ NilEmpty.string_of_uint (Nat.to_uint n))%string) in
    let x := eval cbv in x in
        constr:(x)
  end.
