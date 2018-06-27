Require Import riscv.util.Monads.
Require Import compiler.Tactics.

Inductive Res(A: Type): Type :=
| Success(a: A): Res A
| Fail: Res A
| OutOfFuel: Res A.

Arguments Success {A}.
Arguments Fail {A}.
Arguments OutOfFuel {A}.

Instance Res_Monad: Monad Res := {| 
  Bind := fun {A B: Type} (r: Res A) (f: A -> Res B) => match r with
          | Success a => f a
          | Fail => Fail
          | OutOfFuel => OutOfFuel
          end;
  Return := fun {A: Type} (a: A) => Success a
|}.
- intros; reflexivity.
- intros; destruct_one_match; reflexivity.
- intros; repeat destruct_one_match; reflexivity.
Defined.

Definition option2res{A: Type}(o: option A): Res A :=
  match o with
  | Some a => Success a
  | None => Fail
  end.
