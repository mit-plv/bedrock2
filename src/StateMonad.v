Require Import Coq.Logic.FunctionalExtensionality.
Require Export compiler.Monad.


Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
            fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
Defined.

Definition get{S: Type}: State S S := fun (s: S) => (s, s).
Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).


(* Evaluate state computation with given initial state, discard final state, return final answer *)
Definition evalState{S A: Type}(m: State S A)(initial: S): A := fst (m initial).

(* Evaluate state computation with given initial state, discard final answer, return final state *)
Definition execState{S A: Type}(m: State S A)(initial: S): S := snd (m initial).

