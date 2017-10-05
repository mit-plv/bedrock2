Require Import Coq.Logic.FunctionalExtensionality.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f = f a;
  right_identity: forall {A} (m: M A),
    Bind m Return = m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g = Bind m (fun x => Bind (f x) g)
}.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60).
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60).

Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
          | Some x => f x
          | None => None
          end;
  Return := fun {A: Type} (a: A) => Some a
|}.
- intros. reflexivity.
- intros. destruct m; reflexivity.
- intros. destruct m; reflexivity.
Defined.

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

