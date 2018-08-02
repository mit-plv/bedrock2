Require Import bedrock2.Macros bedrock2.Notations bedrock2.Syntax bedrock2.Map.
Require Import Coq.ZArith.BinIntDef.

Class parameters := {
  syntax :> Syntax.parameters;

  word : Type;
  word_zero : word;
  word_succ : word -> word;
  word_test : word -> bool;
  word_of_Z : BinNums.Z -> option word;
  interp_binop : bopname -> word -> word -> word;

  byte : Type;
  (* nat included for conceptual completeness, only middle-endian would use it *)
  combine : nat -> byte -> word -> word;
  split : nat -> word -> byte * word;

  mem :> map word byte;
  locals :> map varname word;

  funname_eqb : funname -> funname -> bool
}.

Section semantics.
  Context {pp : unique! parameters}.
  
  Fixpoint load (sz : nat) (m:mem) (a:word) : option word :=
    match sz with
    | O => Some word_zero
    | S sz =>
      'Some b <- map.get m a             | None;
      'Some w <- load sz m (word_succ a) | None;
       Some (combine sz b w)
    end.
  Fixpoint store (sz : nat) (m:mem) (a v:word) : option mem :=
    match sz with
    | O => Some m
    | S sz =>
      let '(b, w) := split sz v in
      'Some _ <- map.get m a | None;
      store sz (map.put m a b) (word_succ a) w
    end.
  Definition trace := list ((mem * actname * list word) * (mem * list word)).
End semantics.