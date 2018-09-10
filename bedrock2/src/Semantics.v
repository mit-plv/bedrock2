Require Import bedrock2.Macros bedrock2.Notations bedrock2.Syntax bedrock2.Map.
Require Import Coq.ZArith.BinIntDef.

Class parameters := {
  syntax :> Syntax.parameters;

  word : Set;
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

  globname_eqb : globname -> globname -> bool
}.

Section semantics.
  Context {pp : unique! parameters}.

  Fixpoint load_rec (sz : nat) (m:mem) (a:word) : option word :=
    match sz with
    | O => Some word_zero
    | S sz =>
      'Some b <- map.get m a                 | None;
      'Some w <- load_rec sz m (word_succ a) | None;
       Some (combine sz b w)
    end.
  Definition load n := load_rec (Z.to_nat n).
  Fixpoint unchecked_store_rec (sz : nat) (m:mem) (a v:word) : mem :=
    match sz with
    | O => m
    | S sz =>
      let '(b, w) := split sz v in
      unchecked_store_rec sz (map.put m a b) (word_succ a) w
    end.
  Definition unchecked_store n := unchecked_store_rec (Z.to_nat n).
  Definition store sz m a v : option mem :=
    match load sz m a with
    | None => None
    | Some _ => Some (unchecked_store sz m a v)
    end.
  Definition trace := list ((mem * actname * list word) * (mem * list word)).
End semantics.