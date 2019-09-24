(* fully descriptive separation logic predicates *)

Require Import coqutil.Map.Interface bedrock2.Lift1Prop. Import map.

Section Sep.
  Context {key value} {mem : map key value}.

  (* the type of separation logic predicates is "option mem", and "None" means that
     something which was claimed to be disjoint is not disjoint *)

  Definition holds(P: option mem): mem -> Prop :=
    match P with
    | Some m => eq m
    | None => fun _ => False
    end.

  Parameter disjoint_putmany: mem -> mem -> option mem.

  Definition emp: option mem := Some empty.
  Definition sep(P Q: option mem): option mem :=
    match P, Q with
    | Some mp, Some mq => disjoint_putmany mp mq
    | _, _ => None
    end.

  Definition ptsto(k: key)(v: value): option mem := Some (put empty k v).

  Fixpoint seps (xs : list (option mem)) : option mem :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp
    end.
End Sep.
