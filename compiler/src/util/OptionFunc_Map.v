Require Import Coq.Lists.List.
Require Import compiler.util.Set.
Require Import compiler.Decidable.
Require Import compiler.util.Map.
Require Import compiler.util.PropFunc_Set.

Definition TODO{T: Type}: T. Admitted.

Instance OptionFunc_Map(K V: Type){keq: DecidableEq K}{veq: DecidableEq V}: MapFunctions K V :=
{|
  map := K -> option V;

  map_domain_set := PropFunc_Set _;
  map_range_set := PropFunc_Set _;

  empty_map := fun k => None;
  get A k := A k;
  put A k v := fun k' => if keq k k' then Some v else A k';
  restrict M A := TODO;
  domain M := fun k => exists v, M k = Some v;
  range M := fun v => exists k, M k = Some v;

  reverse_get := TODO;
  intersect_map m1 m2 := fun k =>
                           match m1 k with
                           | Some v1 => match m2 k with
                                        | Some v2 => if veq v1 v2 then Some v1 else None
                                        | None => None
                                        end
                           | None => None
                           end;

  update_map m1 m2 := fun k =>
                        match m2 k with
                        | Some v2 => Some v2
                        | None => m1 k
                        end;

  (* hard to specify in terms of an implementation, would rather specify axiomatically *)
  remove_by_value m v := TODO;
  remove_values := TODO;

|}.
all: apply TODO.
Defined.
