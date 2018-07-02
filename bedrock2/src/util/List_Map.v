Require Import Coq.Lists.List.
Require Import compiler.util.Set.
Require Import compiler.Decidable.
Require Import compiler.util.Map.
Require Import compiler.util.List_Set.

Definition TODO{T: Type}: T. Admitted.

Instance List_Map(K V: Type){keq: DecidableEq K}{veq: DecidableEq V}: MapFunctions K V :=
{|
  map := list (K * V);
  
  map_domain_set := List_Set _;
  map_range_set := List_Set _;

  empty_map := nil;
  get A k := match find (fun a => if set_elem_eq_dec (fst a) k then true else false) A with
             | Some (_, v) => Some v
             | None => None
             end;
  put A k v := (fix rec A := match A with
                            | (k1, v1) :: rest => if set_elem_eq_dec k1 k then (k, v) :: rest
                                                 else (k1, v1) :: rec rest
                            | nil => (k, v) :: nil
                            end) A;
  restrict M A := filter (fun p => containsb A (fst p)) M;
  domain M := of_list (List.map fst M);
  range M := of_list (List.map snd M);
|}.
all: apply TODO.
Defined.
