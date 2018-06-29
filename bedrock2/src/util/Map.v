Require Import compiler.util.Set.
Require Import compiler.Decidable.
Require Import Coq.Lists.List.

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;

  empty_map: map;
  get: map -> K -> option V;
  put: map -> K -> V -> map;
  restrict: map -> set K -> map;
  domain: map -> set K;
  range: map -> set V;
  
  get_put_same: forall (m: map) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: map) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;
  empty_is_empty: forall (k: K), get empty_map k = None

  (* TODO probably needs some more properties *)
}.

Arguments map _ _ {_}.

Definition TODO{T: Type}: T. Admitted.

Instance List_Map(K V: Type)(domain_set: SetFunctions K)(range_set: SetFunctions V):
  MapFunctions K V :=
{|
  map := list (K * V);
  
  map_domain_set := domain_set;
  map_range_set := range_set;

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
