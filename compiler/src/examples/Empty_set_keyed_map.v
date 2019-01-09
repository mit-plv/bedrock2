Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedList.

Instance Empty_set_strictorder: SortedList.parameters.strict_order
                                  (fun (e1 e2: Empty_set) => false).
Proof.
  constructor; intros; match goal with x: Empty_set |- _ => destruct x end.
Qed.

Instance Empty_set_keyed_map_params(V: Type): SortedList.parameters := {|
  parameters.key := Empty_set;
  parameters.value := V;
  parameters.ltb e1 e2 := false;
|}.
Instance Empty_set_keyed_map(V: Type): map.map Empty_set V :=
  SortedList.map (Empty_set_keyed_map_params V) Empty_set_strictorder.
