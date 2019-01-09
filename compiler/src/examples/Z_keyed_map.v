Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedList.

Instance Zltb_strictorder: SortedList.parameters.strict_order Z.ltb.
Proof.
  constructor; intros; rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.ltb_irrefl in *;
    reflexivity || lia.
Qed.

Instance Zkeyed_map_params(V: Type): SortedList.parameters := {|
  parameters.key := Z;
  parameters.value := V;
  parameters.ltb := Z.ltb;
|}.

Instance Zkeyed_map(V: Type): map.map Z V :=
  SortedList.map (Zkeyed_map_params V) Zltb_strictorder.
