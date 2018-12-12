From coqutil Require Import sanity.
Require bedrock2.Map.SortedList bedrock2.String.
Axiom string_strict_order : @SortedList.parameters.strict_order _ String.ltb.
Definition Build_parameters T := SortedList.parameters.Build_parameters String.string T String.ltb.
Definition map T := SortedList.map (Build_parameters T) string_strict_order.
Definition ok T : @Interface.map.ok String.string T (map T).
  pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
Qed.
Set Printing All.
Check ok.