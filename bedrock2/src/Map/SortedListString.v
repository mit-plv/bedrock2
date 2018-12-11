From coqutil Require Import sanity.
Require bedrock2.Map.SortedList bedrock2.String.
Definition map T := SortedList.map (SortedList.parameters.Build_parameters String.string T String.eqb String.ltb).