Require Import coqutil.Map.Interface Coq.Strings.String.
Require bedrock2.Map.SortedListString.
Local Existing Instance bedrock2.Map.SortedListString.map.
Local Open Scope string_scope. Local Open Scope list_scope.

Local Instance StringMapSortedList T : map.map String.string T :=
  SortedList.map (SortedList.parameters.Build_parameters _ T String.eqb String.ltb).

Import SortedList List.ListNotations.
Goal False.
  assert (value (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) = [("a", 6); ("c", 9); ("z", 0)]%list) by exact eq_refl.
  assert ((map.get (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) "c") = Some 9) by exact eq_refl.
  assert ((map.get (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) "z") = Some 0) by exact eq_refl.
  assert ((map.get (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) "x") = None) by exact eq_refl.
  assert (map.putmany (map.put (map.put map.empty "z" 7) "0" 0) (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) = (map.put (map.put (map.put (map.put map.empty "a" 6) "z" 0) "c" 9) "0" 0)) by exact eq_refl.
Abort.