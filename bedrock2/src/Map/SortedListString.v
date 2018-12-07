Require bedrock2.Map.SortedList bedrock2.String.
Definition map T := SortedList.map (SortedList.parameters.Build_parameters _ T String.eqb String.ltb).