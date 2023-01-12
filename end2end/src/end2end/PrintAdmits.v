Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require end2end.End2EndLightbulb.
Open Scope Z_scope.
Open Scope string_scope.
Set Printing Width 150.
(* creates admits.out in the current working directory *)
Redirect "admits" Print Assumptions end2end.End2EndLightbulb.end2end_lightbulb.
