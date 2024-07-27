From Coq Require Import ZArith.
From Coq Require Import String.
Require end2end.End2EndLightbulb.
Open Scope Z_scope.
Open Scope string_scope.
Set Printing Width 150.
(* creates admits.out in the current working directory *)
Redirect "admits" Print Assumptions end2end.End2EndLightbulb.end2end_lightbulb.
