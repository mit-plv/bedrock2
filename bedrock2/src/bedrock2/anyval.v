Require Import bedrock2.Lift1Prop.

Definition anyval{word mem T: Type}(p: T -> word -> mem -> Prop)(a: word): mem -> Prop :=
  ex1 (fun v => p v a).

(* makes __ a keyword, so "let __ := uselessvalue in blah" in Ltac
   doesn't parse any more!
Notation "p '__' a" := (anyval p a) (at level 20, a at level 9).
Infix "__" := anyval (at level 20).
*)

Notation "p ? a" := (anyval p a) (at level 20, a at level 9).
