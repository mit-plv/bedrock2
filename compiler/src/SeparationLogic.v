Require Export Coq.Lists.List. Export ListNotations.
Require Export Coq.ZArith.BinInt. Open Scope Z_scope.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Map.Interface.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Array.

Infix "*" := sep : sep_scope.

Delimit Scope sep_scope with sep.
Arguments impl1 {T} (_)%sep (_)%sep.
Arguments iff1 {T} (_)%sep (_)%sep.

(* TODO does not get rid of %sep in printing as intended *)
Arguments sep {key} {value} {map} (_)%sep (_)%sep.

Ltac seplog :=
  match goal with
  | H: _ ?m |- _ ?m =>
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
    solve [SeparationLogic.ecancel]
  end.
