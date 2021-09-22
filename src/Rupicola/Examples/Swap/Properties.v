Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax. Import Syntax.Coercions.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Rupicola.Examples.Swap.Swap.
Require bedrock2.WeakestPrecondition.
Require bedrock2.Semantics.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.
Import Swap.Bedrock2.


Local Infix "~>" := scalar (at level 40, only parsing).

Section Proofs.
  Instance spec_of_swap : spec_of swap :=
    fun functions =>
      forall a_ptr a b_ptr b tr R mem,
        seps [a_ptr ~> a; b_ptr ~> b; R] mem ->
        WeakestPrecondition.call
          functions swap tr mem [a_ptr; b_ptr]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil
             /\ seps [a_ptr ~> b; b_ptr ~> a; R] mem').

  Lemma swap_correct : program_logic_goal_for_function! swap.
  Proof.
    repeat straightline. cbn [seps] in *.
    eexists; split; [ solve [repeat straightline] | ].
    repeat straightline.
    repeat split; ecancel_assumption.
  Qed.
End Proofs.
