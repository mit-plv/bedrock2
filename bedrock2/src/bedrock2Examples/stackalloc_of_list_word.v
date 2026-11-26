Require Import bedrock2.NotationsCustomEntry.
Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition stack_roundtrip := func! (v) ~> r {
  stackalloc 4 as t;
  store4(t, v);
  r = load4(t)
}.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.BasicC32Semantics.
Require Import coqutil.Map.Interface coqutil.Map.OfListWord bedrock2.Map.SeparationLogic bedrock2.Scalars.
Require Import coqutil.Word.LittleEndianList.

Section WithParameters.
  Local Notation word := (bits 32).

  (* stack frames are kept as maps [bs $@ a] rather than as byte arrays *)
  #[local] Instance : Memory.stackalloc_as_map := {}.

  Global Instance spec_of_stack_roundtrip : spec_of "stack_roundtrip" :=
    fnspec! "stack_roundtrip" (v : word) / (R : mem -> Prop) ~> r,
    { requires t m := m =* R;
      ensures t' m' := m' =* R /\ t' = t /\ r = v }.

  Lemma stack_roundtrip_ok : program_logic_goal_for_function! stack_roundtrip.
  Proof.
    repeat straightline.
    seprewrite_in_by @scalar32_of_list_word_at H ltac:(Lia.lia).
    repeat straightline.
    intuition auto.
  Qed.
End WithParameters.
