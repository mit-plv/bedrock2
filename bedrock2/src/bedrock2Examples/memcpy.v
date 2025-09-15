Require Import bedrock2.NotationsCustomEntry bedrock2.wsize.

Import Syntax BinInt String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface Coq.Init.Byte Coq.Strings.String Coq.Lists.List.
Import coqutil.Map.SortedListString. Local Existing Instances SortedListString.map SortedListString.ok.
From bedrock2 Require Import Semantics WeakestPrecondition ProgramLogic.
Import ProgramLogic.Coercions.

From bedrock2Examples Require Import memmove.

Section WithSemantics.
Context {width} {BW: Bitwidth width}.
Context {word: word.word width} {mem: map.map word byte}.
Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.
Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

#[export] Instance spec_of_br_memcpy : spec_of "br_memcpy" :=
  fnspec! "br_memcpy" (p_d p_s n : word) / (d s : list byte) R,
  { requires t m := m =* d$@p_d * s$@p_s * R /\
      length d = n :> Z /\ length s = n :> Z /\ 2*n <= 2^width;
    ensures t' m := t' = t /\ m =* s$@p_d * s$@p_s * R }.

Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia coqutil.Map.SeparationLogic.

Definition br_memcpy := func! (d, s, n) {
  memmove(d, s, n)
}.

Lemma br_memcpy_ok :
  let '_ := spec_of_memmove in
  program_logic_goal_for_function! br_memcpy.
Proof.
  cbv [spec_of_br_memcpy].
  repeat straightline.
  eapply WeakestPreconditionProperties.Proper_call; cycle 1.
  { eapply H; repeat apply conj; try ecancel_assumption; trivial.
    revert H3; remember (word.unsigned n); case BW as [[ -> | -> ] ]; clear; Lia.lia. }
  repeat intro.
  repeat (straightline || straightline_call); intuition eauto; try ecancel_assumption; trivial.
Qed.
End WithSemantics.
