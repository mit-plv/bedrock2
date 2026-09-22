Require Import Coq.micromega.Lia.
Require Import bedrock2.NotationsCustomEntry bedrock2.wsize.

Import Syntax BinInt String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Import coqutil.Word.Bitwidth coqutil.Map.Interface Coq.Init.Byte Coq.Strings.String Coq.Lists.List.
Import coqutil.Map.SortedListString. Local Existing Instances SortedListString.map SortedListString.ok.
From bedrock2 Require Import LeakageSemantics LeakageWeakestPrecondition LeakageProgramLogic.
Import LeakageProgramLogic.Coercions.

From bedrock2Examples Require Import memmove.

Section WithSemantics.
Context {width} {BW: Bitwidth width}.
Local Notation word := (bits width).
Context {mem: map.map word byte}.
Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec} {pick_sp: PickSp}.
Context {mem_ok: map.ok mem}.

#[export] Instance spec_of_br_memcpy : spec_of "br_memcpy" :=
  fnspec! exists f, "br_memcpy" (p_d p_s n : word) / (d s : list byte) R,
  { requires k t m := m =* d$@p_d * s$@p_s * R /\
      length d = n :> Z /\ length s = n :> Z /\ 2*n <= 2^width;
    ensures k' t' m' := t' = t /\ m' =* s$@p_d * s$@p_s * R /\ k' = f p_d p_s n ++ k }.

Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia coqutil.Map.SeparationLogic.

Definition br_memcpy := func! (d, s, n) {
  memmove(d, s, n)
}.

Lemma br_memcpy_ok :
  let '_ := spec_of_memmove in
  program_logic_goal_for_function! br_memcpy.
Proof.
  enter br_memcpy. (* introduces memmove's leakage function as [f] *)
  exists (fun p_d p_s n => f p_d p_s n ++ (leak_unit :: nil)); intros.
  match goal with
  | H: map.get ?functions ?fname = Some _ |- _ =>
      eapply LeakageWeakestPreconditionProperties.start_func; [exact H | clear H]
  end.
  cbv match beta delta [LeakageWeakestPrecondition.func].
  repeat straightline.
  straightline_call.
  { repeat apply conj; try ecancel_assumption; trivial.
    revert H3; remember (Zmod.unsigned n); case BW as [[ -> | -> ] ]; clear; Lia.lia. }
  repeat straightline.
  repeat apply conj; try ecancel_assumption; trivial.
  align_trace.
Qed.
End WithSemantics.
