Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap := func! (a, b) {
  store(a, load(a)+load(b));
  store(b, load(a)-load(b));
  store(a, load(a)-load(b))
}.

Definition swap_swap := func! (a, b) {
  swap(a, b);
  swap(a, b)
}.

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Naive.
Require Import coqutil.Tactics.eplace Coq.setoid_ring.Ring_tac.

Section WithParameters.
  Context {mem: map.map word32 Byte.byte} {mem_ok: map.ok mem}.
  Implicit Types (R : mem -> Prop).

  Instance spec_of_swap : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ T = t }.

  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof. repeat straightline; ring_simplify_words; eauto. Qed.

  Definition spec_of_swap_same : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a R,
    { requires t m := m =* scalar a_addr a * R /\ b_addr = a_addr;
      ensures T M :=  M =* scalar a_addr (word.of_Z 0) * R /\ T = t }.

  Lemma swap_same_weird :
    let spec_of_swap := spec_of_swap_same in
    program_logic_goal_for_function! swap.
  Proof. repeat straightline; ring_simplify_words; eauto. Qed.

  Instance spec_of_swap_swap : spec_of "swap_swap" :=
    fnspec! "swap_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr a * scalar b_addr b * R /\ T = t}.

  Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
  Proof.
    repeat (straightline || straightline_call); eauto.
  Qed.

  Lemma link_swap_swap_swap_swap : spec_of_swap_swap &[,swap_swap; swap].
  Proof. eauto using swap_swap_ok, swap_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module &[,swap_swap; swap]). Abort.
  *)
End WithParameters.
