Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap := func! (a, b) {
  t = load(b);
  store(b, load(a));
  store(a, t)
}.

Definition bad_swap := func! (a, b) {
  store(b, load(a));
  store(a, load(b))
}.

Definition swap_swap := func! (a, b) {
  swap(a, b);
  swap(a, b)
}.

Require Import bedrock2.LeakageWeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.LeakageSemantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.LeakageWeakestPreconditionProperties.
From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import bedrock2.LeakageProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.rdelta.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {pick_sp: PickSp}.

  Instance spec_of_swap : spec_of "swap" :=
    fnspec! exists f, "swap" a_addr b_addr / a b R,
    { requires k t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures K T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ T = t /\
                          K = f a_addr b_addr ++ k }.

  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof. repeat straightline. intuition eauto. align_trace. Qed.

  Instance spec_of_bad_swap : spec_of "bad_swap" :=
    fnspec! exists f, "bad_swap" a_addr b_addr / a b R,
    { requires k t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures K T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ T = t /\
                          K = f a_addr b_addr ++ k }.
  
  Lemma bad_swap_ok : program_logic_goal_for_function! bad_swap.
  Proof. repeat straightline. intuition eauto; align_trace. Abort.

  Definition spec_of_swap_same : spec_of "swap" :=
    fnspec! exists f, "swap" a_addr b_addr / a R,
    { requires k t m := m =* scalar a_addr a * R /\ b_addr = a_addr;
      ensures K T M :=  M =* scalar a_addr a * R /\ T = t /\ K = f a_addr ++ k }.

  Lemma swap_same_ok :
    let spec_of_swap := spec_of_swap_same in
    program_logic_goal_for_function! swap.
  Proof. repeat straightline. intuition eauto. align_trace. Qed.

  Instance spec_of_swap_swap : spec_of "swap_swap" :=
    fnspec! "swap_swap" a_addr b_addr / a b R,
    { requires k t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures K T M :=  M =* scalar a_addr a * scalar b_addr b * R /\ T = t }.

  Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
  Proof. repeat (straightline || straightline_call); eauto. Qed.

  Lemma link_swap_swap_swap_swap : spec_of_swap_swap (map.of_list &[,swap_swap; swap]).
  Proof. eauto using swap_swap_ok, swap_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module &[,swap_swap; swap]). Abort.
  *)
End WithParameters.
