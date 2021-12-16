Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap : func :=
  ("swap", (["a"; "b"], [], bedrock_func_body:(
  t = load(b);
  store(b, load(a));
  store(a, t)
))).

Definition swap_swap : func :=
  ("swap_swap", (["a";"b"], [], bedrock_func_body:(
  swap(a, b);
  swap(a, b)
))).

Definition main : func :=
  ("main", ([], [], bedrock_func_body:(
    swap_swap($100, $108)))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Local Infix "*" := sep. Local Infix "*" := sep : type_scope.
  Instance spec_of_swap : spec_of "swap" := fun functions =>
    forall a_addr a b_addr b m R t,
      (scalar a_addr a * (scalar b_addr b * R)) m ->
      WeakestPrecondition.call functions
        "swap" t m [a_addr; b_addr]
        (fun t' m' rets => t=t'/\ (scalar a_addr b * (scalar b_addr a * R)) m' /\ rets = nil).

  Instance spec_of_swap_swap : spec_of "swap_swap" := fun functions =>
    forall a_addr a b_addr b m R t,
      (scalar a_addr a * (scalar b_addr b * R)) m ->
      WeakestPrecondition.call functions
        "swap_swap" t m [a_addr; b_addr]
        (fun t' m' rets => t=t' /\ (scalar a_addr a * (scalar b_addr b * R)) m' /\ rets = nil).

  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof.
    repeat straightline; []; eauto.
  Defined.

  Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
  Proof.
    repeat (straightline || (straightline_call; [solve[SeparationLogic.ecancel_assumption]|])); []; eauto.
  Defined.

  Lemma link_swap_swap_swap_swap : spec_of_swap_swap (swap_swap::swap::nil).
  Proof. auto using swap_swap_ok, swap_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (* SortedList.* SortedListString.* *)

  (*
  From bedrock2 Require Import ToCString Bytedump.
  Local Open Scope bytedump_scope.
  Goal True.
    let c_code := eval cbv in (String.list_byte_of_string (c_module (swap_swap::swap::nil))) in
    idtac c_code.
  Abort.
  *)
End WithParameters.
