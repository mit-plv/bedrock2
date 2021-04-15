Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition indirect_add : func := let a := "a" in let b := "b" in let c := "c" in
  ("indirect_add", ([a; b; c], [], bedrock_func_body:(
  store(a, load(b) + load(c))
))).

Definition indirect_add_twice : func := let a := "a" in let b := "b" in
  ("indirect_add_twice", ([a;b], [], bedrock_func_body:(
  indirect_add(a, a, b);
  indirect_add(a, a, b)
))).

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface coqutil.Map.Interface bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Definition f a b := word.add (word.add a b) b.

  Local Notation "m =* P" := (P%sep m) (at level 70, only parsing). (* experiment *)
  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" a b c / va Ra vb Rb vc Rc,
    { requires t m := m =* scalar a va * Ra /\ m =* scalar b vb * Rb /\ m =* scalar c vc * Rc;
      ensures t' m' := t=t' /\ m' =* scalar a (word.add vb vc) * Ra }.
  Instance spec_of_indirect_add_twice : spec_of "indirect_add_twice" :=
    fnspec! "indirect_add_twice" a b / va vb R,
    { requires t m := m =* scalar a va * scalar b vb * R;
      ensures t' m' := t=t' /\ m' =* scalar a (f va vb) * scalar b vb * R }.

  Lemma indirect_add_ok : program_logic_goal_for_function! indirect_add.
  Proof. repeat straightline; []; eauto. Qed.

  Lemma indirect_add_twice_ok : program_logic_goal_for_function! indirect_add_twice.
  Proof.
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    { split; trivial. split; trivial. cbv [f]. ecancel_assumption. }
  Qed.

  Example link_both : spec_of_indirect_add_twice (indirect_add_twice::indirect_add::nil).
  Proof. auto using indirect_add_twice_ok, indirect_add_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (* SortedList.* SortedListString.* *)

  From bedrock2 Require Import ToCString Bytedump.
  Local Open Scope bytedump_scope.
  Goal True.
    let c_code := eval cbv in (byte_list_of_string (c_module (indirect_add_twice::indirect_add::nil))) in
    idtac c_code.
  Abort.
End WithParameters.
