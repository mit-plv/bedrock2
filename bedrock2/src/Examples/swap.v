Require Coq.ZArith.BinInt Coq.Strings.String.
Require Import bedrock2.Syntax.Basic bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.Syntax.Basic.parameters.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

Definition swap := let a := "a" in let b := "b" in let t := "t" in
  ("swap", ([a; b], ([]:list varname), bedrock_func_body:(
  t = (load(b)) ;
  store(b, load(a));
  store(a, t)
))).

Definition swap_swap := let swap := "swap" in let a := "a" in let b := "b" in
  ("swap_swap", (("a"::"b"::nil), ([]:list varname), bedrock_func_body:(
  swap(a, b);
  swap(a, b)
))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.BasicC64Semantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Local Existing Instance bedrock2.BasicC64Semantics.parameters.

Axiom __map_ok : map.ok Semantics.mem. Local Existing Instance __map_ok. (* FIXME *)

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.
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

Require Import bedrock2.string2ident.

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

Print Assumptions link_swap_swap_swap_swap.
(* __map_ok SortedListString.string_strict_order SortedList.sorted_remove SortedList.sorted_put StrictOrderWord *)