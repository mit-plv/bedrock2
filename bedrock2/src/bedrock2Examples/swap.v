Require Import bedrock2.BasicCSyntax bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type := funname * (list varname * list varname * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition swap : bedrock_func := let a := "a" in let b := "b" in let t := "t" in
  ("swap", ([a; b], ([]:list varname), bedrock_func_body:(
  t = (load(b)) ;
  store(b, load(a));
  store(a, t)
))).

Definition swap_swap := let a := "a" in let b := "b" in
  ("swap_swap", (("a"::"b"::nil), ([]:list varname), bedrock_func_body:(
  swap(a, b);
  swap(a, b)
))).

Definition main :=
  ("main", ([]: list varname, []: list varname, cmd.call [] "swap_swap" [expr.literal 100; expr.literal 108])).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Local Infix "*" := sep. Local Infix "*" := sep : type_scope.
  Instance spec_of_swap : spec_of "swap" := fun functions =>
    forall a_addr a b_addr b m R t,
      (scalar a_addr a * (scalar b_addr b * R)) m ->
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
        "swap" t m [a_addr; b_addr]
        (fun t' m' rets => t=t'/\ (scalar a_addr b * (scalar b_addr a * R)) m' /\ rets = nil).

  Instance spec_of_swap_swap : spec_of "swap_swap" := fun functions =>
    forall a_addr a b_addr b m R t,
      (scalar a_addr a * (scalar b_addr b * R)) m ->
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
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

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (* SortedList.* SortedListString.* *)

  From bedrock2 Require Import ToCString Byte Bytedump.
  Local Open Scope bytedump_scope.
  Goal True.
    let c_code := eval cbv in (of_string (@c_module to_c_parameters (swap_swap::swap::nil))) in
    idtac c_code.
  Abort.
End WithParameters.
