Require Import bedrock2.BasicCSyntax bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type := String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.
Local Coercion expr.literal : Z >-> expr.

Definition stacknondet : bedrock_func := let a := "a" in let b := "b" in let t := "t" in
  ("stacknondet", ([]:list String.string, [a; b], bedrock_func_body:(stackalloc 4 as t {
  a = (load4(t) >> constr:(8));
  store1(a+constr:(3), constr:(42));
  b = (load4(t) >> constr:(8))
}))).

Definition stackdisj : bedrock_func := let a := "a" in let b := "b" in
  ("stackdisj", ([]:list String.string, [a; b], bedrock_func_body:(
  stackalloc 4 as a {
  stackalloc 4 as b {
  /*skip*/
}}))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Instance spec_of_stacknondet : spec_of "stacknondet" := fun functions => forall m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
        "stacknondet" t m [] (fun t' m' rets => exists a b, rets = [a;b] /\ a = b /\ m'=m/\t'=t).

  Require Import bedrock2.string2ident.

  Lemma stacknondet_ok : program_logic_goal_for_function! stacknondet.
  Proof.
    repeat straightline.
    split; trivial; [].
    repeat straightline.
  Abort.

  Instance spec_of_stackdisj : spec_of "stackdisj" := fun functions => forall m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
        "stackdisj" t m [] (fun t' m' rets => exists a b, rets = [a;b] /\ a <> b /\ m'=m/\t'=t).

  Lemma stackdisj_ok : program_logic_goal_for_function! stackdisj.
  Proof.
    repeat straightline.
    split; trivial; [].
    repeat straightline.
    split; trivial; [].
    repeat straightline.
    eexists _, _; split; eauto; split; eauto.
    eexists _, _; split; eauto; split; eauto.
    repeat straightline.
    cbn.
    eexists; split; eauto.
    eexists _, _; repeat split; eauto.

    destruct H0 as (?&?).
    destruct H1 as (?&?).
  Abort.


  From bedrock2 Require Import ToCString Bytedump.
  Local Open Scope bytedump_scope.
  Goal True.
    let c_code := eval cbv in (byte_list_of_string (@c_module to_c_parameters (stacknondet::nil))) in
    idtac c_code.
  Abort.
End WithParameters.
