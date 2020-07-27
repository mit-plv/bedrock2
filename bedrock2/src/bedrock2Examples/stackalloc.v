Require Import bedrock2.BasicCSyntax bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type := String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.
Local Coercion expr.literal : Z >-> expr.

Definition stacktrivial : bedrock_func := let t := "t" in
  ("stacktrivial", ([]:list String.string, [], bedrock_func_body:(stackalloc 4 as t { /*skip*/ }))).

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

  Instance spec_of_stacktrivial : spec_of "stacktrivial" := fun functions => forall m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
        "stacktrivial" t m [] (fun t' m' rets => rets = [] /\ m'=m /\ t'=t).

  
  Lemma stacktrivial_ok : program_logic_goal_for_function! stacktrivial.
  Proof.
    repeat straightline.
    set (R := eq m).
    pose proof (eq_refl : R m) as Hm.
    split; trivial; [].
    repeat straightline.

    match goal with
      Hsplit: map.split ?mCobined ?m ?mStack,
      Hanybytes: anybytes ?a ?n ?mStack |- _ =>
      let Hm' := fresh Hm in
      rename Hm into Hm';
      let stack := fresh "stack" in
      let stack_length := fresh "length_" stack in (* MUST remain in context for deallocation *)
      let Htmp := fresh in
      destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length);
      pose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
                  : sep R (Array.array ptsto (Interface.word.of_Z 1) a _) mCombined) as Hm;
      clear Htmp Hsplit Hanybytes mStack;
      try (let m' := fresh m in rename m into m'); rename mCombined into m
    end.

    (* to be incorporated in previous match / maybe refactor lemma in previous match *)
    assert (Z.of_nat (Datatypes.length stack) = 4) as H_length_stack.
    1:rewrite length_stack, Znat.Z2Nat.id; try apply Zbool.Zle_bool_imp_le; exact eq_refl.
    clear length_stack.
    
    let m := match goal with |- exists _ _, _ /\ map.split ?m _ _ /\ _ => m end in
    let Hm := match goal with Hm : _ m |- _ => Hm end in
    let Hm' := fresh Hm in
    pose proof Hm as Hm';
    let Psep := match type of Hm with ?P _ => P end in
    let Htmp := fresh "Htmp" in
    eassert (Lift1Prop.iff1 Psep (sep _ (Array.array ptsto (Interface.word.of_Z 1) a stack))) as Htmp
      by ecancel || fail "failed to find" lemma_lhs "in" Psep "using ecancel";
    eapply (fun m => proj1 (Htmp m)) in Hm;
    let m' := fresh m in
    rename m into m';
    destruct Hm as (m&mStack&Hsplit&Hm&Harray1); move Hm at bottom;
    pose proof Array.array_1_to_anybytes _ _ _ Harray1 as Hanybytes;
    rewrite H_length_stack in Hanybytes;
    refine (ex_intro _ m (ex_intro _ mStack (conj Hanybytes (conj Hsplit _))));
    clear Htmp Hsplit mStack Harray1 Hanybytes.

    repeat straightline.
    intuition idtac.
  Qed.

  Instance spec_of_stacknondet : spec_of "stacknondet" := fun functions => forall m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions
        "stacknondet" t m [] (fun t' m' rets => exists a b, rets = [a;b] /\ a = b /\ m'=m/\t'=t).

  Require Import bedrock2.string2ident.

  Lemma stacknondet_ok : program_logic_goal_for_function! stacknondet.
  Proof.
    repeat straightline.
    set (R := eq m).
    pose proof (eq_refl : R m) as Hm.
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
