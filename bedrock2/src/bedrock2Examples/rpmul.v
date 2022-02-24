Require Import ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Variant of "ipow" implementing multiplication in terms of addition instead
* of exponentiation in terms of multiplication. *)

Definition rpmul :=
  ("rpmul", (["x";"e"], (["ret"]), bedrock_func_body:(
  ret = $0;
  while (e) {
    if (e & $1) { ret = ret + x };
    e = e >> $1;
    x = x + x
  }
))).

From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.

#[export] Instance spec_of_rpmul : spec_of "rpmul" := fnspec! "rpmul" x e ~> v,
  { requires t m := True;
    ensures t' m' := t=t' /\ m=m' /\
      (* TODO could be expressed as just word.mul *)
      word.unsigned v = word.unsigned x * word.unsigned e mod 2^32 }.

Module Z.
  Lemma mod2_nonzero x : x mod 2 <> 0 -> x mod 2 = 1.
  Proof. Z.div_mod_to_equations. blia. Qed.
End Z.

Require Import bedrock2.AbsintWordToZ coqutil.Z.Lia.

Ltac t :=
  repeat match goal with x := _ |- _ => subst x end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := unsigned.zify_expr e in try rewrite H) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := unsigned.zify_expr e in try rewrite H in G) end;
  repeat match goal with H: absint_eq ?x ?x |- _ => clear H end;
  cbv [absint_eq] in *.

Lemma rpmul_ok : program_logic_goal_for_function! rpmul.
Proof.
  repeat straightline.
  repeat match goal with H : True |- _ => clear H end.

  refine ((Loops.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) (["e";"ret";"x"] : list String.string))
    (fun v t m e ret x => PrimitivePair.pair.mk (v = word.unsigned e) (* precondition *)
    (fun   T M E RET X => T = t /\ M = m /\ (* postcondition *)
        word.unsigned RET = (word.unsigned ret + word.unsigned x * word.unsigned e) mod 2^32))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      letexists; split; [repeat straightline|]. (* if condition evaluation *)
      split. (* if cases, path-blasting *)
      {
        repeat (straightline || (split; trivial; [])). all:t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          change (1+1) with 2 in *.
          eapply Z.mod2_nonzero in Hbit.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2. clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_add.
          unfold word.wrap.
          change (2 ^ 1) with 2.
          do 2 rewrite <- Z.add_mod_idemp_r by discriminate.
          rewrite Z.mul_mod_idemp_l by discriminate.
          rewrite <- Z.add_mod by discriminate.
          rewrite Z.add_mod_idemp_r by discriminate.
          f_equal; ring. } }
      {
        repeat (straightline || (split; trivial; [])).
        all: t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          change (1+1) with 2 in *.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          rewrite word.unsigned_add.
          cbv [word.wrap].
          change (2 ^ 1) with 2.
          rewrite <- Z.add_mod_idemp_r by discriminate.
          rewrite Z.mul_mod_idemp_l by discriminate.
          rewrite Z.add_mod_idemp_r by discriminate.
          f_equal; ring. } } }
    { (* postcondition *) rewrite H, Z.mul_0_r, Z.add_0_r, word.wrap_unsigned; auto. } }

  repeat straightline.

  repeat (split || letexists || t || trivial).
Defined.
