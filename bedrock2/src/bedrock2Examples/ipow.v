Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition ipow :=
  ("ipow", (["x";"e"], (["ret"]:list String.string), bedrock_func_body:(
  ret = $1;
  while (e) {
    if (e & $1) { ret = ret * x };
    e = e >> $1;
    x = x * x
  }
))).

From bedrock2 Require Import Semantics BasicC64Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.

#[global] Instance spec_of_ipow : spec_of "ipow" := fun functions =>
  forall x e t m,
    WeakestPrecondition.call functions
      "ipow" t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v] /\ (
        word.unsigned v = word.unsigned x ^ word.unsigned e mod 2^64)).


Module Z.
  Lemma pow_mod x n m (Hnz: m <> 0) : (x mod m)^n mod m = x^n mod m.
  Proof.
    revert n.
    eapply Z.order_induction_0; intros.
    { intros ???; subst; split; auto. }
    { rewrite 2Z.pow_0_r; trivial. }
    { rewrite 2Z.pow_succ_r by trivial.
      rewrite <-Z.mul_mod_idemp_r by trivial.
      multimatch goal with H: _ |- _ => rewrite H end;
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; solve[trivial]. }
    { rewrite 2Z.pow_neg_r; trivial. }
  Qed.

  Lemma mod2_nonzero x : x mod 2 <> 0 -> x mod 2 = 1.
  Proof. Z.div_mod_to_equations. blia. Qed.

  Lemma land_1_r x : Z.land x 1 = x mod 2.
  Proof.
    change 1 with (Z.ones 1) in *.
    rewrite Z.land_ones in * by discriminate.
    exact eq_refl.
  Qed.
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

Lemma ipow_ok : program_logic_goal_for_function! ipow.
Proof.
  repeat straightline.

  refine ((Loops.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) (["e";"ret";"x"] : list String.string))
    (fun v t m e ret x => PrimitivePair.pair.mk (v = word.unsigned e) (* precondition *)
    (fun   T M E RET X => T = t /\ M = m /\ (* postcondition *)
        word.unsigned RET = word.unsigned ret * word.unsigned x ^ word.unsigned e mod 2^64))
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
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul.
          unfold word.wrap.
          rewrite ?Z.mul_mod_idemp_l by discriminate.
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.pow_add_r by (pose proof word.unsigned_range x0; Z.div_mod_to_equations; blia).
          rewrite ?Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
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
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul, ?Z.mul_mod_idemp_l by discriminate.
          cbv [word.wrap].
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.add_0_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. } } }
    { (* postcondition *) rewrite H, Z.pow_0_r, Z.mul_1_r, word.wrap_unsigned; auto. } }

  repeat straightline.

  repeat (split || letexists || t || trivial).
  setoid_rewrite H1; setoid_rewrite Z.mul_1_l; trivial.
Defined.
