Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.

Strategy -1000 [word parameters]. (* TODO where should this go? *)

Module absint_test.
  Fixpoint goal (x : word) (n : nat) : Prop
    := match n with
       | O => True
       | S n' => let x := word.add x x in goal x n'
       end.
  Goal forall x X, 1 <= X < 2^60 -> absint_eq (word.unsigned x) X -> goal x 7.
  Proof.
    cbv beta iota delta [goal].
    intros.

    let e := match goal with x := _ |- _ => x end in
    let e := constr:(word.ndn (word.xor (word.or (word.and (word.sub (word.mul (word.slu (word.sru e (word.of_Z 16)) (word.of_Z 3)) x) x) x) x) x) x) in
    let H := unsigned.zify_expr e in
    idtac H.
    exact I.
  Qed.


  Goal forall x y, 0 <= x < 5 -> 10 <= y < 20 -> True.
  Proof.
    intros.

    set (a := x+y).
    set (b := y+x).
    set (c := a*b+7).

    let e := constr:(a + y mod 2 * (b*(x*y/4)) + c) in
    let H := rbounded e in
    cbn in *.

    let e := constr:(a*c + b) in
    let H := rbounded e in
    idtac H;
    cbn in *.
    exact I.
  Qed.
End absint_test.

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.
Local Notation "\_" := word.unsigned.
Local Open Scope Z_scope.

From coqutil Require Import Z.div_mod_to_equations.
From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

Local Unset Simplex. (* COQBUG(9615) *)
Lemma bsearch_ok : program_logic_goal_for_function! bsearch.
Proof.
  repeat straightline.

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target => PrimitivePair.pair.mk
                                               (sep (array scalar (word.of_Z 8) left xs) R m /\
                                                \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                                                List.length xs = l)
        (fun        T M LEFT RIGHT TARGET => T = t /\ sep (array scalar (word.of_Z 8) left xs) R M))
        lt _ _ _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact lt_wf. }
  { eauto. }
  { repeat straightline.
    2: solve [auto]. (* exiting loop *)
    (* loop body *)
    rename H2 into length_rep. subst br. subst v0.
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H end.
      rewrite length_rep in *. (* WHY is this necessary for blia? *)
      Z.div_mod_to_equations. blia. }
    { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H end.
      Z.div_mod_to_equations. blia. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst v1. subst x7.
        clear H1 x8 H5 v0.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        unshelve erewrite (_ : _ ^- _ = x2 ^- x1 ^- (/_ 8 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3)); [ring|].
        rewrite word.unsigned_sub.
        repeat (rewrite ?length_rep || match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end).
        pose proof Properties.word.unsigned_range (x2 ^- x1) as HH; rewrite length_rep in HH, H4.
        cbv [word.wrap].
        rewrite Z.mod_small; cycle 1. { clear -HH H4. PreOmega.zify. Z.div_mod_to_equations. blia. }
        rewrite length_skipn.
        rewrite Z.div_mul by discriminate.
        (* Z and nat ... *)
        PreOmega.zify; rewrite Z2Nat.id in *; Z.div_mod_to_equations; blia. }
      { subst v'. subst v. subst x7.
        set (\_ (x1 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- x1) / \_ (/_ 8)) as X.
        assert (X < Z.of_nat (Datatypes.length x)). {
          eapply Z.div_lt_upper_bound; [exact eq_refl|].
          rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
          repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
          rewrite length_rep in *. (* WHY does lia need this? *)
          revert H4. clear. intros. Z.div_mod_to_equations. blia. }
        rewrite length_skipn; bomega. }
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. bomega. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst v1. subst x7.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite List.firstn_length_le; cycle 1.
        { assert (Datatypes.length x <> 0)%nat by bomega.
          revert H13. clear. intros. Z.div_mod_to_equations; zify; rewrite Z2Nat.id by blia; blia. }
        rewrite Z2Nat.id by (clear; Z.div_mod_to_equations; blia).
        clear. Z.div_mod_to_equations. blia. }
      { subst v. subst v'. subst x7.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        assert (Datatypes.length x <> 0)%nat by bomega.
        rewrite List.firstn_length_le; cycle 1.
        { revert H12. clear. intros. Z.div_mod_to_equations; zify; rewrite Z2Nat.id by blia; blia. }
        revert H12. clear. zify. rewrite Z2Nat.id; (Z.div_mod_to_equations; blia). }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. bomega. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Qed.
(* Print Assumptions bsearch_ok. *)
(* SortedListString.string_strict_order *)
(* reconstruct_enforce *)
(* SortedListMap *)

Local Set Simplex.