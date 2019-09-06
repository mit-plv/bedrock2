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

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.      (* smaller angle: squeeze a Z into a word *)
Local Notation "\_" := word.unsigned.  (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
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

    Import Markers.hide. idtac.

    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { rewrite ?Properties.word.word_sub_add_l_same_l. rewrite ?Properties.word.word_sub_add_l_same_r.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H end.
      (* rewrite length_rep in *. (* WHY is this necessary for blia? *) *)
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

(* does one simplification step *)
Ltac wsimp e parentIsWord simplifier :=
  first
  [ (* try to simplify child expression *)
    lazymatch e with
    | @word.add _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.mul _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.sub _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.opp _ _ ?a    =>         wsimp a true simplifier
    | ?f ?a               => first [ wsimp f false simplifier | wsimp a false simplifier ]
    end
  | (* If we're here, no child expression could be simplified. *)
    lazymatch parentIsWord with false => idtac end;
    lazymatch e with
    | @word.add _ _ _ _ => idtac
    | @word.mul _ _ _ _ => idtac
    | @word.sub _ _ _ _ => idtac
    | @word.opp _ _ _   => idtac
    end;
    progress (simplifier e)
  ].

Ltac wsimp_goal :=
  repeat match goal with
         | |- ?G =>  wsimp G false ltac:(fun e => ring_simplify e)
         end.

Ltac wsimp_hyps :=
  repeat match goal with
         | H: ?P |- _ => wsimp P false ltac:(fun e => ring_simplify e in H)
         end.

Ltac wsimp_star := wsimp_goal; wsimp_hyps.

Ltac lia2 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_mod_to_equations; blia.

        wsimp_star.

        replace (x2 ^- x1 ^- (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- /_ 8) with
            (x2 ^- x1 ^- (/_ 8 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3)); [|wsimp_star; ring].
        rewrite word.unsigned_sub.

        (* push/pull mod??
        TODO delete it in compiler, update submodule
        TODO: can we use "ring_simplify [HH GG] (a - b + c)" to throw in additional equations? *)

        match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; idtac H e end.
        match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; idtac H e end.
        match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; idtac H e end.

        rewrite ?length_rep.

        pose proof Properties.word.unsigned_range (x2 ^- x1) as HH.
        rewrite length_rep in HH, H4.
        cbv [word.wrap].
        rewrite Z.mod_small; cycle 1. { clear -HH H4. Z.div_mod_to_equations. blia. }
        rewrite length_skipn.
        rewrite Z.div_mul by discriminate.
        clear -H4.
        lia2.
      }

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
          revert H13. clear. intros. Z.div_mod_to_equations; zify; rewrite ?Z2Nat.id by blia; blia. }
        rewrite Z2Nat.id by (clear; Z.div_mod_to_equations; blia).
        clear. Z.div_mod_to_equations. blia. }
      { subst v. subst v'. subst x7.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        assert (Datatypes.length x <> 0)%nat by bomega.
        rewrite List.firstn_length_le; cycle 1.
        { revert H12. clear. intros. Z.div_mod_to_equations; zify; rewrite ?Z2Nat.id by blia; blia. }
        revert H12. clear. zify. rewrite ?Z2Nat.id; (Z.div_mod_to_equations; blia). }
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
