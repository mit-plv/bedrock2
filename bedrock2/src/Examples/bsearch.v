Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.PushPullMod.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations Z.div_to_equations.
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

Lemma mix_eq_into_mod{lhs rhs m: Z}(E: lhs mod m = rhs)(a: Z):
    a mod m = (a - lhs + rhs) mod m.
Proof.
  intros. rewrite <- E. Z.mod_equality.
Qed.

Lemma mix_eq_into_unsigned{lhs: word}{rhs: Z}(E: word.unsigned lhs = rhs)(w: word):
  word.unsigned w = word.unsigned (word.add w (word.sub (word.of_Z rhs) lhs)).
Proof.
  intros.
  rewrite <- E.
  rewrite word.of_Z_unsigned.
  f_equal.
  ring.
Qed.

Lemma computable_bounds{lo v hi: Z}(H: andb (Z.leb lo v) (Z.ltb v hi) = true): lo <= v < hi.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1.
  apply Z.ltb_lt in H2.
  auto.
Qed.

Lemma computable_le{lo v: Z}(H: Z.leb lo v = true): lo <= v.
Proof. apply Z.leb_le. assumption. Qed.

Lemma computable_lt{lo v: Z}(H: Z.ltb lo v = true): lo < v.
Proof. apply Z.ltb_lt. assumption. Qed.

Ltac count_summands e :=
  lazymatch e with
  | Z.add ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | Z.sub ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | _ => Z.one
  end.

Goal False.
  let a := constr:((1 - 3) + (3 + 2 + 8)) in
  let n := count_summands a in set (x := n).
Abort.

Ltac rhs_fewer_summands E :=
   match type of E with
   | ?a mod ?x = ?b mod ?x =>
     let m := count_summands a in
     let n := count_summands b in
     let b := eval cbv in (Z.ltb n m) in
     lazymatch b with
     | true => idtac
     | false => fail "lhs has" m "summands, rhs has" n
     end
   end.

(* If we have "(... + a ... - b ...) mod m" and an equation "E: a - b = somethingSimpler",
   this tactic will replace "a - b" by "somethingSimpler", even though "a - b" does not
   appear as such. In a sense, it does rewriting where the matching is not syntactic, but
   according to the "ring" tactic on Z.
   And note that "a - b" is just an example lhs, it can be any ring expression over Z. *)
Ltac mix_eq_into_mod :=
  match goal with
  | E: ?lhs mod ?m = ?rhs |- context[?e mod ?m] =>
    let F := named_pose_proof (mix_eq_into_mod E e) in
    match type of F with
    | _ = ?R mod m => ring_simplify R in F
    end;
    rhs_fewer_summands F;
    rewrite F;
    clear F;
    (* removing the modulo, so let's remember its bounds: *)
    let B := named_pose_proof (Z.mod_pos_bound lhs m eq_refl) in
    rewrite E in B (* TODO prevent duplicate *)
  end.

Ltac lia2 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_mod_to_equations; blia.

Ltac lia3 :=
  idtac; (* for evaluation order when passing lia3 as an arg to other tactics *)
  lazymatch goal with
  | |- context[_ mod _] => fail "mod found, applying lia could be too expensive"
  | |- _ => lia2
  end.

Ltac lia4 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_to_equations; blia.

Ltac cleanup_for_ZModArith :=
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => lazymatch T with
                         | _ < _ => fail
                         | _ <= _ => fail
                         | _ <= _ < _ => fail
                         | @eq Z _ _ => fail
                         | not (@eq Z _ _) => fail
                         | _ => clear H
                         end
         end.

Ltac ZModArith_step lia_tac :=
  match goal with
  (* TODO delete this first line because it's already on the last line,
     it's just here to demo how "robust" the heuristics are which decide when
     it's safe to try lia *)
  | |- _ => solve [lia_tac]
  | |- _ => progress Z.push_pull_mod
  | |- context[?a mod ?m] =>
    (* Note: invoking lia here for Z.mod_small can be extremely expensive.
       We alleviate this by only doing it for terms which don't contain a
       mod themselves, thus getting a more bottom-up than top-down traversal,
       and apparently much less expensive lia goals *)
    lazymatch a with
    | context[_ mod _] => fail
    | _ => rewrite (Z.mod_small a m) by
          first [apply computable_bounds; reflexivity | assumption | lia_tac]
    end
  | |- _ => mix_eq_into_mod
  | |- _ => solve [lia_tac]
  end.

Ltac simpl_list_length_exprs := rewrite ?length_skipn. (* TODO improve *)

Hint Rewrite word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
       using solve[reflexivity || trivial]
  : word_laws.

Ltac wordOps_to_ZModArith :=
  repeat first
         [ progress (autorewrite with word_laws in *; cbv [word.wrap] in *)
         | rewrite Z.shiftr_div_pow2 by (apply computable_le; reflexivity)
         | rewrite Z.shiftl_mul_pow2 by (apply computable_le; reflexivity) ].

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
      {
        cleanup_for_ZModArith.
        simpl_list_length_exprs.
        wordOps_to_ZModArith.
        repeat ZModArith_step ltac:(lia4).
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
