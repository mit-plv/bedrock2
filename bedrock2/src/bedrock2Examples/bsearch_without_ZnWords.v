Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import bedrock2.ZnWords.
From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Array Scalars Loops.

Require Import egg.Loader.
Require Import Coq.Logic.PropExtensionality.
Require Import bedrock2.egg_lemmas.

Require bedrock2Examples.Demos.
Definition bsearch := Demos.bsearch.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
Require Import coqutil.Word.Properties.

Local Open Scope Z_scope.

From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.
Strategy -1000 [word]. (* TODO where should this go? *)

Declare Scope word_scope.

Local Infix "^+" := word.add  (at level 50, left associativity) : word_scope.
Local Infix "^-" := word.sub  (at level 50, left associativity) : word_scope.
Local Infix "^<<" := word.slu  (at level 37, left associativity) : word_scope.
Local Infix "^>>" := word.sru  (at level 37, left associativity) : word_scope.
Local Notation "/_" := word.of_Z       (* smaller angle: squeeze a Z into a word *)
 : word_scope.
Local Notation "\_" := word.unsigned   (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
 : word_scope.

Local Open Scope word_scope.

From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
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

Ltac consts :=
  lazymatch goal with
  | |- ?a <= ?b < ?c => requireZcstExpr a; requireZcstExpr b; requireZcstExpr c;
                        eapply computable_bounds
  | |- ?a <= ?b => requireZcstExpr a; requireZcstExpr b;
                   eapply computable_le
  | |- ?a < ?b => requireZcstExpr a; requireZcstExpr b;
                  eapply computable_lt
  | |- ?a <> ?b => requireZcstExpr a; requireZcstExpr b; unfold not; discriminate 1
  end;
  reflexivity.

Lemma eight_divides_2_64: (2 ^ 3 | 2 ^ 64).
Proof. unfold Z.divide. exists (2 ^ 61). reflexivity. Qed.

Ltac pose_const_sideconds :=
  assert (0 <= 8 < 2 ^ 64) as C1 by consts;
  assert (0 <= 3 < 64) as C2 by consts;
  assert (0 <= 4 < 64) as C3 by consts;
  assert (0 <= 2 ^ 3) as C4 by consts;
  assert (0 < 2 ^ 4) as C5 by consts;
  assert (0 < 2 ^ 64) as C6 by consts;
  assert (0 < 2 ^ 3) as C7 by consts;
  assert (2 ^ 3 < 2 ^ 4) as C8 by consts;
  assert (2 ^ 3 = 8) as C9 by reflexivity;
  pose proof eight_divides_2_64 as C10.

(* will have to stop using fully applied sep *)
Ltac desep :=
  repeat match goal with
         | H: sep _ _ _ |- _ => clear H
         | x := context[@sep] |- _ => subst x
         end.

Ltac preproc :=
  desep; pose_const_sideconds;
  pose_word_lemmas 64 word; pose_Z_lemmas; pose_Prop_lemmas; pose_list_lemmas.

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
    rename H2 into length_rep. subst br.
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)

    { (*
      subst mid.
      rewrite word.unsigned_of_Z_nowrap by consts.
      rewrite <- length_rep.
      rewrite word.word_sub_add_l_same_l.
      rewrite word.unsigned_slu_to_mul_pow2 by consts.
      rewrite word.unsigned_sru_to_div_pow2 by consts.

      eapply Z.le_lt_trans. 1: eapply Z.mod_le.
      { eapply Ztac.mul_le. 2: consts.
        eapply Z.div_pos. 2: consts.
        eapply word.unsigned_nonneg.}
      { consts. }
      eapply Z.div_mul_lt. 2,3: consts.
      eapply Z.lt_from_le_and_neq.
      1: apply word.unsigned_nonneg.
      apply neq_sym.
      apply H4. *)


      preproc.
      all: egg_step 3.
      all: egg_step 3.
      all: egg_step 3.
      all: egg_step 3.
      all: egg_step 3.
    }
    { preproc.
      (*
      subst mid.
      rewrite wunsigned_of_Z_nowrap by exact C1.
      rewrite wsub_def.
      rewrite wadd_comm.
      rewrite wadd_to_left_assoc.
      rewrite (wadd_comm (word.opp x1) x1).
      rewrite wadd_opp.
      rewrite wadd_0_l.
      rewrite wunsigned_slu_to_mul_pow2 by exact C2.
      rewrite <- C9.
      rewrite z_remove_inner_mod. 2: exact C7. 2: exact C6. 2: exact C10.
      rewrite z_mod_mult.
      reflexivity.
      *)

      all: egg_step 3.
    }

    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      {

        repeat match goal with
               | x := _ |- _ => clear x || subst x
               end.

        preproc.
        clear H2.

        set (halflen := (8 * Z.of_nat v / 2 ^ 4)).

  assert (8 <> 0) as C11 by consts.
  assert (2 ^ 64 = 2 ^ 64 / 8 * 8) as C12 by reflexivity.
  assert (2 ^ 64 / 8 * 2 ^ 4 = 2 * 2 ^ 64) as C13 by reflexivity.
  assert (0 < 2) as C14 by reflexivity.
  assert (2 ^ 4 = 8 * 2) by reflexivity.

        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 2.
        all: egg_step 3.
        all: egg_step 2.

rewrite (z_mod_small (Z.of_nat v - (halflen + 1))).

  2: {
    subst halflen.
    all: egg_step 3.
    all: egg_step 3.

    (* Z.of_nat v appears twice, so (independent) bounds propagation won't work well,
       because it doesn't know that the two occurrences are correlated *)

    replace (Z.of_nat v - (Z.of_nat v / 2 + 1)) with
      (Z.of_nat v - Z.of_nat v / 2 - 1).
    2: {
    all: egg_step 3.
    }

rewrite (Z.euclidean_decomp (Z.of_nat v) 2) at 1 3.

replace (Z.of_nat v / 2 * 2 + Z.of_nat v mod 2 - Z.of_nat v / 2 - 1)
with (Z.of_nat v mod 2 + Z.of_nat v / 2 - 1). 2: {
  ZnWords.
}

(* after a simplification attempt, Z.of_nat v still appears twice, but now
   once in a mod and once in a div, but bounds propagation still doesn't
   know about the correlation *)

    move length_rep at bottom.
    move H3 at bottom.
    move H4 at bottom.
    rewrite H3 in length_rep.
    pose proof (wunsigned_upper (x2 ^- x1)) as U. unfold with_trigger in U.
    rewrite length_rep in U.

(* could do bounds propagation like in AbsintWordToZ.v, but lower bound would
   not be strong enough:

  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               0                  0       -1

  need case distinction: Z.of_nat v can't be 0. If it is 1:

  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               1                  0       -1
  ok

  If Z.of_nat v >= 2:
  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               0                  1       -1
  ok

  so how does ZnWords do it?
*)
    ZnWords.
  }

  all: egg_step 2.
  ZnWords.
}

      { cleanup_for_ZModArith. reflexivity. }
      split; repeat straightline.
      2:split; repeat straightline.
      2: SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWordsL. }
      { ZnWords. }
      { ZnWords. }
      { trivial. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split.
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
      { cleanup_for_ZModArith. reflexivity. }
      split.
      { ZnWordsL. }
      repeat straightline; split; trivial.
      subst x5. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWords. }
      { ZnWords. }
      { ZnWords. }
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Time Qed. (* 1.637 secs *)
