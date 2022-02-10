Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Array Scalars Loops.

Require bedrock2Examples.Demos.
Definition bsearch := Demos.bsearch.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
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

Local Open Scope Z_scope.
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
Require Import bedrock2.ZnWords.

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
    { ZnWords. }
    { ZnWords. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
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
Qed.
(* Print Assumptions bsearch_ok. *)
(* SortedListString.string_strict_order *)
(* reconstruct_enforce *)
(* SortedListMap *)
