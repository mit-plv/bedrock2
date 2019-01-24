Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array (scalar Syntax.access_size.word) (word.of_Z 8) left xs) R m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array (scalar Syntax.access_size.word) (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.

Ltac seplog :=
  match goal with
  | H: _ ?m |- _ ?m =>
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
    solve [SeparationLogic.ecancel]
  end.

Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  assert (map.ok mem) by admit.

  bind_body_of_function bsearch. cbv [spec_of_bsearch].

  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  Import Markers.hide.
  Import PrimitivePair.
  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target => PrimitivePair.pair.mk
          (sep (array (scalar Syntax.access_size.word) (word.of_Z 8) left xs) R m /\ List.length xs = l)
        (fun        T M LEFT RIGHT TARGET => T = t /\ sep (array (scalar Syntax.access_size.word) (word.of_Z 8) left xs) R M))
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
    Arguments array_address_inbounds {_ _ _ _ _ _ _ _ _ _ _ _}.
    unshelve (
    let pf := open_constr:(array_address_inbounds (default:=word.of_Z 0) v0 _ _ _ eq_refl) in
    SeparationLogic.seprewrite_in pf H1);
    shelve_unifiable.
    admit. admit.

    letexists. split. repeat straightline.
    letexists. split. eapply load_sep; seplog.
    repeat straightline.

    split; intros; repeat straightline.
    { (* end-of-iteration goals *)
      repeat letexists. split. repeat straightline.
      repeat letexists. split; split.
      { cbn [interp_binop] in *.
        subst x4; subst x5; subst x6; subst v2.
        subst x7; subst x8.
        seplog. }
      { exact eq_refl. }
      { left. auto. }
      repeat straightline_cleanup. split.
      { auto. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      admit. admit. exact eq_refl.
      exact H6. }
    { (* end-of-iteration goals *)
      repeat letexists. split. repeat straightline.
      repeat letexists. split; split.
      { cbn [interp_binop] in *.
        subst x4; subst x5; subst x6; subst v1.
        subst x7; subst x8.
        seplog. }
      { exact eq_refl. }
      { left. auto. }
      repeat straightline_cleanup. split.
      { auto. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      admit. admit. exact eq_refl.
      exact H6. } }

  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  (* 8.8> repeat straightline. *)
  (* Error: Anomaly "Universe Top.370 undefined." Please report at http://coq.inria.fr/bugs/. *)
  straightline.
  repeat straightline.
  repeat apply conj. (* postcondition *)
  { auto. }
  { auto. }
  { letexists. split.
    { exact eq_refl. }
    { auto. } }
  all:fail "subgoals remaining".
Admitted.