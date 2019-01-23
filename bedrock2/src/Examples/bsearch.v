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
    tailrec (HList.polymorphic_list.cons (list word) (HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs t m left right target => PrimitivePair.pair.mk
          (List.length xs = l /\ sep (array (scalar Syntax.access_size.word) (word.of_Z 8) left xs) R m)
        (fun      T M LEFT RIGHT TARGET => True))
        _ lt_wf _ _ _ _ _);
    
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { admit. }
  { repeat straightline.
    (* TODO: fix seprewrite to actually rewrite not just factor *)
    SeparationLogic.seprewrite_in @array_address_inbounds H2; revgoals.
    letexists. split.
    letexists. split. exact eq_refl.
    letexists. split.
    eapply load_sep; seplog.
    cbv [v1]. exact eq_refl.

    repeat straightline.
    letexists. split.
    letexists. split.
    exact eq_refl.
    letexists. split.
    exact eq_refl.
    exact eq_refl.
Abort All.
