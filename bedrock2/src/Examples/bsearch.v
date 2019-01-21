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

Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
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
    eapply SeparationLogic.Proper_sep_iff1 in H1.
    3:reflexivity.
    2:symmetry.
    2:eapply (array_address_inbounds _ _ (word.of_Z 0) _ _ v0).
    4:reflexivity.
    3: {
      subst v0.
      cbn [interp_binop].
      unshelve erewrite (_:forall x y, word.sub (word.add x y) x = y). admit.
      rewrite word.unsigned_slu, Properties.word.unsigned_sru_nowrap by admit.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2.
      rewrite !word.unsigned_of_Z.
      cbn.
      set ((Naive.unsigned x1 - Naive.unsigned x0) mod 18446744073709551616 / 16)%Z.
Abort All.
