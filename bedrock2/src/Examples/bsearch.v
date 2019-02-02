Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

Lemma word__sub_add_l_same_l (x y : word) : (word.sub (word.add x y) x) = y.
Proof.
  eapply Properties.word.unsigned_inj.
  rewrite word.unsigned_sub, word.unsigned_add, Zminus_mod_idemp_l.
  unshelve erewrite (_:(_ - _=_)%Z); shelve_unifiable; [ring_simplify; exact eq_refl|].
  eapply Properties.word.wrap_unsigned.
Qed.

From coqutil Require Import Z.div_mod_to_equations.

Axiom __mem_ok : map.ok mem. Local Existing Instance __mem_ok.
Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  pose proof __mem_ok.
  bind_body_of_function bsearch. cbv [spec_of_bsearch].

  intros. letexists. split. exact eq_refl. (* argument initialization *)

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target => PrimitivePair.pair.mk
          (sep (array scalar (word.of_Z 8) left xs) R m /\ List.length xs = l)
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
    seprewrite @array_address_inbounds.
    admit. admit. exact eq_refl.
    (* if expression *)  letexists; split. repeat straightline. (* determines element *)
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split. repeat straightline.
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v2; subst x7. SeparationLogic.ecancel_assumption. }
      { left. exact I. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { cbn [interp_binop] in *.
        clear.
        subst v0.
        Local Infix "^+" := word.add  (at level 50, left associativity).
        Local Infix "^-" := word.sub  (at level 50, left associativity).
        Local Infix "^<<" := word.slu  (at level 37, left associativity).
        Local Infix "^>>" := word.sru  (at level 37, left associativity).
        Local Notation "/_" := word.of_Z.
        Local Notation "\_" := word.unsigned.
        Local Open Scope Z_scope.
        assert (word__add_sub : forall x y : word, (x^+y^-x) = y) by admit.
        assert (Z.of_nat (Datatypes.length x) <> 0) by admit.
        assert (\_ (x2 ^- x1) = 8*Z.of_nat (Datatypes.length x)) by admit.

        rewrite word__add_sub.

        pose proof Properties.word.unsigned_sru_nowrap (x2 ^- x1) (/_ 4) eq_refl.
        rewrite H0 in H1 ; change (\_ (/_ 4)) with 4 in H1.

        pose proof word.unsigned_slu ((x2 ^- x1) ^>> /_ 4) (/_ 3) eq_refl as H2.
        change (\_ (/_ 3)) with 3 in H2.
        setoid_rewrite H1 in H2.

        setoid_rewrite H2.
        clear -H.
        change (\_ (/_ 8)) with 8.
        rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by discriminate .
        zify. Z.div_mod_to_equations. admit. (* Lia.lia. stack overflow *)
      }
      {
        rewrite word.unsigned_of_Z, (Z.mod_small 8) by (split; (discriminate || exact eq_refl)).
        assert (word.unsigned (word.sub v0 x1) mod 8 = 0)%Z by admit; trivial.
      }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    { repeat letexists. split. repeat straightline.
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v1; subst x7; subst x8. SeparationLogic.ecancel_assumption. }
      { left. exact I. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      admit. admit. exact eq_refl.
      SeparationLogic.ecancel_assumption. } }

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
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  Unshelve.
  exact (word.of_Z 0).
  all:fail "remaining subgoals".
Admitted.
