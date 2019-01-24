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

Require Import AdmitAxiom.
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
    SeparationLogic.seprewrite_in @array_address_inbounds H1; revgoals.
    2:exact eq_refl.
    letexists. split.
    letexists. split. exact eq_refl.
    letexists. split.
    eapply load_sep; seplog.
    letexists. split. cbv [v4]. exact eq_refl.
    cbv [v1]. exact eq_refl.

    split; intros; repeat straightline.
    {
      repeat letexists. split. split; cbv [x4 x5 x6]; exact eq_refl.
      repeat letexists. 
      split.
      split.
      rename v0 into mid.
      subst x4; subst x5; subst x6; subst v2.
      subst x7; subst x8.
      cbn [interp_binop] in *.
      seplog.
      exact eq_refl.
      split. left. auto.

      intros. destruct H5. split. auto.

      subst x8.
      unshelve eapply (SeparationLogic.Proper_sep_iff1 _ _ _ _ _ (RelationClasses.reflexivity _) _); shelve_unifiable.
      eapply array_address_inbounds.
      3: exact eq_refl.
      3: seplog.
      admit. admit.

    }
    {
      repeat letexists. split. split; cbv [x4 x5 x6]; exact eq_refl.
      repeat letexists. 
      split.
      split.
      rename v0 into mid.
      subst x4; subst x5; subst x6.
      subst x7; subst x8.
      cbn [interp_binop] in *.
      seplog.
      exact eq_refl.
      split. left. auto.

      intros. destruct H5. split. auto.

      subst x8.
      unshelve eapply (SeparationLogic.Proper_sep_iff1 _ _ _ _ _ (RelationClasses.reflexivity _) _); shelve_unifiable.
      eapply array_address_inbounds.
      3: exact eq_refl.
      3: seplog.
      admit. admit.
    }

    {
      rewrite word.unsigned_of_Z.
      rewrite (Z.mod_small 8) by admit.
      cbv [interp_binop] in *. subst v0.
      admit.
    } 

    {
      cbv [interp_binop] in *. subst v0.
      admit.
    }

    { auto. }
  }

  repeat straightline.

  split.
  exact eq_refl.
  split.
  exact H2.

  letexists. split. exact eq_refl.
  auto.

  Unshelve.
  exact (word.of_Z 0).
Qed.

(*
total time:      2.001s

 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------  28.1%  34.9%     149    0.136s
─seplog --------------------------------  24.4%  27.7%      10    0.208s
─SeparationLogic.reify_goal ------------   0.3%  24.0%       6    0.120s
─SeparationLogic.ecancel --------------- -14.0%  19.6%       4    0.115s
─unshelve (tactic1) --------------------   3.7%  19.2%      24    0.108s
─split ---------------------------------  18.0%  18.0%      38    0.177s
─rewrite (SeparationLogic.sep_assoc A B   16.7%  17.6%      10    0.051s
─SeparationLogic.find_syntactic_unify --   8.2%  14.6%       0    0.045s
─syntactic_unify._syntactic_unify ------  14.3%  14.3%    1683    0.033s
─tac -----------------------------------  10.6%  10.6%      29    0.073s
─WeakestPrecondition.unfold1_expr_goal -   0.1%   9.2%      16    0.020s
─WeakestPrecondition.unfold1_expr ------   8.9%   8.9%       0    0.019s
─change (Lift1Prop.iff1 (seps LHS) (seps   6.1%   6.1%       6    0.034s
─WeakestPrecondition.unfold1_cmd_goal --   0.0%   4.1%       7    0.009s
─straightline_cleanup ------------------   3.4%   3.7%     712    0.003s
─SeparationLogic.seprewrite_in ---------   0.0%   3.6%      63    0.071s
─SeparationLogic.seprewrite0_in --------   0.1%   3.3%       3    0.034s
─program_logic_goal_for_function -------   3.2%   3.2%       0    0.064s
─eabstract (tactic3) -------------------   0.2%   3.2%       3    0.026s
─WeakestPrecondition.unfold1_cmd -------   3.1%   3.1%       0    0.009s
─refine (uconstr) ----------------------   2.9%   2.9%      48    0.037s
─abstract exact_no_check pf ------------   2.8%   2.8%       3    0.023s
─admit ---------------------------------   0.1%   2.6%       8    0.012s
─abstract case proof_admitted ----------   2.4%   2.4%       8    0.011s
─change G ------------------------------   2.3%   2.3%      25    0.023s
─simple refine (uconstr) ---------------   2.3%   2.3%      10    0.007s

 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------  28.1%  34.9%     149    0.136s
 ├─unshelve (tactic1) ------------------   0.1%  14.5%       3    0.108s
 │ ├─tac -------------------------------  10.6%  10.6%       5    0.073s
 │ └─eabstract (tactic3) ---------------   0.2%   3.2%       3    0.026s
 │  └abstract exact_no_check pf --------   2.8%   2.8%       3    0.023s
 ├─WeakestPrecondition.unfold1_expr_goal   0.1%   9.2%      16    0.020s
 │└WeakestPrecondition.unfold1_expr ----   8.9%   8.9%       0    0.019s
 ├─WeakestPrecondition.unfold1_cmd_goal    0.0%   4.1%       7    0.009s
 │└WeakestPrecondition.unfold1_cmd -----   3.1%   3.1%       0    0.009s
 └─straightline_cleanup ----------------   3.4%   3.7%     673    0.003s
─seplog --------------------------------  24.4%  27.7%      10    0.208s
 ├─SeparationLogic.ecancel ------------- -14.1%  18.4%       3    0.115s
 │ ├─SeparationLogic.reify_goal --------   0.3%  23.5%       5    0.120s
 │ │ ├─rewrite (SeparationLogic.sep_asso  16.7%  17.6%      10    0.051s
 │ │ └─change (Lift1Prop.iff1 (seps LHS)   5.6%   5.6%       5    0.034s
 │ └─SeparationLogic.find_syntactic_unif   4.5%   7.5%       0    0.044s
 │  └syntactic_unify._syntactic_unify --   7.3%   7.4%     870    0.032s
 └─SeparationLogic.find_syntactic_unify    3.7%   6.2%       0    0.045s
  └syntactic_unify._syntactic_unify ----   6.1%   6.1%     694    0.033s
─split ---------------------------------  17.6%  17.6%      21    0.177s
─SeparationLogic.seprewrite_in ---------   0.0%   3.6%      63    0.071s
 ├─unshelve (tactic1) ------------------   3.6%   3.6%      19    0.071s
 └─SeparationLogic.seprewrite0_in ------   0.1%   3.3%       2    0.034s
─program_logic_goal_for_function -------   3.2%   3.2%       0    0.064s
─admit ---------------------------------   0.0%   2.3%       6    0.012s
└abstract case proof_admitted ----------   2.1%   2.1%       6    0.011s
*)