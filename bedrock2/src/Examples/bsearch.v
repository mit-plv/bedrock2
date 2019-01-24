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
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      admit. admit. exact eq_refl. exact H6.
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
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      admit. admit. exact eq_refl. exact H6.
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
Warning: Ltac Profiler cannot yet handle backtracking into multi-success tactics; profiling results may be wildly inaccurate. [profile-backtracking,ltac]
total time:      2.390s

 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─unshelve (tactic1) --------------------  27.8%  39.4%      27    0.307s
─straightline --------------------------  23.5%  29.8%     149    0.134s
─SeparationLogic.seprewrite_in ---------   0.0%  27.7%     225    0.307s
─SeparationLogic.reify_goal ------------   0.2%  21.3%       6    0.117s
─SeparationLogic.ecancel --------------- -10.9%  17.1%       4    0.136s
─SeparationLogic.seprewrite0_in --------  -2.0%  16.2%       8    0.209s
─rewrite (SeparationLogic.sep_assoc A B   14.9%  16.0%      10    0.058s
─split ---------------------------------  15.3%  15.3%      38    0.169s
─seplog --------------------------------  14.7%  14.7%       6    0.137s
─eassert (pf : Lift1Prop.iff1 Psep (sep    6.5%  10.9%       2    0.205s
─SeparationLogic.find_syntactic_unify --   4.7%   8.9%       0    0.037s
─syntactic_unify._syntactic_unify ------   8.7%   8.7%    1188    0.026s
─tac -----------------------------------   8.2%   8.2%      27    0.072s
─WeakestPrecondition.unfold1_expr_goal -   0.1%   6.0%      16    0.016s
─WeakestPrecondition.unfold1_expr ------   5.8%   5.8%       0    0.016s
─change (Lift1Prop.iff1 (seps LHS) (seps   5.0%   5.0%       6    0.033s
─straightline_cleanup ------------------   4.4%   4.6%     712    0.007s
─eapply (SeparationLogic.Proper_sep_iff1   4.6%   4.6%       3    0.045s
─WeakestPrecondition.unfold1_cmd_goal --   0.0%   3.7%       7    0.013s
─eabstract (tactic3) -------------------   0.2%   2.8%       3    0.028s
─WeakestPrecondition.unfold1_cmd -------   2.8%   2.8%       0    0.013s
─program_logic_goal_for_function -------   2.6%   2.6%       0    0.062s
─abstract exact_no_check pf ------------   2.5%   2.5%       3    0.025s
─refine (uconstr) ----------------------   2.4%   2.4%      46    0.036s
─exact_sym_under_binders ---------------   2.0%   2.0%       0    0.028s

 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------  23.5%  29.8%     149    0.134s
 ├─unshelve (tactic1) ------------------   0.1%  11.7%       3    0.111s
 │ ├─tac -------------------------------   8.2%   8.2%       5    0.072s
 │ └─eabstract (tactic3) ---------------   0.2%   2.8%       3    0.028s
 │  └abstract exact_no_check pf --------   2.5%   2.5%       3    0.025s
 ├─WeakestPrecondition.unfold1_expr_goal   0.1%   6.0%      16    0.016s
 │└WeakestPrecondition.unfold1_expr ----   5.8%   5.8%       0    0.016s
 ├─straightline_cleanup ----------------   4.4%   4.6%     673    0.007s
 └─WeakestPrecondition.unfold1_cmd_goal    0.0%   3.7%       7    0.013s
  └WeakestPrecondition.unfold1_cmd -----   2.8%   2.8%       0    0.013s
─SeparationLogic.seprewrite_in ---------   0.0%  27.7%     225    0.307s
 ├─unshelve (tactic1) ------------------  27.7%  27.7%      24    0.307s
 │└SeparationLogic.seprewrite0_in ------   0.0%   3.4%       3    0.045s
 │└eapply (SeparationLogic.Proper_sep_if   3.3%   3.3%       2    0.045s
 └─SeparationLogic.seprewrite0_in ------  -2.0%  12.8%       5    0.209s
   ├─eassert (pf : Lift1Prop.iff1 Psep (   6.5%  10.9%       2    0.205s
   │└SeparationLogic.ecancel ----------- -11.6%   2.5%       1    0.028s
   │ ├─SeparationLogic.reify_goal ------   0.1%  10.1%       3    0.117s
   │ │ ├─rewrite (SeparationLogic.sep_as   6.8%   7.3%       4    0.058s
   │ │ └─change (Lift1Prop.iff1 (seps LH   2.6%   2.6%       3    0.033s
   │ └─SeparationLogic.find_syntactic_un   1.7%   3.2%       0    0.023s
   │  └syntactic_unify._syntactic_unify    3.1%   3.1%     399    0.015s
   └─SeparationLogic.find_syntactic_unif   1.1%   2.3%       0    0.037s
    └syntactic_unify._syntactic_unify --   2.2%   2.2%     317    0.026s
─split ---------------------------------  14.7%  14.7%      21    0.169s
─seplog --------------------------------  14.7%  14.7%       6    0.137s
└SeparationLogic.ecancel ---------------   0.7%  14.6%       3    0.136s
└SeparationLogic.reify_goal ------------   0.1%  11.2%       3    0.093s
 ├─rewrite (SeparationLogic.sep_assoc A    8.1%   8.7%       6    0.046s
 └─change (Lift1Prop.iff1 (seps LHS) (se   2.4%   2.4%       3    0.024s
─program_logic_goal_for_function -------   2.6%   2.6%       0    0.062s
─exact_sym_under_binders ---------------   2.0%   2.0%       0    0.028s
*)