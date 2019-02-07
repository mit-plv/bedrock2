Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil.Tactics Require Import syntactic_unify.

(* custom rewrite tactic to work around COQBUG(4885) *)
Ltac set_evars := repeat match goal with |- context[?e] => is_evar e; set e end.
Ltac subst_evars := repeat match goal with x := ?e |- _ => is_evar e; subst x end.
Ltac _ureplace_in_by pat hyp tac :=
  multimatch goal with
  | H: context [?lhs] |- _ =>
    assert_succeeds (idtac;
                     let pat := open_constr:(pat) in (* uconstr -> open_constr *)
                     let pat := lazymatch pat with ?pat => pat end in (* strip casts if any *)
                     syntactic_unify lhs pat);
    let T := type of lhs in
    let rhs := open_constr:(_:T) in
    let rhs := lazymatch rhs with ?rhs => rhs end in (* strip cast *)
    replace lhs with rhs in H by tac
  end.
Tactic Notation "ureplace" uconstr(pat) "in" hyp(hyp) "by" tactic3(tac) := _ureplace_in_by pat hyp tac.

Ltac _ureplace_by pat tac :=
  let g := fresh in
  let H := fresh in
  lazymatch goal with |- ?G => remember G as g eqn:H end;
  ureplace pat in H by tac;
  subst g.
Tactic Notation "ureplace" uconstr(pat) "by" tactic3(tac) := _ureplace_by pat tac.

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.
Local Notation "\_" := word.unsigned.
Local Open Scope Z_scope.
Lemma word__add_sub x y : (x^+y^-x) = y.
Proof.
  apply Properties.word.unsigned_inj.
  rewrite word.unsigned_sub, word.unsigned_add.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l.
  apply Properties.word.wrap_unsigned.
Qed.

Monomorphic Definition word__monomorphic_ring_theory := Properties.word.ring_theory.
Add Ring word_ring : word__monomorphic_ring_theory.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

From coqutil Require Import Z.div_mod_to_equations.

Axiom __mem_ok : map.ok mem. Local Existing Instance __mem_ok.

Local Set Default Goal Selector "1".

Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  pose proof __mem_ok.
  bind_body_of_function bsearch. cbv [spec_of_bsearch].

  intros. letexists. split; [exact eq_refl|]. (* argument initialization *)

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
    seprewrite @array_address_inbounds.
    1: admit. 1: admit. 1: exact eq_refl.
    (* if expression *)  letexists; split. 1: repeat straightline. (* determines element *)
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split. 1: repeat straightline.
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v2; subst x7. SeparationLogic.ecancel_assumption. }
      { cbn [interp_binop] in *. subst v2; subst x7. subst v0.
        repeat ureplace (_:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl).
        rewrite Properties.word.unsigned_divu_nowrap by discriminate.
        change (\_ (/_ 8)) with 8.
        rewrite word.unsigned_slu by exact eq_refl.
        rewrite Z.mod_small by admit.
        rewrite Z.shiftl_mul_pow2 by discriminate.
        change (2^\_ (/_ 3)) with 8.
        rewrite Z.div_mul by discriminate.
        unshelve erewrite (_ : forall xs, Datatypes.length xs <> 0%nat -> Datatypes.length (List.tl xs) = pred (Datatypes.length xs)). admit.
        unshelve erewrite (_ : forall xs delta, (Datatypes.length xs > delta)%nat -> Datatypes.length (List.skipn delta xs) = (Datatypes.length xs - delta)%nat). admit.
        unshelve erewrite (_ : forall n, n <> O -> Z.of_nat (Init.Nat.pred n) = Z.of_nat n - 1). { clear. intros. Lia.lia. }
        rewrite Nat2Z.inj_sub, Z2Nat.id.
        rewrite word.unsigned_sub, Z.mod_small.
        rewrite word.unsigned_sub, Z.mod_small.
        rewrite word.unsigned_slu, Z.mod_small.
        rewrite Z.shiftl_mul_pow2 by discriminate.
        rewrite !Properties.word.unsigned_sru_nowrap by (exact eq_refl).
        rewrite Z.shiftr_div_pow2 by discriminate.
        change (2^\_ (/_ 3)) with 8.
        change (\_ (/_ 8)) with 8.
        change (2^\_ (/_ 4)) with 16.
        setoid_rewrite H3.
        Lia.lia.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit. }
      { left. exact I. }

      rename H3 into length_rep.

      cbv [interp_binop br] in H5; destruct (word.ltu x1 x2) eqn:Hbr; [clear H5|contradiction H5; exact eq_refl].
      rewrite word.unsigned_ltu, Z.ltb_lt in Hbr.
      assert (\_ (x2 ^- x1) <> 0) as Hnz. {
        assert (\_ x2 <> \_ x1) as HC by Lia.lia.
        intros HX. apply HC. clear -HX.
        rewrite word.unsigned_sub in HX.
        pose proof Properties.word.unsigned_range x1.
        pose proof Properties.word.unsigned_range x2.
        change width with 64 in *.
        Z.div_mod_to_equations; Lia.lia. }

      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H8.

      { cbn [interp_binop] in *.
        subst v0.

        rewrite word__add_sub.

        pose proof Properties.word.unsigned_range (x2 ^- x1) as Hb; rewrite length_rep in Hb; change width with 64 in Hb.
        pose proof Properties.word.unsigned_sru_nowrap (x2 ^- x1) (/_ 4) eq_refl as HH.
        rewrite length_rep in HH ; change (\_ (/_ 4)) with 4 in HH.

        pose proof word.unsigned_slu ((x2 ^- x1) ^>> /_ 4) (/_ 3) eq_refl as HH2.
        change (\_ (/_ 3)) with 3 in HH2.
        setoid_rewrite HH in HH2.
        rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in HH2 by discriminate.
        rewrite Z.mod_small in HH2 by (Z.div_mod_to_equations; Lia.lia).

        change (\_ (/_ 8)) with 8.
        setoid_rewrite HH2.

        Z.div_mod_to_equations; Lia.lia. }
      { cbn [interp_binop] in *.
        subst v0.

        (* repeat ureplace (_:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl). *)
        rewrite word__add_sub.

        (* absint: bottomup (repeat (rewrite_head || memoized_bottomup bounded_head))
           - recurse into arguments
           - repeat:
             - f_equal_n; (eassumption || exact eq_refl)
             - call "typeclasses" based on head symbol with goal [f arg1 args... = ?e]
             - refocus on ?e
           - call "typeclasses" based on head symbol in [?x <= f arg1 args... < ?y]
         *)

        Ltac requireZcst z :=
          lazymatch Coq.setoid_ring.InitialRing.isZcst z with
          | true => idtac
          end.

        Inductive treeshape := br2 (_ _ : treeshape) | lf.
        Ltac etransitivity_at_branches ts :=
          lazymatch ts with
          | lf => idtac
          | br2 ?b1 ?b2 =>
            etransitivity; [eapply f_equal2; [etransitivity_at_branches b1|etransitivity_at_branches b2]|]
          end.
        Ltac idtac_goal :=
          lazymatch goal with |- ?g => idtac g end.

        Ltac absint_rewrite_head :=
          repeat (etransitivity; [typeclasses eauto with absint_rewrite|]); exact eq_refl.

        Ltac lia := Omega.omega.

        Hint Extern 1 (@snd (@word.rep ?n ?W) _ (?x, _)) => exact (@word.unsigned n W x) : absint_semantics.
        Hint Extern 9999999 (@snd _ _ (?x, _)) => exact x : absint_semantics.

        Hint Extern 1 (?a mod ?b = _) => exact (Z.mod_small a b ltac:(lia)) : absint_rewrite.
        Hint Extern 1 (word.unsigned (word.of_Z ?a) = _)
        => (etransitivity; [exact (word.unsigned_of_Z a)|]; eapply f_equal2; absint_rewrite_head) : absint_rewrite.
        Hint Extern 1 (word.unsigned (word.add ?a ?b) = _)
        => (etransitivity; [exact (word.unsigned_add a b)|]; eapply f_equal2; absint_rewrite_head) : absint_rewrite.
        Hint Extern 1 (word.unsigned (word.sub ?a ?b) = _)
        => (etransitivity; [exact (word.unsigned_sub a b)|]; eapply f_equal2; absint_rewrite_head) : absint_rewrite.

        (* WHY is the following [solve] necessary? *)
        Hint Extern 1 (word.unsigned (word.slu ?a ?b) = _)
        => (etransitivity; [exact (word.unsigned_slu a b ltac:(lia))
                           |etransitivity_at_branches constr:(br2 (br2 lf lf) lf); solve[absint_rewrite_head]]) : absint_rewrite.
        Hint Extern 1 (word.unsigned (word.sru ?a ?b) = _)
        => (etransitivity; [exact (Properties.word.unsigned_sru_nowrap a b ltac:(lia)) | eapply f_equal2; absint_rewrite_head]) : absint_rewrite.

        Hint Extern 1 (Z.shiftr ?a ?b = _) => exact (Z.shiftr_div_pow2 a b ltac:(lia)) : absint_rewrite.
        Hint Extern 1 (Z.shiftl ?a ?b = _) => exact (Z.shiftl_mul_pow2 a b ltac:(lia)) : absint_rewrite.

        Ltac absint_head e :=
          let l := lazymatch constr:(ltac:(typeclasses eauto with absint_semantics) : (snd (e, _))) with ?l => l end in
          lazymatch goal with H: l = _ |- _ => fail | |- _ => idtac end;
          let r := open_constr:(_) in
          let H := fresh in
          eassert (l = r) as H by (absint_rewrite_head);
          assert_fails (constr_eq l r);
          (* idtac e ":  " l "=" r; *)
          idtac.

        Ltac absint e :=
          assert_fails (idtac; requireZcst e);
          assert_fails (idtac; lazymatch type of e with Type => idtac | Set => idtac | Prop => idtac end);
          (* idtac e; *)
          try match e with
              | ?f ?x => try absint f; try absint x
              end;
          try absint_head e.

        pose proof (eq_refl : 64 = width).
        pose proof (eq_refl : 18446744073709551616 = 2^width).

        let e := lazymatch goal with |- ?e = _ => e end in 
        absint e.
        rewrite H11, H12.
        rewrite (Z.mod_small _ (2^width)); cycle 1.
        { clear -H5. rewrite <-H5. Z.div_mod_to_equations. Lia.lia. }
        clear. Z.div_mod_to_equations. Lia.lia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v1; subst x7; subst x8. SeparationLogic.ecancel_assumption. }
      { admit. }
      { left. exact I. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H8.
      1: admit. 1: admit. 1: exact eq_refl.
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
