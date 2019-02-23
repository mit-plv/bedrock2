Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require Import bedrock2.Examples.Demos.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.TODO_absint.

Strategy -1000 [word parameters]. (* TODO where should this go? *)

Module absint_test.
  Local Existing Instance BasicC64Semantics.parameters.
  Fixpoint goal (x : word) (n : nat) : Prop
    := match n with
       | O => True
       | S n' => let x := word.add x x in goal x n'
       end.
  Goal forall x X, 1 <= X < 2^60 -> unsigned.absint_eq (word.unsigned x) X -> goal x 7.
  Proof.
    cbv beta iota delta [goal].
    intros.

    let e := match goal with x := _ |- _ => x end in
    let e := constr:(word.ndn (word.xor (word.or (word.and (word.sub (word.mul (word.slu (word.sru e (word.of_Z 16)) (word.of_Z 3)) x) x) x) x) x) x) in
    let H := unsigned.zify_expr e in
    idtac H.
    exact I.
  Qed.


  Goal forall x y, 0 <= x < 5 -> 10 <= y < 20 -> True.
  Proof.
    intros.
  
    set (a := x+y).
    set (b := y+x).
    set (c := a*b+7).
  
    let e := constr:(a + y mod 2 * (b*(x*y/4)) + c) in
    let H := rbounded e in
    cbn in *.
  
    let e := constr:(a*c + b) in
    let H := rbounded e in
    idtac H;
    cbn in *.
    exact I.
  Qed.
End absint_test.

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
Lemma word__add_sub {width} {w : word.word width} {ok : word.ok w} x y : (x^+y^-x) = y.
Proof.
  apply Properties.word.unsigned_inj.
  rewrite word.unsigned_sub, word.unsigned_add.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l.
  apply Properties.word.wrap_unsigned.
Qed.

From coqutil Require Import Z.div_mod_to_equations.

Local Existing Instance BasicC64Semantics.parameters.

Monomorphic Definition word__monomorphic_ring_theory := Properties.word.ring_theory.
Add Ring word_ring : word__monomorphic_ring_theory.

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


Axiom __mem_ok : map.ok mem. Local Existing Instance __mem_ok.


Local Unset Simplex. (* COQBUG(9615) *)
Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  pose proof __mem_ok.
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
    rename H3 into length_rep. subst br. subst mid.
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { rewrite word__add_sub.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
      rewrite length_rep in *. (* WHY is this necessary for lia? *)
      Z.div_mod_to_equations. Lia.lia. }
    { rewrite word__add_sub.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
      Z.div_mod_to_equations. Lia.lia. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst left. subst x7.
        clear H2 x8 H3 v0.
        repeat ureplace (_ ^- _:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl).
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        replace (\_ (x2 ^- x1 ^- (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- /_ 8))
           with (8 * ((word.unsigned (x2 ^- x1)/8)/2)); cycle 1.
        { (* 8 * (\_ (x2 ^- x1) / 8 / 2) = \_ (x2 ^- x1 ^- (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- /_ 8) *) admit. }
        replace (\_ (x2 ^- x1) / 2 ^ 4 * 2 ^ 3 / 8)
           with (word.unsigned (x2 ^- x1)/8/2); cycle 1.
        { rewrite Z.div_mul by discriminate. clear. Z.div_mod_to_equations. Lia.lia. }
        rewrite length_rep, (Z.mul_comm 8 (Z.of_nat _)), Z.div_mul by discriminate; f_equal.
        clear. 
        (* Z and nat ... *)
        change 2 with (Z.of_nat 2); rewrite <-div_Zdiv by discriminate; rewrite ?Nat2Z.id; f_equal.
        (* list manipulation... *)
        unshelve erewrite (_ : forall xs, Datatypes.length (List.tl xs) = pred (Datatypes.length xs)).
        { intros l. destruct l. { reflexivity. } { reflexivity. } }
        unshelve erewrite (_ : forall xs delta, Datatypes.length (List.skipn delta xs) = (Datatypes.length xs - delta)%nat).
        { admit. }
        pattern (Datatypes.length x); set (n := Datatypes.length x); clearbody n; cbv beta; clear.
        (*  forall n, (n / 2)%nat = Init.Nat.pred (n - n / 2) *) admit. }
      { subst v'. subst v. subst x7.
        set (\_ (x1 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- x1) / \_ (/_ 8)) as X.
        assert (X < Z.of_nat (Datatypes.length x)). {
          eapply Z.div_lt_upper_bound; [exact eq_refl|].
          rewrite word__add_sub.
          repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
          rewrite length_rep in *. (* WHY does lia need this? *)
          revert H5. clear. intros. Z.div_mod_to_equations. Lia.lia. }
        clearbody X.
        unshelve erewrite (_ : forall xs, Datatypes.length xs <> 0%nat ->
                                          Datatypes.length (List.tl xs) = pred (Datatypes.length xs)). {
          intros l. destruct l. { contradiction. } { reflexivity. } }
        { assert ((Datatypes.length (List.skipn (Z.to_nat X) x) <= Datatypes.length x)%nat) by admit. (* length_skipn_le? *)
          rewrite length_rep in *; Lia.lia. }
        { (* skipn with less than all elements returns a nonempty list *) admit. } }
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H7.
      { rewrite word__add_sub.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. Lia.lia. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. Lia.lia. }
      { rewrite word__add_sub.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. Lia.lia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst right. subst x7.
        repeat ureplace (_ ^- _:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl).
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite List.firstn_length_le; cycle 1.
        { assert (Datatypes.length x <> 0)%nat by Lia.lia.
          revert H14. clear. intros. Z.div_mod_to_equations; zify; rewrite Z2Nat.id by Lia.lia; Lia.lia. }
        rewrite Z2Nat.id by (clear; Z.div_mod_to_equations; Lia.lia).
        clear. Z.div_mod_to_equations. Lia.lia. }
      { subst v. subst v'. subst x7.
        repeat ureplace (_ ^- _:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl).
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        assert (Datatypes.length x <> 0)%nat by Lia.lia.
        rewrite List.firstn_length_le; cycle 1.
        { revert H13. clear. intros. Z.div_mod_to_equations; zify; rewrite Z2Nat.id by Lia.lia; Lia.lia. }
        revert H13. clear. zify. rewrite Z2Nat.id; (Z.div_mod_to_equations; Lia.lia). }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H7.
      { rewrite word__add_sub.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. Lia.lia. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. Lia.lia. }
      { rewrite word__add_sub.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. Lia.lia. }
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
Admitted.
Local Set Simplex.