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

  From coqutil Require Import Z.div_mod_to_equations.
  From coqutil.Tactics Require Import rdelta.

  (** Bounds propagation *)

  Lemma Z__range_add a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1)
        : a0+b0 <= a+b < a1 + b1 - 1.
  Proof. Lia.nia. Qed.
  Lemma Z__range_div_pos_const_r n0 n n1 (Hn : n0 <= n < n1) d (Hd : 0 < d)
    : n0/d <= n/d < n1/d + 1.
  Proof. Z.div_mod_to_equations. Lia.nia. Qed.
  Lemma Z__range_mul_nonneg a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1) (Ha0 : 0 <= a0) (Hb0 : 0 <= b0)
        : a0*b0 <= a*b < (a1-1)*(b1-1) + 1.
  Proof. Lia.nia. Qed.
  Lemma boundscheck {x0 x x1} (H: x0 <= x < x1) {X0 X1} (Hcheck : andb (X0 <=? x0) (x1 <=? X1) = true) : X0 <= x < X1.
  Proof. eapply andb_prop in Hcheck; case Hcheck; intros H1 H2; eapply Z.leb_le in H1; eapply Z.leb_le in H2. Lia.lia. Qed.
  Lemma boundscheck_lt {x0 x x1} (H: x0 <= x < x1) {X1} (Hcheck: Z.leb x1 X1 = true) : x < X1.
  Proof. eapply Z.leb_le in Hcheck. Lia.lia. Qed.
  Lemma bounded_constant c : c <= c < c+1. Proof. Lia.lia. Qed.

  Ltac named_pose_proof pf :=
    let H := fresh in
    let __ := match constr:(Set) with _ => pose proof pf as H end in
    H.
  Ltac named_pose pf :=
    let H := fresh in
    let __ := match constr:(Set) with _ => pose pf as H end in
    H.
  Ltac named_pose_asfresh pf x :=
    let H := fresh x in
    let __ := match constr:(Set) with _ => pose pf as H end in
    H.

  Ltac requireZcst z :=
    lazymatch Coq.setoid_ring.InitialRing.isZcst z with
    | true => idtac
    end.
  Ltac requireZcstExpr e :=
    match e with
    | Z.pred ?x => requireZcstExpr x
    | Z.succ ?x => requireZcstExpr x
    | Z.opp ?x => requireZcstExpr x
    | Z.lnot ?x => requireZcstExpr x
    | Z.add ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.sub ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.mul ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.div ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.modulo ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.quot ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.rem ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.pow ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.shiftl ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.shiftr ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.land ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.lor ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.lxor ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.ldiff ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.clearbit ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.setbit ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.min ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.max ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.gcd ?x ?y => requireZcstExpr x; requireZcstExpr y
    | Z.lcm ?x ?y => requireZcstExpr x; requireZcstExpr y
    | _ => requireZcst e
    end.

  Ltac zsimp x :=
    match constr:(Set) with
    | _ => let __ := requireZcstExpr x in let y := eval cbv in x in y
    | _ => x
    end.

  Local Notation "zbsimp! H" :=
    (ltac:(
       lazymatch type of H with
             ?L <= ?X < ?R =>
             let L := zsimp L in
             let R := zsimp R in
             exact ((H : L <= X < R))
           end
    )) (at level 10, only parsing).
  
  Ltac rbounded e :=
    let re := rdelta e in
    match goal with
    | H :  _ <= e < _ |- _ => H
    | _ =>
      match re with
      | word.unsigned ?a =>
        named_pose_proof (zbsimp! (Properties.word.unsigned_range a : _ <= e < _))
      | Z.add ?a ?b =>
        let Ha := rbounded a in
        let Hb := rbounded b in
        named_pose_proof (zbsimp! (Z__range_add _ a _ Ha _ b _ Hb : _ <= e < _))
      | Z.mul ?a ?b =>
        let Ha := rbounded a in
        let Hb := rbounded b in
        named_pose_proof (zbsimp! (Z__range_mul_nonneg _ a _ Ha _ b _ Hb ltac:(eapply Z.leb_le; exact eq_refl) ltac:(eapply Z.leb_le; exact eq_refl) : _ <= e < _))
      | Z.div ?a ?b =>
        let __ := match constr:(Set) with _ => requireZcstExpr b end in
        let Ha := rbounded a in
        named_pose_proof (zbsimp! (Z__range_div_pos_const_r _ a _ Ha b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
      | Z.modulo ?a ?b =>
        let __ := match constr:(Set) with _ => requireZcst b end in
        named_pose_proof (zbsimp! (Z.mod_pos_bound a b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
      end
    | _ =>
      let __ := match constr:(Set) with _ => requireZcstExpr re end in
      constr:(zbsimp! (bounded_constant e))
    end.

  (** Abstract interpretation *)
    
  Notation "absint_lemma! pf" := (ltac:(
    etransitivity; [ eapply pf | ]; cycle -1;
      [unshelve (repeat match goal with
        | |-context [Z.shiftr ?x (word.unsigned ?y)] => assert_fails(is_evar x||is_evar y);
          setoid_rewrite (Z.shiftr_div_pow2 x (word.unsigned y) (proj1 (Properties.word.unsigned_range _)))
        | |-context [Z.shiftl ?x (word.unsigned ?y)] => assert_fails(is_evar x||is_evar y);
          setoid_rewrite (Z.shiftl_mul_pow2 x (word.unsigned y) (proj1 (Properties.word.unsigned_range _)))
        | |-context [?x mod (2^?y)] => assert_fails(is_evar x||is_evar y);
          rewrite (Z.mod_small x (2^y)) by shelve
        | |-context [word.unsigned ?x] => assert_fails(is_evar x);
          erewrite (_:word.unsigned _=_) by shelve
        end; exact eq_refl)
      |..];
      (* WHY do I need [> here? *)
      [> (repeat match goal with
                 | H: ?P |- ?G => assert_fails (has_evar P || has_evar G); rewrite H
                 end;
          match reverse goal with H : ?e |- ?G => is_evar e; unify e G; exact H end).. ]
    )) (at level 10, only parsing).
  
  Lemma absint_of_Z (x : Z) (Hrange : 0 <= x < 2^width) : word.unsigned (word.of_Z x) = x.
  Proof. rewrite word.unsigned_of_Z, Z.mod_small; trivial. Qed.
  Definition absint_add (x y : word.rep) ux Hx uy Hy Hbounds : _ = _ :=
    absint_lemma! (word.unsigned_add x y).
  Definition absint_sub (x y : word.rep) ux Hx uy Hy Hbounds : _ = _ :=
    absint_lemma! (word.unsigned_sub x y).
  Definition absint_and (x y : word.rep) ux Hx uy Hy : _ = _ :=
    absint_lemma! (Properties.word.unsigned_and_nowrap x y).
  Definition absint_or (x y : word.rep) ux Hx uy Hy : _ = _ :=
    absint_lemma! (Properties.word.unsigned_or_nowrap x y).
  Definition absint_xor (x y : word.rep) ux Hx uy Hy : _ = _ :=
    absint_lemma! (Properties.word.unsigned_xor_nowrap x y).
  Definition absint_ndn (x y : word.rep) ux Hx uy Hy : _ = _ :=
    absint_lemma! (Properties.word.unsigned_ndn_nowrap x y).
  Definition absint_mul (x y : word.rep) ux Hx uy Hy Hbounds : _ = _ :=
    absint_lemma! (word.unsigned_mul x y).
  Definition absint_sru (x y : word.rep) ux Hx uy Hy Hshift  : _ = _ :=
    absint_lemma! (Properties.word.unsigned_sru_nowrap x y).
  Definition absint_divu (x y : word.rep) ux Hx uy Hy Hshift  : _ = _ :=
    absint_lemma! (Properties.word.unsigned_divu_nowrap x y).
  Definition absint_modu (x y : word.rep) ux Hx uy Hy Hnz  : _ = _ :=
    absint_lemma! (Properties.word.unsigned_modu_nowrap x y).
  Definition absint_slu (x y : word.rep) ux Hx uy Hy Hrange Hshift : _ = _ :=
    absint_lemma! (word.unsigned_slu x y).

  Definition absint_eq {T} := @eq T.
  Local Infix "=~>" := absint_eq (at level 70, no associativity).
  
  Ltac absint e :=
    let re := rdelta e in
    lazymatch type of e with
    | word.rep =>
      match re with
      | _ => match goal with H: word.unsigned e =~> _ |- _ => H end
      | word.of_Z ?a =>
        let Ba := rbounded a in
        named_pose_proof (absint_of_Z a (boundscheck (X0:=0) (X1:=2^width) Ba (eq_refl true)))
      | word.add ?a ?b =>
        let Ha := absint a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := absint b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        let Re := constr:(Ra+Rb) in
        let Re := match e with re => Re | _ => named_pose_asfresh Re e end in
        let Be := rbounded Re in
        named_pose_proof (absint_add a b Ra Ha Rb Hb (boundscheck (X0:=0) (X1:=2^width) Be (eq_refl true)) : word.unsigned e =~> Re)
      | word.sru ?a ?b =>
        let Ha := absint a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := absint b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        let Bb := rbounded Rb in
        named_pose_proof (absint_sru a b Ra Ha Rb Hb (@boundscheck_lt _ Rb _ Bb width eq_refl))
      | word.slu ?a ?b =>
        let Ha := absint a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := absint b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        let Bb := rbounded Rb in
        let Re := constr:((Ra * 2^Rb)) in
        let Be := rbounded Re in
        named_pose_proof (absint_slu a b Ra Ha Rb Hb (boundscheck (X0:=0) (X1:=2^width) Be (eq_refl true)) (@boundscheck_lt _ Rb _ Bb width eq_refl))
      | _ =>
        (* let __ := match constr:(Set) with _ => idtac "ABSINT PASSTHROUGH WORD" e end in *)
        constr:((eq_refl (word.unsigned e)) : _ =~> _)
      end
    | Z =>
      match e with
      | _ => match goal with H: e =~> _ |- _ => H end
      | word.unsigned ?a =>
        absint a
      | Z.modulo ?a ?b =>
        let Ha := absint a in
        let Hb := absint b in
        named_pose_proof (f_equal2 Z.modulo Ha Hb)
      | _ =>
        (* let __ := match constr:(Set) with _ => idtac "ABSINT PASSTHROUGH Z" e end in *)
        constr:((eq_refl e) : _ =~> _)
      end
    end.

  Goal forall x, 0 <= word.unsigned x < 5 ->
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   let x := x^+x in
                   True.
  Proof.
    intros.

    Set Ltac Profiling.
    let e := match goal with x := _ |- _ => x end in
    let H := absint e in
    idtac H.


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
  Abort.

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
      { subst v'; subst v. subst x7. admit. }

      rename H3 into length_rep.

      cbn [interp_binop] in *.
      subst br.
      rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_eq_0_iff in H5.

      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H8.

      1,2: repeat match goal with H: sep _ _ _ |- _ => clear H end.

      { cbn [interp_binop] in *.
        subst v0.

        rewrite word__add_sub.

        let e := constr:(((x2 ^- x1) ^>> /_ 4 ^<< /_ 3)) in
        let H := absint e in
        setoid_rewrite H.

        let e := constr:(/_ 8) in
        let H := absint e in
        setoid_rewrite H.

        rewrite (Z.mul_comm (Z.of_nat _) 8), <-length_rep.
        rewrite word.unsigned_sub.

        pose proof Properties.word.unsigned_range x1.
        pose proof Properties.word.unsigned_range x2.

        change (2^4) with 16.
        change (2^width) with 18446744073709551616 in *.
        clear -H5 H12 H13. Z.div_mod_to_equations; Lia.lia.
      }
      { cbn [interp_binop] in *.
        subst v0.

        clear. Z.div_mod_to_equations. Lia.lia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v1; subst x7; subst x8. SeparationLogic.ecancel_assumption. }
      { admit. }
      { subst v. subst v'. subst x7. admit. }
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
