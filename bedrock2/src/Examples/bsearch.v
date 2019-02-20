Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

  (** Bounds propagation *)

  Lemma Z__range_add a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1)
        : a0+b0 <= a+b < a1 + b1 - 1.
  Proof. Lia.nia. Qed.
  Lemma Z__range_sub a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1)
        : a0-b1+1 <= a-b < a1 - b0.
  Proof. Lia.nia. Qed.
  Lemma Z__range_div_pos_const_r n0 n n1 (Hn : n0 <= n < n1) d (Hd : 0 < d)
    : n0/d <= n/d < n1/d + 1.
  Proof. Z.div_mod_to_equations. Lia.nia. Qed.
  Lemma Z__range_mul_nonneg a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1) (Ha0 : 0 <= a0) (Hb0 : 0 <= b0)
        : a0*b0 <= a*b < (a1-1)*(b1-1) + 1.
  Proof. Lia.nia. Qed.
  Lemma boundscheck {x0 x x1} (H: x0 <= x < x1) {X0 X1} (Hcheck : andb (X0 <=? x0) (x1 <=? X1) = true) : X0 <= x < X1.
  Proof. eapply andb_prop in Hcheck; case Hcheck; intros H1 H2; eapply Z.leb_le in H1; eapply Z.leb_le in H2. Lia.lia. Qed.
  Lemma boundscheck_lt {x0 x x1} (H: x0 <= x < x1) {X1} (Hcheck: Z.ltb x1 X1 = true) : x < X1.
  Proof. eapply Z.ltb_lt in Hcheck. Lia.lia. Qed.
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
    | Z.ones ?x => requireZcstExpr x
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
      | Z.div ?a ?b => (* TODO: non-constant denominator? *)
        let __ := match constr:(Set) with _ => requireZcstExpr b end in
        let Ha := rbounded a in
        named_pose_proof (zbsimp! (Z__range_div_pos_const_r _ a _ Ha b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
      | Z.modulo ?a ?b => (* TODO: non-constant denominator? *)
        let __ := match constr:(Set) with _ => requireZcstExpr b end in
        named_pose_proof (zbsimp! (Z.mod_pos_bound a b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
      | ?op ?a ?b =>
        let Ha := rbounded a in
        let Hb := rbounded b in
        let a0 := match type of Ha with ?a0 <= _ < ?a1 => a0 end in
        let a1 := match type of Ha with ?a0 <= _ < ?a1 => a1 end in
        let b0 := match type of Hb with ?b0 <= _ < ?b1 => b0 end in
        let b1 := match type of Hb with ?b0 <= _ < ?b1 => b1 end in
        match op with
        | Z.add => named_pose_proof (zbsimp! (Z__range_add a0 a a1 Ha b0 b b1 Hb : a0 + b0 <= e < a1 + b1 - 1))
        | Z.sub => named_pose_proof (zbsimp! (Z__range_sub a0 a a1 Ha b0 b b1 Hb : a0-b1+1 <= e < a1-b0))
        | Z.mul => named_pose_proof (zbsimp! (Z__range_mul_nonneg a0 a a1 Ha b0 b b1 Hb (Zle_bool_imp_le 0 a0 eq_refl) (Zle_bool_imp_le 0 b0 eq_refl) : _ <= e < _))
        (* TODO: pow *)
        (* TODO: and, or, xor, ndn *)
        end
      end
    | _ =>
      let __ := match constr:(Set) with _ => requireZcstExpr re end in
      constr:(zbsimp! (bounded_constant e))
    end.

  (** Abstract interpretation *)

  Module unsigned.

  Definition absint_eq {T} := @eq T.
  Local Infix "=~>" := absint_eq (at level 70, no associativity).
    
  Local Notation "absint_lemma! pf" := (ltac:(
    cbv [absint_eq] in *;
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
  Definition absint_add (x y : word.rep) ux Hx uy Hy Hbounds : word.unsigned _ =~> _ :=
    absint_lemma! (word.unsigned_add x y).
  Definition absint_sub (x y : word.rep) ux Hx uy Hy Hbounds : word.unsigned _ =~> _ :=
    absint_lemma! (word.unsigned_sub x y).
  Definition absint_mul (x y : word.rep) ux Hx uy Hy Hbounds : word.unsigned _ =~> _ :=
    absint_lemma! (word.unsigned_mul x y).
  Definition absint_and (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_and_nowrap x y).
  Definition absint_or (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_or_nowrap x y).
  Definition absint_xor (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_xor_nowrap x y).
  Definition absint_ndn (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_ndn_nowrap x y).
  Definition absint_sru (x y : word.rep) ux Hx uy Hy Hshift  : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_sru_nowrap x y).
  Definition absint_slu (x y : word.rep) ux Hx uy Hy Hrange Hshift : word.unsigned _ =~> _ :=
    absint_lemma! (word.unsigned_slu x y).
  Definition absint_divu (x y : word.rep) ux Hx uy Hy Hnz  : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_divu_nowrap x y).
  Definition absint_modu (x y : word.rep) ux Hx uy Hy Hnz  : word.unsigned _ =~> _ :=
    absint_lemma! (Properties.word.unsigned_modu_nowrap x y).

  Ltac named_pose_asfresh_or_id x n :=
    let y := match constr:(Set) with _ => named_pose_asfresh x n | _ => x end in
    y.

  Definition absint_eq_refl {T} v := ((@eq_refl T v) : @absint_eq T v v).
  Ltac zify_expr e :=
    let re := rdelta e in
    lazymatch type of e with
    | @word.rep ?width ?word_parameters =>
      match re with
      | _ => match goal with H: word.unsigned e =~> _ |- _ => H end
      | word.of_Z ?a =>
        let Ba := rbounded a in
        named_pose_proof (absint_of_Z a (boundscheck (X0:=0) (X1:=2^width) Ba (eq_refl true)) : @absint_eq Z (@word.unsigned _ word_parameters e) a)
      | ?op ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        match op with
        | word.and =>
          named_pose_proof constr:(absint_and a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.land Ra Rb))
        | word.or =>
          named_pose_proof constr:(absint_or a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lor Ra Rb))
        | word.xor =>
          named_pose_proof constr:(absint_xor a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lxor Ra Rb))
        | word.ndn =>
          named_pose_proof constr:(absint_ndn a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.ldiff Ra Rb))

        | word.add =>
          let Re := named_pose_asfresh_or_id constr:(Ra+Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_add a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.sub =>
          let Re := named_pose_asfresh_or_id constr:(Ra-Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_sub a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.mul =>
          let Re := named_pose_asfresh_or_id constr:(Ra*Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_mul a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)

        | word.sru =>
          let Re := named_pose_asfresh_or_id constr:((Ra / 2^Rb)) e in
          let Bb := rbounded Rb in
          let pf := constr:(absint_sru a b Ra Ha Rb Hb (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re) in
          named_pose_proof pf
        | word.slu =>
          let Re := named_pose_asfresh_or_id constr:((Ra * 2^Rb)) e in
          let Bb := rbounded Rb in
          let Be := rbounded Re in
          named_pose_proof (absint_slu a b Ra Ha Rb Hb (boundscheck (X0:=0) (X1:=2^width) Be (eq_refl true)) (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | _ => (* unknown binop or bad bounds, don't backtrack to keep Ha and Hb *)
          constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))
         (* TODO: divu, modu (how do we prove denominator nonzero?) *)
        end
      | _ =>
        constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))
      end
    | Z =>
      match e with
      | _ => match goal with H: e =~> _ |- _ => H end
      | word.unsigned ?a => zify_expr a
      | _ => constr:(@absint_eq_refl Z e)
      end
    end.
  End unsigned.
  
  Import unsigned.





  Strategy -1000 [word parameters].
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
    rename H3 into length_rep. subst br. subst v0.
    cbn [interp_binop] in *.
    seprewrite @array_address_inbounds.
    all: (* if expression *) [> ..|exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { rewrite word__add_sub.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
      rewrite length_rep in *. (* WHY is this necessary for lia? *)
      Z.div_mod_to_equations. Lia.lia. }
    { rewrite word__add_sub.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
      Z.div_mod_to_equations. Lia.lia. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split. 1: repeat straightline.
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v1; subst x7. SeparationLogic.ecancel_assumption. }
      { cbn [interp_binop] in *.
        lazymatch goal with |- word.unsigned ?e = _ => let H := unsigned.zify_expr e in idtac H end.
        subst v1; subst x7. subst v0.
        repeat ureplace (_:word) by (set_evars; progress ring_simplify; subst_evars; exact eq_refl).
        rewrite H13.
        unshelve erewrite (_ : forall xs, Datatypes.length xs <> 0%nat -> Datatypes.length (List.tl xs) = pred (Datatypes.length xs)). admit.
        unshelve erewrite (_ : forall xs delta, (Datatypes.length xs > delta)%nat -> Datatypes.length (List.skipn delta xs) = (Datatypes.length xs - delta)%nat). admit.
        unshelve erewrite (_ : forall n, n <> O -> Z.of_nat (Init.Nat.pred n) = Z.of_nat n - 1). { clear. intros. Lia.lia. }
        rewrite Nat2Z.inj_sub, Z2Nat.id.
        rewrite word.unsigned_sub, Z.mod_small.
        rewrite word.unsigned_sub, Z.mod_small.
        rewrite H12.
        setoid_rewrite H13.
        setoid_rewrite length_rep.
        change (2^4) with 16.
        rewrite Z.div_mul by discriminate.
        Lia.lia.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit. }
      { subst v'; subst v. subst x7. admit. }

      cbn [interp_binop] in *.
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
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { cbn [interp_binop] in *. subst v1; subst x7; subst x8. SeparationLogic.ecancel_assumption. }
      { admit. }
      { subst v. subst v'. subst x7. admit. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H7.
      1: admit. 1: admit. 1: exact eq_refl.
      SeparationLogic.ecancel_assumption. } }

  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  all:fail "remaining subgoals".
Admitted.
