Require Import Coq.Strings.String Coq.ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties.
From coqutil Require Import Tactics.rdelta Z.div_mod_to_equations.
Require Import coqutil.Z.Lia.
Local Open Scope Z_scope.

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
Proof. eapply andb_prop in Hcheck; case Hcheck; intros H1 H2; eapply Z.leb_le in H1; eapply Z.leb_le in H2. blia. Qed.
Lemma boundscheck_lt {x0 x x1} (H: x0 <= x < x1) {X1} (Hcheck: Z.ltb x1 X1 = true) : x < X1.
Proof. eapply Z.ltb_lt in Hcheck. blia. Qed.
Lemma bounded_constant c : c <= c < c+1. Proof. blia. Qed.

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

Ltac named_pose_asfresh_or_id x n :=
  let y := match constr:(Set) with _ => named_pose_asfresh x n | _ => x end in
  y.

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
  | Z.log2 ?x => requireZcstExpr x
  | Z.log2_up ?x => requireZcstExpr x
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

Definition absint_eq {T} := @eq T.
Definition absint_eq_refl {T} v := ((@eq_refl T v) : @absint_eq T v v).
Local Infix "=~>" := absint_eq (at level 70, no associativity).

Module unsigned.
  Section WithWord.
    Context {width : Z} {word : word.word width} {word_ok : word.ok word}.
    Local Notation "absint_lemma! pf" := (ltac:(
      cbv [absint_eq] in *;
      etransitivity; [ eapply pf | ]; cycle -1;
        [unshelve (repeat match goal with
          | |- _ => progress unfold word.wrap in *
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

    Definition absint_add (x y : word.rep) ux Hx uy Hy Hbounds : _ =~> _ :=
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
    Implicit Types (x y : word).
    (* TODO use it *)
    Lemma absint_opp x (ux: Z) (Hx: word.unsigned x = ux) (Hnz: ux <> 0):
      word.unsigned (word.opp x) =~> 2^width - ux.
    Proof.
      rewrite word.unsigned_opp. cbv [word.wrap].
      rewrite Z_mod_nz_opp_full.
      - rewrite Z.mod_small; [rewrite Hx; reflexivity|]. apply word.unsigned_range.
      - rewrite Z.mod_small; [rewrite Hx; apply Hnz|]. apply word.unsigned_range.
    Qed.

    Lemma absint_mask_r x y ux (Hx : word.unsigned x = ux) uy (Hy : word.unsigned y = uy) (Huy : uy = Z.ones (Z.log2 uy+1)):
       word.unsigned (word.and x y) =~> Z.modulo ux (uy+1).
    Proof.
      etransitivity; [eapply absint_and; eauto|].
      rewrite Huy.
      rewrite Z.land_ones, Z.ones_equiv; repeat (eapply f_equal2 || blia).
      enough (Z.log2 0 <= Z.log2 uy) by (change (Z.log2 0) with 0 in *; blia).
      eapply Z.log2_le_mono; subst uy; eapply word.unsigned_range.
    Qed.
    Lemma absint_mask_l y x uy (Hy : word.unsigned y = uy) ux (Hx : word.unsigned x = ux) (Huy : uy = Z.ones (Z.log2 uy+1)):
       word.unsigned (word.and y x) =~> Z.modulo ux (uy+1).
    Proof.
      etransitivity; [eapply absint_and; eauto|].
      rewrite Z.land_comm.
      rewrite Huy.
      rewrite Z.land_ones, Z.ones_equiv; repeat (eapply f_equal2 || blia).
      enough (Z.log2 0 <= Z.log2 uy) by (change (Z.log2 0) with 0 in *; blia).
      eapply Z.log2_le_mono; subst uy; eapply word.unsigned_range.
    Qed.
  End WithWord.

  Ltac zify_expr e :=
    let re := rdelta e in
    lazymatch type of e with
    | @word.rep ?width ?word_parameters =>
      match re with
      | _ => match goal with H: word.unsigned e =~> _ |- _ => H end
      | word.of_Z ?a =>
        let Ba := rbounded a in
        named_pose_proof (word.unsigned_of_Z_nowrap a (boundscheck (X0:=0) (X1:=2^width) Ba (eq_refl true)) : @absint_eq Z (@word.unsigned _ word_parameters e) a)
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_r a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Ra (Rb+1)))
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_l a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Rb (Ra+1)))
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

Require coqutil.Word.Naive.
Module absint_test.
  Import Word.Naive.
  Fixpoint goal (x : word32) (n : nat) : Prop
    := match n with
       | O => True
       | S n' => let x := word.add x x in goal x n'
       end.
  Goal forall x X, 1 <= X < 2^60 -> absint_eq (word.unsigned x) X -> goal x 7.
  Proof.
    cbv beta iota delta [goal].
    intros.

    let e := match goal with x := _ |- _ => x end in
    let e := constr:(word.ndn (word.xor (word.or (word.and (word.sub (word.mul (word.slu (word.sru e (word.of_Z 16)) (word.of_Z 3)) x) x) x) x) x) x) in
    let H := unsigned.zify_expr e in
    idtac H.


   clear.
   assert (x3 : word32) by exact (word.of_Z 0).
  let e :=
    constr:(
word.unsigned
  (word.add
     (word.add
        (word.sru
           (word.add
              (word.and (word.sru x3 (word.of_Z 16)) (word.of_Z 16383))
              (word.of_Z 3)) (word.of_Z 2))
        (word.sru
           (word.add
              (word.and (word.sru x3 (word.of_Z 16)) (word.of_Z 16383))
              (word.of_Z 3)) (word.of_Z 2)))
     (word.add
        (word.sru
           (word.add
              (word.and (word.sru x3 (word.of_Z 16)) (word.of_Z 16383))
              (word.of_Z 3)) (word.of_Z 2))
        (word.sru
           (word.add
              (word.and (word.sru x3 (word.of_Z 16)) (word.of_Z 16383))
              (word.of_Z 3)) (word.of_Z 2))))) in
     let H := unsigned.zify_expr e in
     idtac H;
     repeat match goal with H:?x =~> ?x |- _ => clear H end.

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
