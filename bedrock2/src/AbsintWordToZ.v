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

    Lemma absint_of_Z (x : Z) (Hrange : 0 <= x < 2^width) : word.unsigned (word.of_Z x) = x.
    Proof. rewrite word.unsigned_of_Z; unfold word.wrap; rewrite Z.mod_small; trivial. Qed.
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
  End WithWord.

  Ltac named_pose_asfresh_or_id x n :=
    let y := match constr:(Set) with _ => named_pose_asfresh x n | _ => x end in
    y.
  
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
