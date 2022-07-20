Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Tactics.forward coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.
From coqutil Require Import destr div_mod_to_equations.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Section KamiWordFacts.

  (* compatibility code for Coq 8.14 *)
  Fact Znat_N2Z_inj_mod : forall n m : N, m <> 0%N -> Z.of_N (n mod m) = Z.of_N n mod Z.of_N m.
  Proof. intros. now apply Znat.N2Z.inj_mod. Qed.

  Lemma wordToN_split2 a b w :
    wordToN (@split2 a b w) = BinNat.N.div (wordToN w) (NatLib.Npow2 a).
  Proof.
    pose proof wordToNat_split2 a b w as HH.
    eapply Nnat.Nat2N.inj_iff in HH.
    rewrite wordToN_nat, HH; f_equal; clear HH.
    rewrite wordToN_nat, NatLib.pow2_N.
    generalize (#w); intro.
    specialize (NatLib.zero_lt_pow2 a).
    generalize (NatLib.pow2 a); intros.
    pose proof Zdiv.div_Zdiv n n0 ltac:(blia).
    pose proof Znat.N2Z.inj_div (BinNat.N.of_nat n) (BinNat.N.of_nat n0).
    rewrite Znat.nat_N_Z in *.
    blia.
  Qed.

  Lemma wmsb_split2 a b w x y (H:b <> 0%nat)
    : wmsb (split2 a b w) x = wmsb w y.
  Proof.
    intros.
    rewrite <-(combine_split a b w) at 2.
    erewrite wmsb_combine by trivial.
    reflexivity.
  Qed.

  Lemma wordToZ_split2 a b w (H:b <> 0%nat)
    : wordToZ (@split2 a b w) = Z.div (wordToZ w) (2^Z.of_nat a).
  Proof.
    rewrite 2wordToZ_wordToN.
    rewrite wordToN_split2.
    erewrite wmsb_split2; [instantiate (1:=false)|trivial].
    case (wmsb w).
    all: rewrite ?Znat.N2Z.inj_div.
    all: rewrite <-?Znat.N_nat_Z, ?NatLib.Npow2_nat, ?N_Z_nat_conversions.Nat2Z.inj_pow.
    2: setoid_rewrite Z.add_0_r; trivial.
    rewrite ?Znat.Nat2Z.inj_add, ?Z.pow_add_r by blia.
    rewrite Z.mul_comm.
    symmetry.
    rewrite <-Z.add_opp_r, Zopp_mult_distr_l.
    rewrite Zdiv.Z_div_plus.
    1: reflexivity.
    eapply Z.lt_gt.
    eapply Z.pow_pos_nonneg; blia.
  Qed.

  Lemma wordToN_wones_ones:
    forall sz, wordToN (wones sz) = BinNat.N.ones (BinNat.N.of_nat sz).
  Proof.
    intros.
    rewrite wordToN_nat.
    rewrite wones_pow2_minus_one.
    rewrite Nnat.Nat2N.inj_sub, BinNat.N.sub_1_r.
    rewrite <-NatLib.pow2_N.
    cbv [BinNat.N.ones]; rewrite BinNat.N.shiftl_1_l.
    f_equal.
    apply Znat.N2Z.inj.
    rewrite NatLib.Z_of_N_Npow2, Znat.N2Z.inj_pow, Znat.nat_N_Z.
    reflexivity.
  Qed.

  Lemma uwordToZ_wplus_distr:
    forall sz (x y: Word.word sz),
      Z.of_N (wordToN (x ^+ y)) = (Z.of_N (wordToN x) + Z.of_N (wordToN y)) mod 2 ^ (Z.of_nat sz).
  Proof.
    intros.
    cbv [wplus wordBin].
    rewrite wordToN_NToWord_eqn, Znat_N2Z_inj_mod, Znat.N2Z.inj_add, NatLib.Z_of_N_Npow2.
    2: apply NatLib.Npow2_not_zero.
    f_equal; f_equal; blia.
  Qed.

  Lemma wnot_idempotent:
    forall {sz} (w: word sz),
      wnot (wnot w) = w.
  Proof.
    induction w; cbn; rewrite ?IHw, ?Bool.negb_involutive; eauto.
  Qed.

  Lemma wordToN_eq_rect:
    forall sz (w: Word.word sz) nsz Hsz,
      wordToN (eq_rect _ Word.word w nsz Hsz) = wordToN w.
  Proof.
    intros; subst; simpl; reflexivity.
  Qed.

  Lemma Z_pow_add_lor:
    forall n m p: Z,
      0 <= n < 2 ^ p -> 0 <= m -> 0 <= p ->
      (n + 2 ^ p * m)%Z = Z.lor n (2 ^ p * m).
  Proof.
    intros.
    apply eq_sym, BitOps.or_to_plus.
    rewrite Z.mul_comm, <-Z.shiftl_mul_pow2 by assumption.
    replace n with (Z.land n (Z.ones p)).
    - bitblast.Z.bitblast.
      rewrite Z.testbit_neg_r with (n:= l) by blia.
      apply Bool.andb_false_r.
    - destruct (Z.eq_dec n 0); [subst; apply Z.land_0_l|].
      assert (0 < n) by blia.
      rewrite Z.land_ones_low; [reflexivity|blia|].
      apply Z.log2_lt_pow2; blia.
  Qed.

  Lemma Z_of_wordToN_combine_alt:
    forall sz1 (w1: Word.word sz1) sz2 (w2: Word.word sz2),
      Z.of_N (wordToN (Word.combine w1 w2)) =
      Z.lor (Z.of_N (wordToN w1)) (Z.shiftl (Z.of_N (wordToN w2)) (Z.of_N (BinNat.N.of_nat sz1))).
  Proof.
    intros.
    rewrite wordToN_combine, N2Z.inj_add, N2Z.inj_mul.
    assert (0 <= Z.of_N (wordToN w1) < 2 ^ (Z.of_N (N.of_nat sz1))).
    { split; [apply N2Z.is_nonneg|].
      clear.
      induction w1; [simpl; blia|].
      unfold wordToN; fold wordToN.
      destruct b.
      { rewrite N2Z.inj_succ, N2Z.inj_mul, Nnat.Nat2N.inj_succ.
        rewrite N2Z.inj_succ.
        rewrite Z.pow_succ_r by blia; blia.
      }
      { rewrite N2Z.inj_mul, Nnat.Nat2N.inj_succ.
        rewrite N2Z.inj_succ.
        rewrite Z.pow_succ_r by blia; blia.
      }
    }
    assert (0 <= Z.of_N (wordToN w2)) by blia.
    assert (0 <= Z.of_N (N.of_nat sz1)) by blia.

    replace (Z.of_N (NatLib.Npow2 sz1)) with (Z.pow 2 (Z.of_N (N.of_nat sz1))).
    - generalize dependent (Z.of_N (wordToN w1)).
      generalize dependent (Z.of_N (wordToN w2)).
      generalize dependent (Z.of_N (N.of_nat sz1)).
      intros p ? z1 ? z2 ?.
      rewrite Z.shiftl_mul_pow2 by assumption.
      rewrite Z.mul_comm with (n:= z1).
      apply Z_pow_add_lor; assumption.
    - clear; induction sz1; [reflexivity|].
      rewrite Nnat.Nat2N.inj_succ, N2Z.inj_succ.
      unfold NatLib.Npow2; fold NatLib.Npow2.
      rewrite Z.pow_succ_r by blia; blia.
  Qed.

  Lemma ZToWord_zero:
    forall n, ZToWord n 0 = wzero n.
  Proof.
    destruct n; intros; [shatterer|].
    apply wordToZ_inj.
    rewrite wordToZ_ZToWord.
    - rewrite wordToZ_wzero; reflexivity.
    - split.
      + blia.
      + change 0 with (Z.of_nat 0).
        apply Nat2Z.inj_lt.
        apply NatLib.zero_lt_pow2.
  Qed.

  Lemma combine_wplus_wzero:
    forall sz1 (wb: Word.word sz1) sz2 (w1 w2: Word.word sz2),
      Word.combine wb w1 ^+ Word.combine (wzero sz1) w2 =
      Word.combine wb (w1 ^+ w2).
  Proof.
    induction wb; intros; [reflexivity|].
    simpl; rewrite <-wplus_WS_0.
    rewrite IHwb; reflexivity.
  Qed.

  Lemma split1_wplus_silent:
    forall sz1 sz2 (w1 w2: Word.word (sz1 + sz2)),
      split1 sz1 sz2 w2 = wzero _ ->
      split1 sz1 sz2 (w1 ^+ w2) = split1 sz1 sz2 w1.
  Proof.
    intros.
    pose proof (word_combinable _ _ w1).
    destruct H0 as [w11 [w12 ?]].
    pose proof (word_combinable _ _ w2).
    destruct H1 as [w21 [w22 ?]].
    subst; rewrite split1_combine in H; subst.
    rewrite combine_wplus_wzero.
    do 2 rewrite split1_combine.
    reflexivity.
  Qed.

  Lemma wordToN_split1 a b w :
    wordToN (@split1 a b w) = BinNat.N.modulo (wordToN w) (NatLib.Npow2 a).
  Proof.
    pose proof wordToNat_split1 a b w as HH.
    eapply Nnat.Nat2N.inj_iff in HH.
    rewrite wordToN_nat, HH; f_equal; clear HH.
    rewrite wordToN_nat, NatLib.pow2_N.
    generalize (#w); intro.
    remember (NatLib.pow2 a) as pa eqn:Ha.
    pose proof NatLib.pow2_zero a.
    pose proof mod_Zmod n pa ltac:(blia).
    pose proof Znat_N2Z_inj_mod (BinNat.N.of_nat n) (BinNat.N.of_nat pa) ltac:(blia).
    rewrite Znat.nat_N_Z in *.
    blia.
  Qed.

  Lemma sumbool_rect_weq {T} a b n x y :
    sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
  Proof.
    cbv [sumbool_rect].
    destruct (weq _ _), (weqb _ _) eqn:?;
                                   try match goal with H : _ |- _ => eapply weqb_true_iff in H end;
      trivial; congruence.
  Qed.

  Lemma sumbool_rect_bool_weq n x y :
    sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
  Proof. rewrite sumbool_rect_weq; destruct (weqb x y); trivial. Qed.

  Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
  Proof.
    destruct (Z.eqb_spec (Z.of_N (wordToN x)) (Z.of_N (wordToN y))).
    - apply N2Z.inj, wordToN_inj in e; subst.
      apply eq_sym, weqb_eq; reflexivity.
    - apply eq_sym, weqb_ne.
      intro Hx; subst; auto.
  Qed.

  Lemma unsigned_split1_mod:
    forall n m w,
      Z.of_N (wordToN (split1 n m w)) = Z.of_N (wordToN w) mod (2 ^ (Z.of_nat n)).
  Proof.
    intros.
    rewrite wordToN_split1.
    rewrite N2Z.inj_mod by apply NatLib.Npow2_not_zero.
    rewrite NatLib.Z_of_N_Npow2.
    reflexivity.
  Qed.

End KamiWordFacts.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Z.of_N (wordToN x).
  Definition ksigned: kword -> Z := @wordToZ sz.
  Definition kofZ: Z -> kword := ZToWord sz.

  Definition riscvZdivu(x y: Z): Z :=
    if y =? 0 then 2 ^ width - 1 else Z.div x y.

  Definition riscvZdivs(x y: Z): Z :=
    if (x =? - 2 ^ (width - 1)) && (y =? - 1) then x
    else if y =? 0 then - 1 else Z.quot x y.

  Definition riscvZmodu(x y: Z): Z :=
    if y =? 0 then x else Z.modulo x y.

  Definition riscvZmods(x y: Z): Z :=
    if y =? 0 then x else Z.rem x y.

  Instance word : word.word width := {|
    rep := kword;
    unsigned := kunsigned;
    signed := ksigned;
    of_Z := kofZ;

    add := @wplus sz;
    sub := @wminus sz;
    opp := @wneg sz;

    or  := @wor sz;
    and := @wand sz;
    xor := @wxor sz;
    not := @wnot sz;

    (* "x and not y" *)
    ndn x y := kofZ (Z.ldiff (kunsigned x) (kunsigned y));

    mul := @wmult sz;
    mulhss x y := kofZ (Z.mul (ksigned x) (ksigned y) / 2^width);
    mulhsu x y := kofZ (Z.mul (ksigned x) (kunsigned y) / 2^width);
    mulhuu x y := kofZ (Z.mul (kunsigned x) (kunsigned y) / 2^width);

    divu x y := kofZ (riscvZdivu (kunsigned x) (kunsigned y));
    divs x y := kofZ (riscvZdivs (ksigned x) (ksigned y));
    modu x y := kofZ (riscvZmodu (kunsigned x) (kunsigned y));
    mods x y := kofZ (riscvZmods (ksigned x) (ksigned y));

    (* shifts only look at the lowest 5-6 bits of the shift amount *)
    slu x y := wlshift x (Z.to_nat ((kunsigned y) mod width));
    sru x y := wrshift x (Z.to_nat ((kunsigned y) mod width));
    srs x y := wrshifta x (Z.to_nat ((kunsigned y) mod width));

    eqb := @weqb sz;
    ltu x y := if wlt_dec x y then true else false;
    lts x y := if wslt_dec x y then true else false;

    sextend oldwidth z := kofZ ((kunsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));

  |}.

  Section __.
    Import BinNat Word. Local Open Scope N_scope.

    Lemma wordToN_WS b n w :
      wordToN (@WS b n w) = 2*wordToN w + N.b2n b.
    Proof.
      case b; rewrite ?wordToN_WS_0, ?wordToN_WS_1; cbn [N.b2n].
      all : blia.
    Qed.

    Lemma testbit_wordToN_oob n (a : word n) i (H: Logic.not (i < N.of_nat n)) :
      N.testbit (wordToN a) i = false.
    Proof.
      pose proof wordToN_bound a.
      case (wordToN a) in *; trivial; intros.
      apply N.bits_above_log2, N.log2_lt_pow2; try blia.
      eapply N.lt_le_trans; try apply H0; clear H0.
      eapply Znat.N2Z.inj_le.
      rewrite NatLib.Z_of_N_Npow2, Znat.N2Z.inj_pow; cbn.
      eapply Z.pow_le_mono_r; blia.
    Qed.

    Lemma testbit_wordToN_bitwp_inbounds f n (a b : word n) i (H:i < N.of_nat n) :
      N.testbit (wordToN (bitwp f a b)) i = f (N.testbit (wordToN a) i) (N.testbit (wordToN b) i).
    Proof.
      revert dependent i; revert b; revert a; induction n; intros.
      { blia. }
      case (shatter_word_S a) as (?&?&?) in *; subst a.
      case (shatter_word_S b) as (?&?&?) in *; subst b.
      cbn [bitwp whd].
      rewrite 3wordToN_WS.
      case (N.eq_dec 0 i); intros.
      { subst. rewrite 3N.testbit_0_r; trivial. }
      { rewrite <-(N.succ_pred i) by blia.
        rewrite 3N.testbit_succ_r. eapply IHn. blia. }
    Qed.
  End __.

  Lemma uwordToZ_bitwp f F (F_spec : forall x y i, Z.testbit (F x y) i = f (Z.testbit x i) (Z.testbit y i)) sz (x y : Word.word sz)
    : uwordToZ (bitwp f x y) = (F (uwordToZ x) (uwordToZ y)) mod 2 ^ Z.of_nat sz.
  Proof.
    cbv [uwordToZ].
    eapply Z.bits_inj_iff'; intros.
    case (ZArith_dec.Z_lt_dec n (Z.of_nat sz)); intros.
    2: {
      rewrite Z.mod_pow2_bits_high by blia.
      rewrite ?Z.testbit_of_N' by trivial.
      rewrite testbit_wordToN_oob; trivial.
      intro X.
      eapply Znat.N2Z.inj_lt in X; blia.
    }
    rewrite Z.mod_pow2_bits_low by trivial.
    rewrite F_spec.
    rewrite ?Z.testbit_of_N' by trivial.
    rewrite testbit_wordToN_bitwp_inbounds; trivial.
    eapply Znat.N2Z.inj_lt; blia.
  Qed.

  Instance ok : word.ok word.
  Proof using width_nonneg.
    assert (AA: (0 < sz)%nat) by (eapply (Znat.Z2Nat.inj_lt 0); blia).
    assert (BB: Z.of_nat sz = width) by (rewrite Znat.Z2Nat.id; blia).
    split; trivial.
    all: cbv [rep unsigned signed of_Z add sub opp or and xor not
                  ndn mul mulhss mulhsu mulhuu divu divs modu mods slu sru srs
                  eqb ltu lts sextend word wrap
                  kword kunsigned ksigned kofZ]; intros.

    { pose proof @uwordToZ_ZToWord_full (Z.to_nat width) ltac:(blia).
      replace (Z.of_nat sz) with width in * by blia.
      match goal with H : _ |- _ => eapply H end. }
    { rewrite wordToZ_ZToWord_full; try blia. cbv [swrap].
      replace (Z.of_nat sz) with width in * by blia; trivial. }
    { rewrite ZToWord_Z_of_N, NToWord_wordToN; solve[trivial]. }
    { rewrite uwordToZ_wplus_distr, BB; reflexivity. }
    { cbv [wminus]; rewrite uwordToZ_wplus_distr, BB.
      destruct (BinNat.N.eq_dec (wordToN y) N0).
      { rewrite e.
        rewrite <-wordToN_wzero with (sz:= sz) in e.
        apply wordToN_inj in e; subst.
        rewrite wzero_wneg, wordToN_wzero; reflexivity.
      }
      { rewrite wneg_wordToN by assumption.
        rewrite Znat.N2Z.inj_sub by (pose proof (wordToN_bound y); blia).
        rewrite NatLib.Z_of_N_Npow2, BB.
        replace (Z.of_N (wordToN x) + (2 ^ width - Z.of_N (wordToN y)))
          with (Z.of_N (wordToN x) - Z.of_N (wordToN y) + 1 * 2 ^ width) by blia.
        rewrite Zdiv.Z_mod_plus_full.
        reflexivity.
      }
    }

    { destruct (BinNat.N.eq_dec (wordToN x) N0).
      { rewrite e.
        rewrite <-wordToN_wzero with (sz:= sz) in e.
        apply wordToN_inj in e; subst.
        rewrite wzero_wneg, wordToN_wzero; reflexivity.
      }
      { rewrite wneg_wordToN by assumption.
        rewrite Znat.N2Z.inj_sub by (pose proof (wordToN_bound x); blia).
        rewrite NatLib.Z_of_N_Npow2, BB.
        assert (Hms: Z.of_N (wordToN x) mod 2 ^ (Z.of_nat sz) = Z.of_N (wordToN x)).
        { apply Z.mod_small.
          split; [blia|].
          rewrite <-NatLib.Z_of_N_Npow2.
          apply Znat.N2Z.inj_lt, wordToN_bound.
        }
        rewrite BB in Hms.
        rewrite Zdiv.Z_mod_nz_opp_full by (rewrite Hms; blia).
        rewrite Hms; reflexivity.
      }
    }
    { setoid_rewrite (uwordToZ_bitwp _ _ Z.lor_spec); f_equal; congruence. }
    { setoid_rewrite (uwordToZ_bitwp _ _ Z.land_spec); f_equal; congruence. }
    { setoid_rewrite (uwordToZ_bitwp _ _ Z.lxor_spec); f_equal; congruence. }
    { rewrite wnot_wnot'_equiv. cbv [wnot'].
      setoid_rewrite (uwordToZ_bitwp _ _ Z.lxor_spec).
      rewrite <-Z.lxor_m1_l.
      pose proof uwordToZ_bound x.
      change (Z.of_N (wordToN x)) with (uwordToZ x).
      eapply Z.bits_inj_iff'; intros i Hi.
      case (ZArith_dec.Z_lt_dec i width); intros.
      2: rewrite !Z.mod_pow2_bits_high by blia; trivial.
      rewrite !Z.mod_pow2_bits_low by blia.
      rewrite 2Z.lxor_spec.
      rewrite bitblast.Z.testbit_minus1 by trivial.
      enough (Z.testbit (uwordToZ (wones sz)) i = true) by congruence.
      cbv [uwordToZ].
      rewrite ?Z.testbit_of_N' by trivial.
      rewrite wordToN_wones_ones.
      apply BinNat.N.ones_spec_low.
      blia.
    }

    { setoid_rewrite uwordToZ_ZToWord_full; f_equal; trivial; congruence. }
    { cbv [wmult wordBin].
      rewrite wordToN_NToWord_eqn, Znat_N2Z_inj_mod, Znat.N2Z.inj_mul, NatLib.Z_of_N_Npow2.
      2: apply NatLib.Npow2_not_zero.
      f_equal; f_equal; blia. }

    { rewrite wordToZ_ZToWord_full by blia;
        cbv [swrap];  repeat (blia || f_equal). }
    { rewrite wordToZ_ZToWord_full by blia;
        cbv [swrap];  repeat (blia || f_equal). }
    { repeat setoid_rewrite uwordToZ_ZToWord_full; try blia.
      cbv [swrap];  repeat (blia || f_equal). }

    { repeat setoid_rewrite uwordToZ_ZToWord_full; try blia.
      f_equal.
      2: repeat (blia || f_equal).
      (* f_equal. (* WHY (COQBUG?) does this add hyps to the goal *) *)
      cbv [riscvZdivu]; destr (Z.of_N (wordToN y) =? 0); blia. }
    { rewrite wordToZ_ZToWord_full by blia.
      cbv [swrap]; f_equal.
      2 : repeat (blia || f_equal).
      cbv [swrap]; f_equal.
      2 : repeat (blia || f_equal).
      cbv [riscvZdivs].
      destr ((wordToZ x =? - 2 ^ (width - 1))); cbn [andb].
      { destr (wordToZ y =? -1); try blia.
        destr (wordToZ y =?  0); try blia.
        f_equal; f_equal; blia. }
      { destr (wordToZ y =?  0); try blia.
        f_equal; f_equal; blia. } }
    { repeat setoid_rewrite uwordToZ_ZToWord_full; try blia.
      f_equal.
      2: repeat (blia || f_equal).
      cbv [riscvZmodu].
      destr (Z.of_N (wordToN y) =? 0); blia. }
    { rewrite wordToZ_ZToWord_full by blia.
      cbv [swrap]; f_equal.
      2 : repeat (blia || f_equal).
      cbv [swrap]; f_equal.
      2 : repeat (blia || f_equal).
      cbv [riscvZmods].
      destr (wordToZ y =? 0); try blia.
      f_equal; f_equal; blia. }
    { rewrite wlshift_mul_Zpow2 by (Z.div_mod_to_equations; blia).
      cbv [wmult wordBin].
      rewrite wordToN_NToWord_eqn, Znat_N2Z_inj_mod, Znat.N2Z.inj_mul, NatLib.Z_of_N_Npow2.
      2:apply NatLib.Npow2_not_zero.
      repeat setoid_rewrite uwordToZ_ZToWord_full; try blia.
      rewrite Zdiv.Zmult_mod_idemp_r.
      rewrite Z.shiftl_mul_pow2 by blia.
      f_equal. 2: { f_equal; blia. }
      f_equal.
      f_equal.
      apply Z.mod_small; blia. }

    { cbv [wrshift].
      rewrite wordToN_split2.
      cbv [eq_rec_r eq_rec].
      rewrite wordToN_nat, wordToNat_eq_rect, <-wordToN_nat, wordToN_combine, wordToN_wzero.
      PreOmega.zify.
      rewrite !NatLib.Z_of_N_Npow2.
      rewrite Z.shiftr_div_pow2 by blia.
      replace (Z.of_N (wordToN x) + 2 ^ Z.of_nat sz * 0)
        with (Z.of_N (wordToN x)) by blia.
      rewrite Z.mod_small by blia.
      rewrite Z.mod_small.
      2: {
        pose proof uwordToZ_bound x; cbv [uwordToZ] in *.
        replace (Z.of_nat sz) with width in * by blia.
        match goal with
        | H: _ \/ _ |- _ => clear H; subst
        end.
        pose proof Z.pow_pos_nonneg 2 (Z.of_N (wordToN y)) eq_refl. auto_specialize.
        replace 0 with (0/2 ^ Z.of_N (wordToN y)) by (apply Z.div_0_l; blia).
        split; eauto using Z.div_le_mono.
        eapply Z.div_lt_upper_bound; trivial.
        Lia.nia. }
      f_equal.
      f_equal.
      rewrite Znat.Z2Nat.id; blia. }

    { cbv [wrshifta eq_rec_r eq_rec].
      rewrite Z.mod_small, wordToZ_split2, wordToZ_eq_rect, sext_wordToZ, Znat.Z2Nat.id, Z.shiftr_div_pow2; try blia.
      cbv [swrap]; rewrite Z.mod_small; try blia.
      pose proof @wordToZ_size (pred sz).
      rewrite PeanoNat.Nat.succ_pred in H0; [|blia].
      specialize (H0 x).
      pose proof (wordToZ_size'' AA x); rewrite BB in H1.
      split.
      { assert (0 < 2 ^ Z.of_N (wordToN y)) by (apply Z.pow_pos_nonneg; blia).
        assert (0 < 2 ^ (width - 1)) by (apply Z.pow_pos_nonneg; blia).
        assert (- 2 ^ (width - 1) <= wordToZ x / 2 ^ Z.of_N (wordToN y)).
        { apply Z.div_le_lower_bound; [assumption|].
          etransitivity; [|apply H1].
          rewrite Z.mul_comm; apply Z.le_mul_diag_l; blia.
        }
        blia.
      }
      { apply Z.lt_add_lt_sub_r.
        replace (2 ^ width) with (2 * 2 ^ (width - 1)).
        2: { change 2 with (2 ^ 1) at 1.
             rewrite <-Z.pow_add_r by blia.
             f_equal; blia.
        }
        replace (2 * 2 ^ (width - 1) - 2 ^ (width - 1))
          with (2 ^ (width - 1)) by blia.
        apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; blia|].
        eapply Z.lt_le_trans; [apply H1|].
        rewrite Z.mul_comm; apply Z.le_mul_diag_r.
        { apply Z.pow_pos_nonneg; blia. }
        { pose proof (Z.pow_pos_nonneg 2 (Z.of_N (wordToN y))); blia. }
      }
    }
    { specialize (weqb_true_iff x y); case (weqb x y); intros [].
      { specialize (H eq_refl); subst; rewrite Z.eqb_refl; trivial. }
      { case (weq x y); try solve [intuition congruence]; intros HH.
        case (Z.eqb_spec (Z.of_N (wordToN x)) (Z.of_N (wordToN y))) as [X|X]; trivial.
        eapply Znat.N2Z.inj_iff in X.
        eapply wordToN_inj in X.
        contradiction. } }
    { case (wlt_dec x y) as [H|H]; cbv [wlt] in H;
        case (Z.ltb_spec (Z.of_N (wordToN x)) (Z.of_N (wordToN y)));
        trivial; blia. }
    { case (wslt_dec x y) as [H|H]; cbv [wslt] in H;
        case (Z.ltb_spec (wordToZ x) (wordToZ y)) as [G|G];
        trivial; blia. }
  Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.
Arguments kword : clear implicits.

#[global] Existing Instance word.
#[global] Existing Instance ok.


Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Lemma boundW: 0 < width.
  Proof.
    case width_cases; intro E; rewrite E; reflexivity.
  Defined.
  #[local] Instance wordW: word.word width := word width.
  #[local] Instance wordWok: word.ok wordW := ok width boundW.

  #[local] Instance word8: word.word 8 := word 8.
  #[local] Instance word8ok: word.ok word8 := ok 8 eq_refl.
End MkWords.
