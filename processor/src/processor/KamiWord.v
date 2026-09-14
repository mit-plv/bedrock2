Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Tactics.forward coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.
From coqutil Require Import destr div_mod_to_equations.
From Stdlib Require Import Zmod.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

(** [Kami.Lib.Word.word n] is the standard library's [bits (Z.of_nat n)], and
    every Kami word operation is specified through [Zmod.unsigned].  So this
    bridge only has to transport the Kami [unsigned_*] lemmas from
    [Zmod.unsigned] to Kami's [wordToN]/[wordToZ] spellings, which is what
    [Z_of_wordToN] below does. *)

Section KamiWordFacts.

  Lemma Z_of_wordToN: forall sz (w: Word.word sz), Z.of_N (wordToN w) = Zmod.unsigned w.
  Proof.
    intros; cbv [wordToN]; pose proof (@unsigned_range _ w); apply Z2N.id; blia.
  Qed.

  (* [uwordToZ] is [Zmod.unsigned], while [wordToN] goes through [Z.to_N]. *)
  Lemma uwordToZ_kunsigned: forall sz (w: Word.word sz),
      uwordToZ w = Z.of_N (wordToN w).
  Proof. intros; symmetry; apply Z_of_wordToN. Qed.

  Lemma unsigned_mod_id: forall sz (w: Word.word sz),
      Zmod.unsigned w mod 2 ^ Z.of_nat sz = Zmod.unsigned w.
  Proof. intros; apply Z.mod_small, (@unsigned_range _ w). Qed.

  Lemma unsigned_wnot_mod: forall sz (w: Word.word sz),
      Zmod.unsigned (wnot w) = Z.lnot (Zmod.unsigned w) mod 2 ^ Z.of_nat sz.
  Proof.
    intros; rewrite unsigned_wnot.
    pose proof (@unsigned_range _ w); pose proof (pow2_pos_Z sz).
    unfold Z.lnot.
    replace (Z.pred (- Zmod.unsigned w))
      with (2 ^ Z.of_nat sz - 1 - Zmod.unsigned w + (-1) * 2 ^ Z.of_nat sz) by blia.
    rewrite Z.mod_add by blia.
    rewrite Z.mod_small by blia; reflexivity.
  Qed.

  Lemma wrshifta_ZToWord: forall sz (w: Word.word sz) n,
      wrshifta w n = ZToWord sz (wordToZ w / 2 ^ Z.of_nat n).
  Proof. reflexivity. Qed.

  Lemma weqb_eqb: forall sz (x y: Word.word sz),
      weqb x y = Z.eqb (Zmod.unsigned x) (Zmod.unsigned y).
  Proof.
    intros.
    destruct (Zmod.eqb_spec x y) as [E|E];
      destruct (Z.eqb_spec (Zmod.unsigned x) (Zmod.unsigned y)) as [E2|E2];
      try reflexivity.
    - subst; congruence.
    - exfalso; apply E, Zmod.unsigned_inj, E2.
  Qed.

  Lemma wordToN_split2 a b w :
    wordToN (@split2 a b w) = BinNat.N.div (wordToN w) (NatLib.Npow2 a).
  Proof.
    apply Znat.N2Z.inj.
    rewrite Znat.N2Z.inj_div, !Z_of_wordToN, NatLib.Z_of_N_Npow2.
    apply unsigned_split2.
  Qed.

  Lemma wordToN_split1 a b w :
    wordToN (@split1 a b w) = BinNat.N.modulo (wordToN w) (NatLib.Npow2 a).
  Proof.
    apply Znat.N2Z.inj.
    rewrite Znat.N2Z.inj_mod, !Z_of_wordToN, NatLib.Z_of_N_Npow2.
    apply unsigned_split1.
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
    pose proof (@unsigned_range _ w1); pose proof (@unsigned_range _ w2).
    rewrite !Z_of_wordToN, unsigned_combine, Znat.nat_N_Z.
    rewrite Z.shiftl_mul_pow2 by blia.
    rewrite (Z.mul_comm (Zmod.unsigned w2)).
    apply Z_pow_add_lor; blia.
  Qed.

  Lemma split1_wplus_silent:
    forall sz1 sz2 (w1 w2: Word.word (sz1 + sz2)),
      split1 sz1 sz2 w2 = wzero _ ->
      split1 sz1 sz2 (w1 ^+ w2) = split1 sz1 sz2 w1.
  Proof.
    intros sz1 sz2 w1 w2 H.
    apply (f_equal (@Zmod.unsigned _)) in H.
    rewrite unsigned_split1, Zmod.unsigned_0 in H.
    apply Zmod.unsigned_inj.
    rewrite !unsigned_split1, Zmod.unsigned_add.
    rewrite Z.mod_mod_divide by (exists (2 ^ Z.of_nat sz2); rewrite pow2_add_Z; ring).
    rewrite Zplus_mod, H, Z.add_0_r, Zmod_mod; reflexivity.
  Qed.

  Lemma sumbool_rect_weq {T} a b n x y :
    sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
  Proof.
    cbv [sumbool_rect].
    destruct (weq _ _), (weqb _ _) eqn:?;
                                   try match goal with H : _ |- _ => eapply Zmod.eqb_eq in H end;
      trivial; congruence.
  Qed.

  Lemma sumbool_rect_bool_weq n x y :
    sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
  Proof. rewrite sumbool_rect_weq; destruct (weqb x y); trivial. Qed.

  Lemma unsigned_eqb n (x y : Word.word n) : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = weqb x y.
  Proof. rewrite !Z_of_wordToN; symmetry; apply weqb_eqb. Qed.

  Lemma unsigned_split1_mod:
    forall n m w,
      Z.of_N (wordToN (split1 n m w)) = Z.of_N (wordToN w) mod (2 ^ (Z.of_nat n)).
  Proof. intros; rewrite !Z_of_wordToN; apply unsigned_split1. Qed.

End KamiWordFacts.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Z.of_N (wordToN x).
  Definition ksigned (x: kword): Z := wordToZ x.
  Definition kofZ (z: Z): kword := ZToWord sz z.

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

    add := Zmod.add;
    sub := Zmod.sub;
    opp := Zmod.opp;

    or  := Zmod.or;
    and := Zmod.and;
    xor := Zmod.xor;
    not := Zmod.not;

    (* "x and not y" *)
    ndn x y := kofZ (Z.ldiff (kunsigned x) (kunsigned y));

    mul := Zmod.mul;
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

    eqb := Zmod.eqb;
    ltu x y := Z.ltb (uwordToZ x) (uwordToZ y);
    lts x y := Z.ltb (wordToZ x) (wordToZ y);

    sextend oldwidth z := kofZ ((kunsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));

  |}.

  (* [Z.of_nat sz] is only propositionally [width], and it also occurs in the
     (implicit) modulus of every [Zmod.unsigned] below, where rewriting it would
     be ill-typed.  So the width arithmetic always goes from [width] to
     [Z.of_nat sz], never the other way. *)
  Local Lemma sz_pos: (0 < sz)%nat.
  Proof using width_nonneg. eapply (Znat.Z2Nat.inj_lt 0); blia. Qed.

  Local Lemma pow2_sz: 2 ^ Z.of_nat sz = 2 ^ width.
  Proof using width_nonneg. f_equal; apply Znat.Z2Nat.id; blia. Qed.

  Local Lemma pow2_sz_pred: 2 ^ (Z.of_nat sz - 1) = 2 ^ (width - 1).
  Proof using width_nonneg. f_equal; rewrite Znat.Z2Nat.id; blia. Qed.

  Instance ok : word.ok word.
  Proof using width_nonneg.
    pose proof sz_pos as AA.
    split; trivial.
    all: cbv [rep unsigned signed of_Z add sub opp or and xor not
                  ndn mul mulhss mulhsu mulhuu divu divs modu mods slu sru srs
                  eqb ltu lts sextend word wrap swrap
                  kword kunsigned ksigned kofZ]; intros.
    all: rewrite <- ?pow2_sz, <- ?pow2_sz_pred in *.
    all: rewrite ?Z_of_wordToN in *.

    { apply Zmod.unsigned_of_Z. }
    { rewrite wordToZ_ZToWord_full by exact AA; reflexivity. }
    { apply Zmod.of_Z_unsigned. }
    { apply Zmod.unsigned_add. }
    { apply Zmod.unsigned_sub. }
    { apply Zmod.unsigned_opp. }
    { rewrite <- bits.unsigned_or; symmetry; apply unsigned_mod_id. }
    { rewrite <- bits.unsigned_and; symmetry; apply unsigned_mod_id. }
    { rewrite <- bits.unsigned_xor; symmetry; apply unsigned_mod_id. }
    { apply unsigned_wnot_mod. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_mul. }
    { rewrite wordToZ_ZToWord_full by exact AA; reflexivity. }
    { rewrite wordToZ_ZToWord_full by exact AA; reflexivity. }
    { apply Zmod.unsigned_of_Z. }

    { rewrite Zmod.unsigned_of_Z.
      cbv [riscvZdivu]; destr (Zmod.unsigned y =? 0); [blia|reflexivity]. }
    { rewrite wordToZ_ZToWord_full by exact AA.
      cbv [riscvZdivs]; rewrite <- ?pow2_sz_pred.
      destr (wordToZ x =? - 2 ^ (Z.of_nat sz - 1)); cbn [andb].
      { destr (wordToZ y =? -1); [blia|].
        destr (wordToZ y =? 0); [blia|reflexivity]. }
      { destr (wordToZ y =? 0); [blia|reflexivity]. } }
    { rewrite Zmod.unsigned_of_Z.
      cbv [riscvZmodu]; destr (Zmod.unsigned y =? 0); [blia|reflexivity]. }
    { rewrite wordToZ_ZToWord_full by exact AA.
      cbv [riscvZmods]; destr (wordToZ y =? 0); [blia|reflexivity]. }

    { pose proof (@unsigned_range _ y).
      rewrite (Z.mod_small (Zmod.unsigned y) width) by blia.
      rewrite unsigned_wlshift, (Znat.Z2Nat.id (Zmod.unsigned y)) by blia.
      rewrite Z.shiftl_mul_pow2 by blia; reflexivity. }
    { pose proof (@unsigned_range _ x); pose proof (@unsigned_range _ y).
      pose proof (Z.pow_pos_nonneg 2 (Zmod.unsigned y) ltac:(blia) ltac:(blia)).
      rewrite (Z.mod_small (Zmod.unsigned y) width) by blia.
      rewrite unsigned_wrshift, (Znat.Z2Nat.id (Zmod.unsigned y)) by blia.
      rewrite Z.shiftr_div_pow2 by blia.
      symmetry; apply Z.mod_small.
      split; [apply Z.div_pos; blia|apply Z.div_lt_upper_bound; [blia|Lia.nia]]. }
    { pose proof (@unsigned_range _ y).
      rewrite (Z.mod_small (Zmod.unsigned y) width) by blia.
      rewrite wrshifta_ZToWord, wordToZ_ZToWord_full by exact AA.
      rewrite (Znat.Z2Nat.id (Zmod.unsigned y)) by blia.
      rewrite Z.shiftr_div_pow2 by blia; reflexivity. }

    { apply weqb_eqb. }
    { reflexivity. }
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
