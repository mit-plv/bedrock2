Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Axiom TODO_andres: False.
Axiom TODO_joonwon: False.

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
    if (x =? - 2 ^ (width - 1)) && (y =? - 1) then 0
    else if y =? 0 then x else Z.rem x y.

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


  (* TODO: move to word lemmas *)
  Lemma wordToN_split2 a b w :
    wordToN (@split2 a b w) = BinNat.N.div (wordToN w) (NatLib.Npow2 a).
  Proof.
    pose proof wordToNat_split2 a b w as HH.
    eapply Nnat.Nat2N.inj_iff in HH.
    rewrite wordToN_nat, HH; f_equal; clear HH.
    rewrite wordToN_nat, NatLib.pow2_N.
    generalize (#w); intro.
    generalize (NatLib.pow2 a); intro.
    pose proof Zdiv.div_Zdiv n n0 (match TODO_andres with end).
    pose proof Znat.N2Z.inj_div (BinNat.N.of_nat n) (BinNat.N.of_nat n0).
    rewrite Znat.nat_N_Z in *.
    Lia.lia.
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
    all: rewrite ?(match TODO_andres with end : forall x, Z.of_N (NatLib.Npow2 x) = Z.pow 2 (Z.of_nat x)).
    2: setoid_rewrite Z.add_0_r; trivial.
    rewrite ?Znat.Nat2Z.inj_add, ?Z.pow_add_r by Lia.lia.
    rewrite Z.mul_comm.
    symmetry.
    rewrite <-Z.add_opp_r, Zopp_mult_distr_l.
    rewrite Zdiv.Z_div_plus.
    1: Lia.lia.
    eapply Z.lt_gt.
    eapply Z.pow_pos_nonneg; Lia.lia.
  Qed.

  Instance ok : word.ok word.
  Proof using width_nonneg.
    split; trivial.
    all : cbv [rep unsigned signed of_Z add sub opp or and xor not
      ndn mul mulhss mulhsu mulhuu divu divs modu mods slu sru srs
      eqb ltu lts sextend word wrap
      kword kunsigned ksigned kofZ ];
    intros.
    1,2: case TODO_joonwon. (* bbv 9ec036507dbd592425576423f2a42256732a74d5 *)
    { rewrite ZToWord_Z_of_N, NToWord_wordToN; solve[trivial]. }

    19: {
      cbv [wrshifta eq_rec_r eq_rec].
      rewrite Z.mod_small, wordToZ_split2, wordToZ_eq_rect, sext_wordToZ, Znat.Z2Nat.id, Z.shiftr_div_pow2; try Lia.lia.
      1: cbv [swrap]; rewrite Z.mod_small; try Lia.lia.
      1: pose proof @wordToZ_size (pred sz).
      1: rewrite PeanoNat.Nat.succ_pred in H0.
      1: specialize (H0 x).
      1,2,3:case TODO_andres. }
    19: {
      specialize (weqb_true_iff x y); case (weqb x y); intros [].
      { specialize (H eq_refl); subst; rewrite Z.eqb_refl; trivial. }
      { case (weq x y); try solve [intuition congruence]; intros HH.
        case (Z.eqb_spec (Z.of_N (wordToN x)) (Z.of_N (wordToN y))) as [X|X]; trivial.
        eapply Znat.N2Z.inj_iff in X.
        eapply wordToN_inj in X.
        contradiction. } }
    19: {
      case (wlt_dec x y) as [H|H]; cbv [wlt] in H;
      case (Z.ltb_spec (Z.of_N (wordToN x)) (Z.of_N (wordToN y)));
          trivial; Lia.lia. }
    19: {
      case (wslt_dec x y) as [H|H]; cbv [wslt] in H;
      case (Z.ltb_spec (wordToZ x) (wordToZ y)) as [G|G];
          trivial; Lia.lia. }
    all : case TODO_andres.
  Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.
Arguments kword : clear implicits.

Existing Instance word.
Existing Instance ok.


Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Lemma boundW: 0 < width.
  Proof.
    case width_cases; intro E; rewrite E; reflexivity.
  Defined.
  Instance wordW: word.word width := word width.
  Instance wordWok: word.ok wordW := ok width boundW.

  Instance word8: word.word 8 := word 8.
  Instance word8ok: word.ok word8 := ok 8 eq_refl.

  Instance WordsKami: Utility.Words := {|
    Utility.byte := word8;
    Utility.word := wordW;
    Utility.width_cases := width_cases;
  |}.

End MkWords.
