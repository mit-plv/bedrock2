Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.

Axiom TODO: False.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Z.of_N (wordToN x).
  Definition ksigned: kword -> Z := @wordToZ sz.
  Definition kofZ: Z -> kword := ZToWord sz.

  Instance word : word.word width := {
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

    mul x y := kofZ (Z.mul (kunsigned x) (kunsigned y));
    mulhss x y := kofZ (Z.mul (ksigned x) (ksigned y) / 2^width);
    mulhsu x y := kofZ (Z.mul (ksigned x) (kunsigned y) / 2^width);
    mulhuu x y := kofZ (Z.mul (kunsigned x) (kunsigned y) / 2^width);

    divu x y := kofZ (Z.div (kunsigned x) (kunsigned y));
    divs x y := kofZ (Z.quot (ksigned x) (ksigned y));
    modu x y := kofZ (Z.modulo (kunsigned x) (kunsigned y));
    mods x y := kofZ (Z.rem (ksigned x) (ksigned y));

    slu x y := kofZ (Z.shiftl (kunsigned x) (kunsigned y));
    sru x y := kofZ (Z.shiftr (kunsigned x) (kunsigned y));
    srs x y := kofZ (Z.shiftr (ksigned x) (kunsigned y));

    eqb x y := Z.eqb (kunsigned x) (kunsigned y);
    ltu x y := Z.ltb (kunsigned x) (kunsigned y);
    lts x y := Z.ltb (ksigned x) (ksigned y);

    sextend oldwidth z := kofZ ((kunsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));

  }.

  (*
  Lemma eq_unsigned {x y : rep} : unsigned x = unsigned y -> x = y.
  Proof.
    cbv [value]; destruct x as [x px], y as [y py]; cbn.
    intro; subst y.
    apply f_equal, Eqdep_dec.UIP_dec. eapply Z.eq_dec.
  Qed.

  Lemma of_Z_unsigned x : wrap (unsigned x) = x.
  Proof. eapply eq_unsigned; destruct x; cbn; assumption.  Qed.

  Lemma signed_of_Z z : signed (wrap z) = wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Proof.
    cbv [unsigned signed wrap wrap_value swrap_value].
    rewrite Zdiv.Zplus_mod_idemp_l; auto.
  Qed.
  *)
  Instance ok : word.ok word. Admitted.
  (* Proof. split; eauto using of_Z_unsigned, signed_of_Z. Qed. *)
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
