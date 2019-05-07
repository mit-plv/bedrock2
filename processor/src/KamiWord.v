Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.

Axiom TODO: False.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Local Set Refine Instance Mode.

  Instance word : word.word width := {|
    word.rep := Kami.Lib.Word.word sz;
    word.unsigned x := Z.of_N (wordToN x);
    word.signed := @wordToZ sz;
    of_Z := ZToWord sz;

    add := @wplus sz;
    sub := @wminus sz;
    opp := @wneg sz;

    or  := @wor sz;
    and := @wand sz;
    xor := @wxor sz;
    not := @wnot sz;

    (* "x and not y"
    ndn := wrap (Z.ldiff (unsigned x) (unsigned y));

    mul x y := wrap (Z.mul (unsigned x) (unsigned y));
    mulhss x y := wrap (Z.mul (signed x) (signed y) / 2^width);
    mulhsu x y := wrap (Z.mul (signed x) (unsigned y) / 2^width);
    mulhuu x y := wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    divu x y := wrap (Z.div (unsigned x) (unsigned y));
    divs x y := wrap (Z.quot (signed x) (signed y));
    modu x y := wrap (Z.modulo (unsigned x) (unsigned y));
    mods x y := wrap (Z.rem (signed x) (signed y));

    slu x y := wrap (Z.shiftl (unsigned x) (unsigned y));
    sru x y := wrap (Z.shiftr (unsigned x) (unsigned y));
    srs x y := wrap (Z.shiftr (signed x) (unsigned y));

    eqb x y := Z.eqb (unsigned x) (unsigned y);
    ltu x y := Z.ltb (unsigned x) (unsigned y);
    lts x y := Z.ltb (signed x) (signed y);

    sextend oldwidth z := wrap ((unsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));
    *)
  |}.
  all: case TODO. Defined.

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

Existing Instance word.
Existing Instance ok.


Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Lemma boundW: 0 < width. blia. Qed.
  Instance wordW: word.word width := word width.
  Instance wordWok: word.ok wordW := ok width boundW.

  Lemma bound8: 0 < 8. blia. Qed.
  Instance word8: word.word 8 := word 8.
  Instance word8ok: word.ok word8 := ok 8 bound8.

  Instance WordsKami: Utility.Words := {|
    Utility.byte := word8;
    Utility.word := wordW;
    Utility.width_cases := width_cases;
  |}.

End MkWords.

Definition kword (w: Z): Type := Kami.Lib.Word.word (Z.to_nat w).

