Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Axiom TODO_andres: False.

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

    mul := @wmult sz;
    mulhss x y := kofZ (Z.mul (ksigned x) (ksigned y) / 2^width);
    mulhsu x y := kofZ (Z.mul (ksigned x) (kunsigned y) / 2^width);
    mulhuu x y := kofZ (Z.mul (kunsigned x) (kunsigned y) / 2^width);

    divu x y := kofZ (riscvZdivu (kunsigned x) (kunsigned y));
    divs x y := kofZ (riscvZdivs (ksigned x) (ksigned y));
    modu x y := kofZ (riscvZmodu (kunsigned x) (kunsigned y));
    mods x y := kofZ (riscvZmods (ksigned x) (ksigned y));

    (* shifts only look at the lowest 5-6 bits of the shift amount *)
    slu x y := kofZ (Z.shiftl (kunsigned x) (kunsigned y mod width));
    sru x y := kofZ (Z.shiftr (kunsigned x) (kunsigned y mod width));
    srs x y := kofZ (Z.shiftr (ksigned x) (kunsigned y mod width));

    eqb x y := Z.eqb (kunsigned x) (kunsigned y);
    ltu x y := Z.ltb (kunsigned x) (kunsigned y);
    lts x y := Z.ltb (ksigned x) (ksigned y);

    sextend oldwidth z := kofZ ((kunsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));

  }.

  Instance ok : word.ok word.
  Proof using width_nonneg.
    case TODO_andres.
    (* is there a smart way to lift the proofs from coqutil.Word to KamiWord,
       exploiting the regular structure of the definitions based on kofZ/kunsigned/ksigned ? *)
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
