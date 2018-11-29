(* Specification of two's complement machine words wrt Z *)

Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Local Open Scope Z_scope.

Require Coq.setoid_ring.Ring_theory Lia.

Module word.
  Local Set Primitive Projections.
  Local Set Universe Polymorphism.
  Class word {width : Z} := {
    rep : Set;

    (* defining relations *)
    unsigned : rep -> Z;
    signed : rep -> Z;
    of_Z : Z -> rep;

    (* operations *)
    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep;

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    srs : rep -> rep -> rep;

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    lts : rep -> rep -> bool;

    gtu x y := ltu y x;
    gts x y := lts y x;
  }.
  Arguments word : clear implicits.
  
  Class ok {width} {word : word width} := {
    wrap z := z mod 2^width;
    swrap z := wrap (z + 2^(width-1)) - 2^(width-1);

    unsigned_of_Z : forall z, unsigned (of_Z z) = wrap z;
    signed_of_Z : forall z, signed (of_Z z) = swrap z;
    of_Z_unsigned : forall x, of_Z (unsigned x) = x;

    unsigned_add : forall x y, unsigned (add x y) = wrap (Z.add (unsigned x) (unsigned y));
    unsigned_sub : forall x y, unsigned (sub x y) = wrap (Z.sub (unsigned x) (unsigned y));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));
    unsigned_mulhss : forall x y, signed (mulhss x y) = swrap (Z.mul (signed x) (signed y) / 2^width);
    unsigned_mulhsu : forall x y, signed (mulhsu x y) = swrap (Z.mul (signed x) (unsigned y) / 2^width);
    unsigned_mulhuu : forall x y, unsigned (mulhuu x y) = wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    unsigned_divu : forall x y, unsigned (divu x y) = wrap (Z.div (unsigned x) (unsigned y));
    signed_divs : forall x y, signed (divs x y) = swrap (Z.div (signed x) (signed y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));
    signed_srs : forall x y, Z.lt (unsigned y) width -> signed (srs x y) = swrap (Z.shiftr (signed x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
    signed_lts : forall x y, lts x y = Z.ltb (signed x) (signed y);
  }.
  Arguments ok {_} _.

  Section WithWord.
    Context {width} {word : word width} {word_ok : ok word}.
    Lemma unsigned_mod_range x : (unsigned x) mod (2^width) = unsigned x.
    Proof.
      pose proof unsigned_of_Z (unsigned x) as H.
      rewrite of_Z_unsigned in H. congruence.
    Qed.

    Lemma eq_unsigned x y (H : unsigned x = unsigned y) : x = y.
    Proof. rewrite <-(of_Z_unsigned x), <-(of_Z_unsigned y). apply f_equal, H. Qed.

    Lemma ring_theory (H:0 <= width) : Ring_theory.ring_theory (of_Z 0) (of_Z 1) add mul sub (sub (of_Z 0)) Logic.eq.
    Proof.
     assert (2^width <> 0) by (assert (2 <> 0) by discriminate; apply Z.pow_nonzero; auto).
     split; intros; apply eq_unsigned; repeat rewrite
         ?unsigned_add, ?unsigned_sub, ?unsigned_mul, ?unsigned_of_Z, ?unsigned_mod_range,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l;
       f_equal; auto with zarith.
    Qed.
  End WithWord.
End word. Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.