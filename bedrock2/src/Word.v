(* Specification of two's complement machine words wrt Z *)

Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.

Module word.
  Local Set Primitive Projections.
  Local Set Universe Polymorphism.
  Class word {width : Z} := {
    rep : Set;

    (* defining relations *)
    unsigned : rep -> Z;
    (* signed : rep -> Z; *)
    of_Z : Z -> rep;

    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;

    (* adc : bool -> rep -> rep -> rep*bool; *)
    (* sbb : bool -> rep -> rep -> rep*bool; *)

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    (* mulhss : rep -> rep -> rep; *)
    (* mulhsu : rep -> rep -> rep; *)
    (* mulhuu : rep -> rep -> rep; *)

    (* divu : rep -> rep -> rep; *)
    (* divs : rep -> rep -> rep; *)

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    (* srs : rep -> rep -> rep; *)

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    (* lts : rep -> rep -> bool; *)

    (* gtu : rep -> rep -> bool; *)
    (* gts : rep -> rep -> bool; *)
  }.
  Arguments word : clear implicits.
  
  Class ok {width} {word : word width} := {
    wrap z := Z.modulo z (Z.pow 2 width);

    unsigned_of_Z : forall z, unsigned (of_Z z) = wrap z;
    of_Z_unsigned : forall x, of_Z (unsigned x) = x;

    unsigned_add : forall x y, unsigned (add x y) = wrap (Z.add (unsigned x) (unsigned y));
    unsigned_sub : forall x y, unsigned (sub x y) = wrap (Z.sub (unsigned x) (unsigned y));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
  }.
  Arguments ok {_} _.

  Section WithWord.
    Context {width} {word : word width} {word_ok : ok word}.
    Lemma unsigned_mod_range x : unsigned x = Z.modulo (unsigned x) (Z.pow 2 width).
    Proof.
      pose proof unsigned_of_Z (unsigned x) as H.
      rewrite of_Z_unsigned in H.
      assumption.
    Qed.
  End WithWord.
End word. Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.