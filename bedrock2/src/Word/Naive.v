Local Set Universe Polymorphism.
Local Set Primitive Projections.
  
Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Lia.
Require Import bedrock2.Word. Import word.
Local Open Scope Z_scope.

(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section WithWidth.
  Context {width : Z}.
  Let wrap_value z := z mod (2^width).
  Let swrap_value z := wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Record rep := mk { unsigned : Z ; _unsigned_in_range : wrap_value unsigned = unsigned }.

  Context {width_nonneg : Z.lt 0 width}.

  Lemma wrap_value_wrap_value z : wrap_value (wrap_value z) = wrap_value z.
    cbv [wrap_value]. rewrite Z.mod_mod. reflexivity.
    eapply Z.pow_nonzero; [congruence | Lia.lia ].
  Qed.

  Definition wrap (z:Z) : rep :=
    mk (wrap_value z) (minimize_eq_proof Z.eq_dec (wrap_value_wrap_value z)).
  Definition signed w := swrap_value (unsigned w).

  Definition word : word.word width := {|
    word.rep := rep;
    word.unsigned := unsigned;
    word.signed := signed;
    of_Z := wrap;

    add x y := wrap (Z.add (unsigned x) (unsigned y));
    sub x y := wrap (Z.sub (unsigned x) (unsigned y));
    opp x := wrap (Z.opp (unsigned x));

    or x y := wrap (Z.lor (unsigned x) (unsigned y));
    and x y := wrap (Z.land (unsigned x) (unsigned y));
    xor x y := wrap (Z.lxor (unsigned x) (unsigned y));
    not x := wrap (Z.lnot (unsigned x));
    ndn x y := wrap (Z.ldiff (unsigned x) (unsigned y));

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
  |}.

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

  Lemma ok : word.ok word.
  Proof. split; eauto using of_Z_unsigned, signed_of_Z. Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.