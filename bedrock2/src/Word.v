(* Specification of two's complement machine words wrt Z *)

Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* TODO: move me? *)
(* from https://github.com/coq/coq/pull/8062/files#diff-c73fff6c197eb53a5ca574b51e21bf82 *)
Require Import Lia.
Module Z.  Lemma mod_0_r_ext x y : y = 0 -> x mod y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma div_0_r_ext x y : y = 0 -> x / y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Ltac div_mod_to_quot_rem_generalize x y :=
    pose proof (Z.div_mod x y);    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);    pose proof (div_0_r_ext x y);
    pose proof (mod_0_r_ext x y);    let q := fresh "q" in
    let r := fresh "r" in    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.  Ltac div_mod_to_quot_rem_step :=
    match goal with    | [ |- context[?x / ?y] ] => div_mod_to_quot_rem_generalize x y
    | [ |- context[?x mod ?y] ] => div_mod_to_quot_rem_generalize x y    | [ H : context[?x / ?y] |- _ ] => div_mod_to_quot_rem_generalize x y
    | [ H : context[?x mod ?y] |- _ ] => div_mod_to_quot_rem_generalize x y    end.
  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step.
End Z.
Ltac mia := Z.div_mod_to_quot_rem; nia.


(* TODO: move *)
Lemma Z__testbit_mod_pow2 a n i (H:0<=n)
  : Z.testbit (a mod 2 ^ n) i = ((i <? n) && Z.testbit a i)%bool.
Proof.
  destruct (Z.ltb_spec i n); rewrite
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high by auto; auto.
Qed.

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
    opp : rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;
    not : rep -> rep;
    ndn : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep; (* Z.quot *)
    modu : rep -> rep -> rep;
    mods : rep -> rep -> rep; (* Z.rem *)

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
    unsigned_opp : forall x, unsigned (opp x) = wrap (Z.opp (unsigned x));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));
    unsigned_not : forall x, unsigned (not x) = wrap (Z.lnot (unsigned x));
    unsigned_ndn : forall x y, unsigned (ndn x y) = wrap (Z.ldiff (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));
    unsigned_mulhss : forall x y, signed (mulhss x y) = swrap (Z.mul (signed x) (signed y) / 2^width);
    unsigned_mulhsu : forall x y, signed (mulhsu x y) = swrap (Z.mul (signed x) (unsigned y) / 2^width);
    unsigned_mulhuu : forall x y, unsigned (mulhuu x y) = wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    unsigned_divu : forall x y, unsigned y <> 0 -> unsigned (divu x y) = wrap (Z.div (unsigned x) (unsigned y));
    signed_divs : forall x y, signed y <> 0 -> signed x <> -2^(width-1) \/ signed y <> -1 -> signed (divs x y) = swrap (Z.quot (signed x) (signed y));
    unsigned_modu : forall x y, unsigned y <> 0 -> unsigned (modu x y) = wrap (Z.modulo (unsigned x) (unsigned y));
    signed_mods : forall x y, signed y <> 0 -> signed (mods x y) = swrap (Z.rem (signed x) (signed y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));
    signed_srs : forall x y, Z.lt (unsigned y) width -> signed (srs x y) = swrap (Z.shiftr (signed x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
    signed_lts : forall x y, lts x y = Z.ltb (signed x) (signed y);
  }.
  Arguments ok {_} _.

  (* TODO: move this section to WordProperties.v or similar *)
  Section WithWord.
    Context {width} {word : word width} {word_ok : ok word}.

    (* Create HintDb word_laws discriminated. *) (* DON'T do this, COQBUG(5381) *)
    Hint Rewrite
         unsigned_of_Z signed_of_Z of_Z_unsigned unsigned_add unsigned_sub unsigned_opp unsigned_or unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul unsigned_mulhss unsigned_mulhsu unsigned_mulhuu unsigned_divu signed_divs unsigned_modu signed_mods unsigned_slu unsigned_sru signed_srs unsigned_eqb unsigned_ltu signed_lts
         using trivial
         : word_laws.

    Lemma unsigned_mod_range x : (unsigned x) mod (2^width) = unsigned x.
    Proof.
      pose proof unsigned_of_Z (unsigned x) as H.
      rewrite of_Z_unsigned in H. congruence.
    Qed.

    Lemma eq_unsigned x y (H : unsigned x = unsigned y) : x = y.
    Proof. rewrite <-(of_Z_unsigned x), <-(of_Z_unsigned y). apply f_equal, H. Qed.

    Context (width_nonneg : 0 <= width).
    Let m_small : 0 < 2^width. apply Z.pow_pos_nonneg; firstorder idtac. Qed.

    Lemma ring_theory : Ring_theory.ring_theory (of_Z 0) (of_Z 1) add mul sub opp Logic.eq.
    Proof.
     split; intros; apply eq_unsigned; repeat rewrite ?unsigned_mod_range,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l;
       f_equal; auto with zarith.
    Qed.

    Lemma ring_morph :
      Ring_theory.ring_morph (of_Z 0) (of_Z 1) add mul sub opp Logic.eq 0  1 Z.add Z.mul Z.sub Z.opp Z.eqb of_Z.
    Proof.
     split; intros; apply eq_unsigned; repeat rewrite  ?unsigned_mod_range,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Zdiv.Zminus_mod_idemp_l, ?Zdiv.Zminus_mod_idemp_r,
         ?Z.sub_0_l, ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l by auto with zarith;
       try solve [f_equal; auto with zarith].
     { rewrite <-Z.sub_0_l; symmetry; rewrite <-Z.sub_0_l, Zdiv.Zminus_mod_idemp_r. auto. } (* COQBUG? *)
     { f_equal. eapply Z.eqb_eq. auto. } (* Z.eqb -> @eq z *)
    Qed.

    Require Import Btauto.
    (* Create HintDb z_bitwise discriminated. *) (* DON'T do this, COQBUG(5381) *)
    Hint Rewrite
         Z.shiftl_spec_low Z.lxor_spec Z.lor_spec Z.land_spec Z.lnot_spec Z.ldiff_spec Z.shiftl_spec Z.shiftr_spec Z.ones_spec_high Z.shiftl_spec_alt Z.ones_spec_low Z.shiftr_spec_aux Z.shiftl_spec_high Z.ones_spec_iff Z.testbit_spec' Z.testbit_spec 
         Z.div_pow2_bits Z.pow2_bits_eqb Z.bits_opp Z.testbit_0_l
         Z__testbit_mod_pow2
         using solve [auto with zarith] : z_bitwise.
    Hint Rewrite <-Z.ones_equiv
         using solve [auto with zarith] : z_bitwise.

    Ltac generalize_unsigned_mod_range :=
      repeat match goal with
             | x : @word.rep ?a ?b |- _ =>
               rewrite <-(unsigned_mod_range x);
               let x' := fresh in
               set (unsigned x) as x' in *; clearbody x'; clear x; rename x' into x
             end.

    Ltac bitwise :=
      autorewrite with word_laws;
      generalize_unsigned_mod_range;
      eapply Z.bits_inj'; intros ?i ?Hi; autorewrite with z_bitwise; btauto.

    Ltac unsigned :=
      autorewrite with word_laws;
      generalize_unsigned_mod_range;
      rewrite Z.mod_small; mia.

    Lemma unsigned_or_nowrap x y : unsigned (or x y) = Z.lor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_and_nowrap x y : unsigned (and x y) = Z.land (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_xor_nowrap x y : unsigned (xor x y) = Z.lxor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_ndn_nowrap x y : unsigned (ndn x y) = Z.ldiff (unsigned x) (unsigned y).
    Proof. bitwise. Qed.

    Lemma unsigned_mulhuu_nowrap x y : unsigned (mulhuu x y) = Z.mul (unsigned x) (unsigned y) / 2^width.
    Proof. unsigned. Qed.
    Lemma unsigned_divu_nowrap x y (H:unsigned y <> 0) : unsigned (divu x y) = Z.div (unsigned x) (unsigned y).
    Proof. unsigned. Qed.
    Lemma unsigned_modu_nowrap x y (H:unsigned y <> 0) : unsigned (modu x y) = Z.modulo (unsigned x) (unsigned y).
    Proof. unsigned. Qed.

    Context (width_nonzero : 0 < width).
    Let halfm_small : 0 < 2^(width-1). apply Z.pow_pos_nonneg; auto with zarith. Qed.

    Lemma signed_eq_swrap_unsigned x : signed x = swrap (unsigned x).
    Proof. cbv [swrap wrap]; rewrite <-signed_of_Z, of_Z_unsigned; trivial. Qed.
    
    Definition weightwrap z := (z mod 2^width) mod 2^(width-1) - 2^(width - 1) * (z mod 2^width / 2^(width - 1)).
    Lemma weightwrap_eq_swrap z : weightwrap z = swrap z.
    Proof.
      symmetry. cbv [weightwrap swrap wrap].
      set (M := 2 ^ (width - 1)).
      assert (0 < M) by (change 0 with (2^(-1)); eapply Z.pow_lt_mono_r; lia).
      assert (0 < 2*M) by lia.
      replace (2^width) with (2*M) in * by
          (subst M; rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; nia).
      clearbody M.
      rewrite (Z.add_mod _ _ _) by lia.
      assert (M/(2 * M)=0) as H2M by mia;
        replace (M mod (2 * M)) with M by mia; clear H2M.
      set (X := z mod (2*M));
        destruct (ltac:(subst X; mia):(0 <= X < M \/ M <= X < 2*M)); clearbody X.
      { assert (X/M = 0) by mia; assert ((X + M) / (2 * M) = 0); mia. }
      { assert (X/M = 1) by mia; assert ((X + M) / (2 * M) = 1); mia. }
    Qed.

    Lemma signed_alt x : signed x = weightwrap (unsigned x).
    Proof. rewrite signed_eq_swrap_unsigned. rewrite weightwrap_eq_swrap. trivial. Qed.

    Lemma testbit_signed x i (H:0 <= i) : Z.testbit (signed x) i
                               = if i <? width
                                 then Z.testbit (unsigned x) i
                                 else Z.testbit (unsigned x) (width -1).
    Proof.
      assert ((unsigned x mod 2 ^ width / 2 ^ (width - 1)) = 0 \/ (unsigned x mod 2 ^ width / 2 ^ (width - 1)) = 1) as HH by admit.
      rewrite signed_alt.
      cbv [weightwrap].
      rewrite <-Z.add_opp_r.
      destruct HH as [HH|HH]; rewrite ?HH, ?Z.mul_0_r, ?Z.mul_1_r, ?Z.add_0_r; autorewrite with z_bitwise; cbn.
      { destruct (Z.ltb_spec i (width-1)), (Z.ltb_spec i width); cbn;
          autorewrite with z_bitwise; cbn; try solve [lia | btauto].
        all: try replace i with (width-1) by lia.
        all: replace (Z.testbit (unsigned x) (width-1)) with (Z.testbit (unsigned x mod 2 ^ width / 2 ^ (width - 1)) 0) by admit; rewrite ?HH; cbn; trivial. }
      rewrite Z.add_nocarry_lxor; cycle 1.
      { clear i H.
        eapply Z.bits_inj'; intros ?i ?Hi; autorewrite with z_bitwise.
        destruct (Z.ltb_spec i (width-1)), (Z.ltb_spec i width); cbn;
          autorewrite with z_bitwise; cbn; try solve [lia | btauto]. }
      autorewrite with z_bitwise.
      destruct (Z.ltb_spec i (width-1)), (Z.ltb_spec i width); cbn;
        autorewrite with z_bitwise; cbn; try solve [lia | btauto].
        all: try replace i with (width-1) by lia.
        all: replace (Z.testbit (unsigned x) (width-1)) with (Z.testbit (unsigned x mod 2 ^ width / 2 ^ (width - 1)) 0) by admit; rewrite ?HH; cbn; trivial.
    Admitted.

    Lemma signed_add x y : signed (add x y) = swrap (Z.add (signed x) (signed y)).
    Proof.
      rewrite !signed_eq_swrap_unsigned; autorewrite with word_laws.
      cbv [wrap swrap]; generalize_unsigned_mod_range.
      replace (2 ^ width) with (2*2 ^ (width - 1)) by
        (rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; lia).
      set (M := 2 ^ (width - 1)) in*; clearbody M; clear dependent width.
      assert (0<2*M) by nia.
      rewrite <-!Z.add_opp_r.
      repeat rewrite ?Z.add_assoc, ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?(Z.add_shuffle0 _ (_ mod _)).
      rewrite 4(Z.add_comm (_ mod _)).
      repeat rewrite ?Z.add_assoc, ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?(Z.add_shuffle0 _ (_ mod _)).
      f_equal.
      f_equal.
      all:lia.
    Qed.

    Lemma signed_mul x y : signed (mul x y) = swrap (Z.mul (signed x) (signed y)).
    Proof.
      rewrite !signed_eq_swrap_unsigned; autorewrite with word_laws.

      cbv [wrap swrap]; generalize_unsigned_mod_range.
      replace (2 ^ width) with (2*2 ^ (width - 1)) by
        (rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; lia).
      set (M := 2 ^ (width - 1)) in*; clearbody M; clear dependent width.
      assert (0<2*M) by nia.
      f_equal.
      symmetry.
      rewrite <-Z.add_mod_idemp_l by lia.
      rewrite Z.mul_mod by lia.
      rewrite <-!Z.add_opp_r.
      rewrite ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r by lia.
      rewrite !Z.add_opp_r.
      rewrite !Z.add_simpl_r.
      rewrite !Z.mod_mod by lia.
      trivial.
    Qed.

    Lemma signed_sru x y (H : Z.lt (unsigned y) width) : signed (slu x y) = swrap (Z.shiftl (signed x) (unsigned y)).
    Proof.
      rewrite !signed_eq_swrap_unsigned; autorewrite with word_laws.
      cbv [wrap swrap]; generalize_unsigned_mod_range.
      replace (2 ^ width) with (2*2 ^ (width - 1)) by
        (rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; lia).
      set (M := 2 ^ (width - 1)) in*; clearbody M; clear dependent width.
      assert (0<2*M) by nia.
      f_equal.
      symmetry.
      rewrite <-(Z.add_mod_idemp_l _ M).
      symmetry.
      f_equal.
      f_equal.
      rewrite !Z.shiftl_mul_pow2 by mia.
      generalize (y mod (2 * M)); clear y; intro n.
      rewrite <-!Z.add_opp_r.
      rewrite !Z.add_mod_idemp_l.
      symmetry.
      rewrite <-(Z.mul_mod_idemp_l _ (2^n)).
      rewrite !Z.add_mod_idemp_l.
      rewrite !Z.mul_mod_idemp_l.
      f_equal.
      all:lia.
    Qed.

  End WithWord.
End word. Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.