Local Set Universe Polymorphism.
Local Set Primitive Projections.
  
Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import bedrock2.Word. Import word.
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


(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section WithWidth.
  Context {width : Z}.
  Let wrap_value z := z mod (2^width).
  Record rep := mk { unsigned : Z ; _ : wrap_value unsigned = unsigned }.

  Context {width_nonneg : Z.lt 0 width}.

  Lemma wrap_value_wrap_value z : wrap_value (wrap_value z) = wrap_value z.
    cbv [wrap_value]. rewrite Z.mod_mod. reflexivity.
    eapply Z.pow_nonzero; [congruence | lia ].
  Qed.

  Definition wrap (z:Z) : rep :=
    mk (wrap_value z) (minimize_eq_proof Z.eq_dec (wrap_value_wrap_value z)).
  Definition signed w :=
    unsigned w mod 2^(width-1) - 2^(width-1) * (unsigned w / 2^(width-1)).

  Definition word : word.word width := {|
    word.rep := rep;
    word.unsigned := unsigned;
    word.signed := signed;
    of_Z := wrap;

    add x y := wrap (Z.add (unsigned x) (unsigned y));
    sub x y := wrap (Z.sub (unsigned x) (unsigned y));

    or x y := wrap (Z.lor (unsigned x) (unsigned y));

    and x y := wrap (Z.land (unsigned x) (unsigned y));
    xor x y := wrap (Z.lxor (unsigned x) (unsigned y));

    mul x y := wrap (Z.mul (unsigned x) (unsigned y));
    mulhss x y := wrap (Z.mul (signed x) (signed y) / 2^width);
    mulhsu x y := wrap (Z.mul (signed x) (unsigned y) / 2^width);
    mulhuu x y := wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    divu x y := wrap (Z.div (unsigned x) (unsigned y));
    divs x y := wrap (Z.div (signed x) (signed y));

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
    cbv [unsigned signed wrap wrap_value].
    set (M := 2 ^ (width - 1)).
    assert (0 < M) by (change 0 with (2^(-1)); eapply Z.pow_lt_mono_r; lia).
    assert (0 < 2*M) by lia.
    replace (2^width) with (2*M) in * by
        (subst M; rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; nia).
    clearbody M.
    rewrite (Z.add_mod z M (2*M)) by lia.
    assert (M/(2 * M)=0) as H2M by mia;
      replace (M mod (2 * M)) with M by mia; clear H2M.
    set (X := z mod (2*M));
      destruct (ltac:(subst X; mia):(0 <= X < M \/ M <= X < 2*M)); clearbody X.
    { assert (X/M = 0) by mia; assert ((X + M) / (2 * M) = 0); mia. }
    { assert (X/M = 1) by mia; assert ((X + M) / (2 * M) = 1); mia. }
  Qed.

  Check fun (x y : word) => signed_of_Z (Z.shiftr (word.signed x) (word.unsigned y)).

  Lemma ok : word.ok word.
  Proof. split; eauto using of_Z_unsigned, signed_of_Z. Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.

Local Instance word8 : word.word 8 := word 8 ltac:(firstorder).