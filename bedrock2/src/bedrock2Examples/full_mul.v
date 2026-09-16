(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics wsize.
Require Import bedrock2.ZnWords.
From Coq Require Import Lia ZArith.

Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Bitwidth coqutil.Word.Properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Return the high word of the integer multiplication a * b. *)
Definition br_full_mul :=
  func! (a, b) ~> (low, high) {
      n = $wsize >> $1;
      M = $1 << n - $1;
      ll = (a & M) * (b & M);
      lh = (a & M) * (b >> n);
      hl = (a >> n) * (b & M);
      hh = (a >> n) * (b >> n);
      second_halfword_w_oflow = (ll >> n) + (lh & M) + (hl & M);
      high = hh + (lh >> n) + (hl >> n) + (second_halfword_w_oflow >> n);
      low = (second_halfword_w_oflow << n) + (ll & M)
    }.

#[export] Instance spec_of_full_mul : spec_of "br_full_mul" :=
  fnspec! "br_full_mul" a b ~> low high,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          Zmod.unsigned low + 2^64 * (Zmod.unsigned high) =
            (Zmod.unsigned a) * (Zmod.unsigned b)
    }.

Local Lemma mask_is_mod :
  forall a : BasicC64Semantics.word,
    Zmod.unsigned
      (Zmod.and
         a
         (Zmod.sub (Zmod.slu (bits.of_Z _ 1) 32) (bits.of_Z _ 1))) =
      (Zmod.unsigned a) mod (2^32).
Proof.
  intros.
  rewrite <- Z.land_ones by lia.
  specialize
    (bits.unsigned_and
       a (Zmod.sub (Zmod.slu (bits.of_Z _ 1) 32) (bits.of_Z _ 1)) ).
  trivial.
Qed.

Local Lemma wrap_mul32_is_mul32 :
  forall a b,
    0 <= a < 2^32 ->
    0 <= b < 2^32 -> (a * b) mod 2 ^ 64 = (a * b).
Proof.
  intros.
  apply Zmod_small.
  nia.
Qed.

Local Lemma mul32_ub :
  forall a b : BasicC64Semantics.word,
    (Zmod.unsigned a) < 2^32 ->
    (Zmod.unsigned b) < 2^32 ->
    Zmod.unsigned (Zmod.mul a b) < 2^64 - 2^33 + 2.
Proof.
  intros.
  specialize (bits.unsigned_range a width_nonneg).
  specialize (bits.unsigned_range b width_nonneg).
  rewrite Zmod.unsigned_mul.
  rewrite wrap_mul32_is_mul32 by ZnWords.
  specialize (Zmult_le_compat_r (Zmod.unsigned a) (2^32 - 1) (Zmod.unsigned b)).
  specialize (Zmult_le_compat_l (Zmod.unsigned b) (2^32 - 1) (2^32 - 1)).
  ZnWords.
Qed.

Local Lemma mul_half_words :
  forall a b : BasicC64Semantics.word,
    Zmod.unsigned a < 2^32 ->
    Zmod.unsigned b < 2^32 ->
    Zmod.unsigned (Zmod.mul a b) = Zmod.unsigned a * Zmod.unsigned b.
Proof.
  intros.
  rewrite Zmod.unsigned_mul.
  rewrite wrap_mul32_is_mul32; ZnWords.
Qed.

Lemma full_mul_ok : program_logic_goal_for_function! br_full_mul.
Proof.
  repeat straightline.

  change n with (match bits.of_Z 64 32 return BasicC64Semantics.word with x => x end) in *.
  clear n.

  specialize (mask_is_mod a).
  specialize (mask_is_mod b).
  specialize (mask_is_mod ll).
  specialize (mask_is_mod lh).
  specialize (mask_is_mod hl).
  specialize (mul_half_words (Zmod.and a M) (Zmod.and b M)).
  specialize (mul_half_words (Zmod.and a M) (Zmod.sru b 32)).
  specialize (mul_half_words (Zmod.sru a 32) (Zmod.and b M)).
  specialize
    (mul_half_words (Zmod.sru a 32) (Zmod.sru b 32)).
  specialize
    (mul32_ub (Zmod.and a M) (Zmod.sru b 32)).
  specialize
    (mul32_ub (Zmod.sru a 32) (Zmod.and b M)).
  specialize
    (mul32_ub (Zmod.sru a 32) (Zmod.sru b 32)).
  Time ZnWords.
Qed.
