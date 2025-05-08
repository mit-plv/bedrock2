(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import bedrock2.ZnWords.
Require Import Lia ZArith.

Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Interface coqutil.Word.Properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Definition wmask : expr.expr := bedrock_expr:((-$1>>$27)&$63).
Local Definition wsize : expr.expr := bedrock_expr:($wmask+$1).

(* Return the high word of the integer multiplication a * b. *)
Definition full_mul :=
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

Local Instance spec_of_full_mul : spec_of "full_mul" :=
  fnspec! "full_mul" a b ~> low high,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned low + 2^64 * (word.unsigned high) =
            (word.unsigned a) * (word.unsigned b)
    }.

Local Lemma mask_is_mod :
  forall a : BasicC64Semantics.word,
    word.unsigned
      (word.and
         a
         (word.sub (word.slu (word.of_Z 1) (word.of_Z 32)) (word.of_Z 1))) =
      (word.unsigned a) mod (2^32).
Proof.
  intros.
  rewrite <- Z.land_ones by lia.
  specialize
    (word.unsigned_and_nowrap
       a (word.sub (word.slu (word.of_Z 1) (word.of_Z 32)) (word.of_Z 1)) ).
  trivial.
Qed.

Local Lemma wrap_mul32_is_mul32 :
  forall a b,
    0 <= a < 2^32 ->
    0 <= b < 2^32 -> word.wrap (a * b) = (a * b).
Proof.
  intros.
  apply Zmod_small.
  nia.
Qed.

Local Lemma mul32_ub :
  forall a b : BasicC64Semantics.word,
    (word.unsigned a) < 2^32 ->
    (word.unsigned b) < 2^32 ->
    word.unsigned (word.mul a b) < 2^64 - 2^33 + 2.
Proof.
  intros.
  specialize (word.unsigned_range a).
  specialize (word.unsigned_range b).
  rewrite word.unsigned_mul.
  rewrite wrap_mul32_is_mul32 by ZnWords.
  specialize (Zmult_le_compat_r (word.unsigned a) (2^32 - 1) (word.unsigned b)).
  specialize (Zmult_le_compat_l (word.unsigned b) (2^32 - 1) (2^32 - 1)).
  ZnWords.
Qed.

Local Lemma mul_half_words :
  forall a b : BasicC64Semantics.word,
    word.unsigned a < 2^32 ->
    word.unsigned b < 2^32 ->
    word.unsigned (word.mul a b) = word.unsigned a * word.unsigned b.
Proof.
  intros.
  rewrite word.unsigned_mul.
  rewrite wrap_mul32_is_mul32; ZnWords.
Qed.

Lemma full_mul_ok : program_logic_goal_for_function! full_mul.
Proof.
  repeat straightline.

  change n with (match word.of_Z 32 return BasicC64Semantics.word with x => x end) in *.
  clear n.

  specialize (mask_is_mod a).
  specialize (mask_is_mod b).
  specialize (mask_is_mod ll).
  specialize (mask_is_mod lh).
  specialize (mask_is_mod hl).
  specialize (mul_half_words (word.and a M) (word.and b M)).
  specialize (mul_half_words (word.and a M) (word.sru b (word.of_Z 32))).
  specialize (mul_half_words (word.sru a (word.of_Z 32)) (word.and b M)).
  specialize
    (mul_half_words (word.sru a (word.of_Z 32)) (word.sru b (word.of_Z 32))).
  specialize
    (mul32_ub (word.and a M) (word.sru b (word.of_Z 32))).
  specialize
    (mul32_ub (word.sru a (word.of_Z 32)) (word.and b M)).
  specialize
    (mul32_ub (word.sru a (word.of_Z 32)) (word.sru b (word.of_Z 32))).
  Time ZnWords.
Qed.
