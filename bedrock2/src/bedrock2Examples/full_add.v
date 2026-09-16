Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition br_full_add :=
  func! (x, y, carry) ~> (sum, carry_out) {
      x = x + carry;
      carry_out = x < carry;
      sum = x + y;
      carry_out = carry_out + (sum < y)
    }.

From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Import coqutil.Word.Bitwidth.
Require Import bedrock2.ZnWords.

#[export] Instance spec_of_full_add : spec_of "br_full_add" :=
  fnspec! "br_full_add" x y carry ~> sum carry_out,
    { (* The required upper bound on `carry` isn't necessary for the
         current `br_full_add` to support the `ensures` clause, but
         it does formalize an expected condition that future
         implementations should be free to leverage. *)
      requires t m := Zmod.unsigned carry < 2;
      ensures T M :=
        M = m /\ T = t /\
          Zmod.unsigned sum + 2^64 * Zmod.unsigned carry_out =
            Zmod.unsigned x + Zmod.unsigned carry + Zmod.unsigned y
    }.

Require Import coqutil.Tactics.Tactics.

Lemma add_ltu_as_adder : forall a b : BasicC64Semantics.word,
    Zmod.unsigned a + Zmod.unsigned b =
      2^64 * (if Zmod.unsigned (Zmod.add a b) <? Zmod.unsigned b then 1 else 0) +
          Zmod.unsigned (Zmod.add a b).
Proof.
  intros.
  destr (Zmod.unsigned (Zmod.add a b) <? Zmod.unsigned b);
    ZnWords.
Qed.

Require Import ZArith.

Lemma full_add_ok : program_logic_goal_for_function! br_full_add.
Proof.
  repeat straightline. 
  
  rewrite add_ltu_as_adder.
  rewrite <- Z.add_assoc.
  rewrite add_ltu_as_adder.
  repeat
    (match goal with
     | X := _ |- _  => subst X end).
  destruct (Zmod.unsigned (Zmod.add x'0 carry) <? Zmod.unsigned carry);
    destruct (Zmod.unsigned (Zmod.add (Zmod.add x'0 carry) y) <? Zmod.unsigned y);
    ZnWords.
Qed.
