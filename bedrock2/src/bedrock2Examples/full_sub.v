Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Require Import bedrock2.ZnWords.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import coqutil.Macros.ident_to_string.
Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Lia ZArith.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation "x += e" :=
  (cmd.set
     (ident_to_string! x)
     (expr.op bopname.add (ident_to_string! x) e))
    (in custom bedrock_cmd at
          level 0, x ident, e custom bedrock_expr, only parsing).

Local Notation "x -= e" :=
  (cmd.set
     (ident_to_string! x)
     (expr.op bopname.sub (ident_to_string! x) e))
    (in custom bedrock_cmd at
          level 0, x ident, e custom bedrock_expr, only parsing).

(* This definition is inspired by `bn_sub_with_borrow` in BoringSSL,
 * but has been rewritten in order to simplify its verification.  *)
Definition br_full_sub :=
  func! (x, y, borrow) ~> (diff, out_borrow) {
      out_borrow = x < y;
      diff = x - y;
      out_borrow += diff < borrow;
      diff -= borrow
    }.

Local Instance spec_of_full_sub : spec_of "br_full_sub" :=
  fnspec! "br_full_sub" x y borrow ~> diff out_borrow,
    { requires t m :=
        (* This pre-condition is not required in order to ensure the
         * post-condition, but formalizes on a condition on the
         * operation's expected usage. *)
        word.unsigned borrow < 2;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned diff - 2^64 * word.unsigned out_borrow =
            word.unsigned x - word.unsigned y - word.unsigned borrow
    }.

Lemma ltu_as_borrow :
  forall a b : BasicC64Semantics.word,
    word.unsigned a - word.unsigned b =
      word.unsigned (word.sub a b) - 2^64 * (if word.ltu a b then 1 else 0).
Proof.
  intros.
  rewrite word.unsigned_ltu.
  destr (word.unsigned a <? word.unsigned b);
    ZnWords.
Qed.

Lemma full_sub_ok : program_logic_goal_for_function! br_full_sub.
Proof.
  repeat straightline.
  rewrite ltu_as_borrow.
  assert (subtrahends_comm: forall m n o, m - n - o = m - o - n) by lia.
  rewrite subtrahends_comm. clear subtrahends_comm.
  rewrite ltu_as_borrow.
  repeat
    (match goal with
     | X := _ |- _  => subst X end).
  destruct (word.ltu x y);
    destruct (word.ltu (word.sub x y) borrow);
    ZnWords.
Qed.
