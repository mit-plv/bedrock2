Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Interface.

Section ZnWordTests.
  Context {word: word.word 32} {word_ok: word.ok word}.

  Goal forall (a a' SZ: word) (T: Type) (f: T -> nat) (vs1: T),
      word.unsigned (word.sub a' a) mod word.unsigned SZ = 0 ->
      f vs1 = Z.to_nat (word.unsigned (word.sub a' a) / word.unsigned SZ) ->
      word.add a (word.of_Z (word.unsigned (word.of_Z (word := word) (word.unsigned SZ))
                             * Z.of_nat (f vs1))) = a'.
  Proof.
    intros.
    Fail ZnWords.
    (* This rewrite should not be needed, but it seems to be a limitation of lia:
       https://github.com/coq/coq/issues/15583
       TODO remove the rewrite if lia is fixed. *)
    rewrite H0.
    ZnWords.
    all: fail "remaining subgoals".
  Abort.

End ZnWordTests.
