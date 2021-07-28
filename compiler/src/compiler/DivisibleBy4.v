Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.Utility.
Require Import compiler.mod4_0.

Local Open Scope Z_scope.


Lemma divisibleBy4Signed{width}{BW: Bitwidth width}{word: word.word width}{ok: word.ok word}:
  forall (w: word),
    (word.unsigned w) mod 4 = 0 ->
    (word.signed w) mod 4 = 0.
Proof.
  intros.
  rewrite word.signed_eq_swrap_unsigned.
  unfold word.swrap.
  pose proof (word.unsigned_range w).
  remember (word.unsigned w) as x. clear Heqx.
  destruct width_cases as [E | E]; simpl in *; rewrite E;
    Z.div_mod_to_equations; blia.
Qed.

Definition divisibleBy4{width}{word: word.word width}(x: word): Prop := (word.unsigned x) mod 4 = 0.

Ltac divisibleBy4_pre :=
  lazymatch goal with
  | |- ?G => assert_fails (has_evar G)
  end;
  unfold divisibleBy4 in *;
  lazymatch goal with
  | |- _ mod 4 = 0 => idtac
  | |- _ => fail "not a divisibleBy4 goal"
  end;
  repeat match goal with
         | H: _ mod 4 = 0 |- _ => revert H
         end;
  repeat match goal with
         (* TODO might fail to find Words instance *)
         | H: word.unsigned _ mod 4 = 0 |- _ => unique pose proof (divisibleBy4Signed _ H)
         end;
  repeat match goal with
         | H: ?T |- _ => lazymatch T with
                         | word.ok _ => fail
                         | Bitwidth _ => fail
                         | _ => clear H
                         end
         end;
  repeat match goal with
         | |- _ mod 4 = 0 -> _ => intro
         end;
  try apply mod4_0_opp;
  try apply divisibleBy4Signed;
  repeat (rewrite ?word.unsigned_add, ?word.signed_add,
                  ?word.unsigned_sub, ?word.signed_sub,
                  ?word.unsigned_mul, ?word.signed_mul,
                  ?word.unsigned_of_Z, ?word.signed_of_Z
          || unfold word.wrap, word.swrap).

Ltac solve_divisibleBy4 := divisibleBy4_pre; solve_mod4_0.

(* tests from FlatToRiscv *)
Goal forall {width}{BW: Bitwidth width}{word: word.word width}{ok: word.ok word} (pc: word) (l n m: Z),
    divisibleBy4 pc -> False.
  intros.
  assert (divisibleBy4 (word.add pc (word.of_Z (l * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4 (word.add pc (word.of_Z 4))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add (word.add pc (word.of_Z 4))
                         (word.mul (word.of_Z 4) (word.of_Z l)))
               (word.of_Z (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add pc
                         (word.mul (word.of_Z 4) (word.of_Z l)))
               (word.of_Z (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add pc
                         (word.mul (word.of_Z 4)
                                   (word.of_Z l)))
               (word.of_Z 4))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add
                  (word.add
                     (word.add pc
                               (word.mul (word.of_Z 4)
                                         (word.of_Z l)))
                     (word.of_Z 4))
                  (word.mul (word.of_Z 4) (word.of_Z n)))
               (word.of_Z
                  (- m * 4)))) as A by solve_divisibleBy4. clear A.
Abort.


Section Modu.
  Context {width} {BW: Bitwidth width} {word: word.word width} {ok: word.ok word}.

  Definition divisibleBy4'(x: word): Prop := word.modu x (word.of_Z 4) = word.of_Z 0.

  Lemma four_fits: 4 < 2 ^ width.
  Proof.
    destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Ltac div4_sidecondition :=
    pose proof four_fits;
    rewrite ?word.unsigned_of_Z; unfold word.wrap; rewrite ?Z.mod_small;
    blia.

  Lemma divisibleBy4_alt(x: word): divisibleBy4 x -> divisibleBy4' x.
  Proof.
    intro H. unfold divisibleBy4, divisibleBy4' in *.
    apply word.unsigned_inj.
    rewrite word.unsigned_modu_nowrap by div4_sidecondition.
    replace (word.unsigned (word.of_Z 4)) with 4 by div4_sidecondition.
    rewrite H.
    div4_sidecondition.
  Qed.

End Modu.

Ltac simpl_modu4_0 :=
  simpl;
  match goal with
  | |- context [word.eqb ?a ?b] =>
    rewrite (word.eqb_eq a b) by (apply divisibleBy4_alt; solve_divisibleBy4)
  end;
  simpl.
