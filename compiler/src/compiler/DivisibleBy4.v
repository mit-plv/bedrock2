Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.Utility.
Require Import compiler.mod4_0.

Local Open Scope Z_scope.


Lemma divisibleBy4Signed{width}{BW: Bitwidth width}:
  forall (w: bits width),
    (Zmod.unsigned w) mod 4 = 0 ->
    (Zmod.signed w) mod 4 = 0.
Proof.
  intros.
  rewrite <- Zmod.smod_unsigned, word.smodulo_pow2.
  pose proof (bits.unsigned_range w width_nonneg).
  remember (Zmod.unsigned w) as x. clear Heqx.
  destruct width_cases as [E | E]; simpl in *; rewrite E;
    Z.div_mod_to_equations; blia.
Qed.

Definition divisibleBy4{width}(x: bits width): Prop := (Zmod.unsigned x) mod 4 = 0.

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
         | H: Zmod.unsigned _ mod 4 = 0 |- _ => unique pose proof (divisibleBy4Signed _ H)
         end;
  repeat match goal with
         | H: ?T |- _ => lazymatch T with
                         | Bitwidth _ => fail
                         | _ => clear H
                         end
         end;
  repeat match goal with
         | |- _ mod 4 = 0 -> _ => intro
         end;
  try apply mod4_0_opp;
  try apply divisibleBy4Signed;
  repeat (rewrite ?Zmod.unsigned_add, ?Zmod.signed_add,
                  ?Zmod.unsigned_sub, ?Zmod.signed_sub,
                  ?Zmod.unsigned_mul, ?Zmod.signed_mul,
                  ?bits.unsigned_of_Z, ?Zmod.signed_of_Z, ?word.smodulo_pow2).

Ltac solve_divisibleBy4 := divisibleBy4_pre; solve_mod4_0.

(* tests from FlatToRiscv *)
Goal forall {width}{BW: Bitwidth width} (pc: bits width) (l n m: Z),
    divisibleBy4 pc -> False.
  intros.
  assert (divisibleBy4 (Zmod.add pc (bits.of_Z width (l * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4 (Zmod.add pc 4)) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (Zmod.add
               (Zmod.add (Zmod.add pc 4)
                         (Zmod.mul 4 (bits.of_Z width l)))
               (bits.of_Z width (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (Zmod.add
               (Zmod.add pc
                         (Zmod.mul 4 (bits.of_Z width l)))
               (bits.of_Z width (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (Zmod.add
               (Zmod.add pc
                         (Zmod.mul 4
                                   (bits.of_Z width l)))
               (bits.of_Z width 4))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (Zmod.add
               (Zmod.add
                  (Zmod.add
                     (Zmod.add pc
                               (Zmod.mul 4
                                         (bits.of_Z width l)))
                     (bits.of_Z width 4))
                  (Zmod.mul 4 (bits.of_Z width n)))
               (bits.of_Z width
                  (- m * 4)))) as A by solve_divisibleBy4. clear A.
Abort.


Section Modu.
  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).

  Definition divisibleBy4'(x: word): Prop := Zmod.umod x 4 = (bits.of_Z width 0).

  Lemma four_fits: 4 < 2 ^ width.
  Proof.
    destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Ltac div4_sidecondition :=
    pose proof four_fits;
    rewrite ?bits.unsigned_of_Z; rewrite ?Z.mod_small;
    blia.

  Lemma divisibleBy4_alt(x: word): divisibleBy4 x -> divisibleBy4' x.
  Proof.
    intro H. unfold divisibleBy4, divisibleBy4' in *.
    apply Zmod.unsigned_inj.
    rewrite Zmod.unsigned_umod by div4_sidecondition.
    replace (Zmod.unsigned (bits.of_Z width 4)) with 4 by div4_sidecondition.
    rewrite H.
    div4_sidecondition.
  Qed.

End Modu.

Ltac simpl_modu4_0 :=
  simpl;
  match goal with
  | |- context [Zmod.eqb ?a ?b] =>
    rewrite (proj2 (Zmod.eqb_eq a b)) by (apply divisibleBy4_alt; solve_divisibleBy4)
  end;
  simpl.
