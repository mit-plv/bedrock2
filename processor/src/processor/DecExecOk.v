Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Spec.Decode.
Require Import coqutil.Map.Interface.

Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes.
Require Import Kami.Ex.IsaRv32.

Require Import processor.KamiProc.

Set Implicit Arguments.

Local Open Scope Z_scope.

Axiom TODO_joonwon: False.

Lemma unsigned_wordToZ n z : Z.of_N (wordToN (ZToWord n z)) = z mod 2^(Z.of_nat n).
Admitted.

Lemma unsigned_inj n x y : Z.of_N (@wordToN n x) = Z.of_N (@wordToN n y) -> x = y.
Admitted.

Lemma sumbool_rect_weq {T} a b n x y :
  sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
Proof.
  cbv [sumbool_rect].
  destruct (weq _ _), (weqb _ _) eqn:?;
  try match goal with H : _ |- _ => eapply weqb_true_iff in H end;
  trivial; congruence.
Qed.

Lemma sumbool_rect_bool_weq n x y :
  sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
Proof. rewrite sumbool_rect_weq; destruct (weqb x y); trivial. Qed.

Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
Admitted.

Lemma unsigned_split1_as_bitSlice a b x :
  Z.of_N (wordToN (split1 a b x)) = bitSlice (Z.of_N (wordToN x)) 0 (Z.of_nat a).
Admitted.

Lemma unsigned_split2_as_bitSlice a b x :
  Z.of_N (wordToN (split2 a b x)) = bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

Lemma unsigned_split2_split1_as_bitSlice a b c x :
  Z.of_N (wordToN (split2 a b (split1 (a+b) c x))) = bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

Section DecExecOk.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  Variables (instrMemSizeLg: Z).
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  (** * Register file mapping *)

  Context {Registers: map.map Register word}
          (Registers_ok : map.ok Registers).

  Definition regs_related (krf: kword 5 -> kword width)
             (rrf: Registers): Prop :=
    forall w, w <> $0 -> map.get rrf (Z.of_N (wordToN w)) = Some (krf w).

  Lemma regs_related_get:
    forall krf (Hkrf0: krf $0 = $0) rrf,
      regs_related krf rrf ->
      forall w z,
        Z.of_N (wordToN w) = z ->
        krf w =
        (if Z.eq_dec z 0 then word.of_Z 0
         else
           match map.get rrf z with
           | Some x => x
           | None => word.of_Z 0
           end).
  Proof.
    intros.
    destruct (Z.eq_dec _ _).
    - subst; destruct (weq w $0); subst; [assumption|].
      exfalso.
      rewrite <-N2Z.inj_0 in e.
      apply N2Z.inj in e.
      rewrite <-wordToN_wzero with (sz:= 5%nat) in e.
      apply wordToN_inj in e; auto.
    - subst; rewrite H; [reflexivity|].
      intro; subst; auto.
  Qed.

  Lemma regs_related_put krf rrf kv rv kk rk
        (Hrf: regs_related krf rrf)
        (Hk: Z.of_N (wordToN kk) = rk)
        (Hv: kv = rv):
    regs_related
      (fun w : Word.word rv32RfIdx => if weq w kk then kv else krf w)
      (map.put rrf rk rv).
  Proof.
    rewrite <-Hv.
    cbv [regs_related].
    intros i Hi.
    destruct (weq (sz:= rv32RfIdx) i kk).
    - subst; apply map.get_put_same.
    - rewrite map.get_put_diff.
      + apply Hrf; auto.
      + subst; intro.
        apply N2Z.inj, wordToN_inj in H; auto.
  Qed.

End DecExecOk.
