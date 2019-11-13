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

Lemma sumbool_rect_bool_weq n x y :
  sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
Admitted.

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
  Hypothesis (HinstrMemBound: instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  (** * Register file mapping *)

  Context {Registers: map.map Register word}.
  Definition regs_related (krf: kword 5 -> kword width)
             (rrf: Registers): Prop :=
    forall z, 0 < z < 32 -> map.get rrf z = Some (krf (ZToWord _ z)).
End DecExecOk.
