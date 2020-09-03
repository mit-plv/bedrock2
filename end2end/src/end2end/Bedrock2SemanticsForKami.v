Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require Import coqutil.Z.HexNotation.
Require Import processor.KamiWord.
Require Import compiler.RiscvWordProperties.
Require Import end2end.KamiRiscvWordProperties.
Require Import compilerExamples.MMIO.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

Instance word: word.word 32 := KamiWord.word 32.
Instance word_ok: word.ok word := KamiWord.ok 32 eq_refl.

Local Existing Instance SortedListString.ok.

Instance word_riscv_ok: word.riscv_ok word.
refine (@kami_word_riscv_ok 5 _ _).
all: cbv; congruence.
Qed.

Instance FE310CSemanticsParameters : FE310CSemantics.parameters.parameters := {|
  FE310CSemantics.parameters.word := word;
  FE310CSemantics.parameters.mem := SortedListWord.map _ _;
  (* FIXME: we shouldn't need the next line *)
  FE310CSemantics.parameters.mem_ok := SortedListWord.ok _ _;
|}.

Goal True.
  pose (_: Semantics.parameters).
Abort.

Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.word)),
       constants [Properties.word_cst]).
